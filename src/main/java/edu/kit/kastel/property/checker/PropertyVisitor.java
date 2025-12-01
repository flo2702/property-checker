/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.kastel.property.checker;

import com.sun.source.tree.*;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.packing.PackingVisitor;
import edu.kit.kastel.property.printer.JavaJMLPrinter;
import edu.kit.kastel.property.printer.JavaVerifastPrinter;
import edu.kit.kastel.property.printer.PrettyPrinter;
import edu.kit.kastel.property.smt.SmtCompiler;
import edu.kit.kastel.property.smt.SmtExpression;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.FileUtils;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.javacutil.TreeUtils;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.*;

public final class PropertyVisitor extends PackingVisitor {

    private TreePath path;

    Map<MethodTree, AnnotationMirror[]> inputPackingTypes = new HashMap<>();
    Map<MethodTree, AnnotationMirror[]> outputPackingTypes = new HashMap<>();

    Map<Tree, TypeMirror> inferredUnpackStatements = new HashMap<>();
    Map<Tree, TypeMirror> inferredPackStatements = new HashMap<>();

    protected PropertyVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    @Override
    public void visit(TreePath path) {
        super.visit(path);
        this.path = path;

        PropertyChecker checker = (PropertyChecker) this.checker;
        String outputLangOption = checker.getOption(Config.OUTPUT_LANG_OPTION, Config.OUTPUT_LANG_JML);

        File file = Paths.get(checker.getOutputDir(), checker.getRelativeSourceFileName()).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);

        try (BufferedWriter out = new BufferedWriter(new FileWriter(file))) {
            List<LatticeVisitor.Result> results = checker.getResults(checker.getAbsoluteSourceFileName());
            mendTypeErrors(results);

            // TODO: fix reporting here (results is never empty, even if there are no proof obligations left)
            if (results.isEmpty()) {
                PrettyPrinter printer = new PrettyPrinter(out, true);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with no remaining proof obligations",
                        checker.getRelativeSourceFileName()));
            } else if (outputLangOption.equals(Config.OUTPUT_LANG_JML)) {
                JavaJMLPrinter printer = new JavaJMLPrinter(results, checker, out);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)\n\t%d non-free method postconditions (to be proven in JML)\n\t%d free method postconditions (proven by checker)",
                        checker.getRelativeSourceFileName(),
                        printer.getAssertions(), printer.getAssumptions(),
                        printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions(),
                        printer.getMethodCallPostconditions(), printer.getFreeMethodCallPostconditions()));
                // LatticeVisitors are reused, but result contents are compilation-unit-specific, so we reset them
                results.forEach(LatticeVisitor.Result::clear);
            } else if (outputLangOption.equals(Config.OUTPUT_LANG_VERIFAST)) {
                JavaVerifastPrinter printer = new JavaVerifastPrinter(results, checker, out);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)\n\t%d non-free method postconditions (to be proven in JML)\n\t%d free method postconditions (proven by checker)",
                        checker.getRelativeSourceFileName(),
                        printer.getAssertions(), printer.getAssumptions(),
                        printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions(),
                        printer.getMethodCallPostconditions(), printer.getFreeMethodCallPostconditions()));
                // LatticeVisitors are reused, but result contents are compilation-unit-specific, so we reset them
                results.forEach(LatticeVisitor.Result::clear);
            } else {
                throw new IOException("unknown output language: " + outputLangOption);
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private void mendTypeErrors(List<LatticeVisitor.Result> results) {
        System.out.println("\nFile: \033[4m" + root.getSourceFile().getName() + "\033[0m");
        // merge contexts from all lattices
        Map<Tree, Set<SmtExpression>> contexts = new HashMap<>();
        for (LatticeVisitor.Result result : results) {
            result.getContexts()
                    .forEach((tree, context) -> contexts.computeIfAbsent(tree, v -> new HashSet<>()).addAll(context));
        }

        // go through all expression trees that caused type errors
        results.stream()
                .map(LatticeVisitor.Result::getMendingConditions)
                .map(Map::keySet)
                .flatMap(Set::stream)
                .distinct()
                .forEach(tree -> processMendableExpression(results, contexts.getOrDefault(tree, Set.of()), tree));
        // go through all packing calls with uninitialized fields left
        results.stream()
                .map(LatticeVisitor.Result::getUninitializedFields)
                .map(Map::keySet)
                .flatMap(Set::stream)
                .distinct()
                .forEach(tree -> processMendablePackingCall(results, contexts.getOrDefault(tree, Set.of()), tree));

    }

    private void processMendableExpression(
            List<LatticeVisitor.Result> results,
            Set<SmtExpression> context,
            Tree expression
    ) {
        try (var solverContext = createSolverContext()) {
            SmtCompiler compiler = new SmtCompiler(solverContext);
            var conjunction = contextConjunction(compiler, expression, context);
            for (LatticeVisitor.Result result : results) {
                var condition = result.getMendingConditions().get(expression);
                if (condition == null) {
                    continue;
                }
                if (universallyValid(solverContext, compiler, conjunction, condition)) {
                    result.removeTypeError(TreePath.getPath(checker.getPathToCompilationUnit(), expression));
                }
            }
        }
    }

    private void processMendablePackingCall(
            List<LatticeVisitor.Result> results,
            Set<SmtExpression> context,
            Tree packingCall
    ) {
        try (var solverContext = createSolverContext()) {
            SmtCompiler compiler = new SmtCompiler(solverContext);
            var conjunction = contextConjunction(compiler, packingCall, context);
            for (LatticeVisitor.Result result : results) {
                var fields = result.getUninitializedFields().getOrDefault(packingCall, Collections.emptyList()).iterator();
                while (fields.hasNext()) {
                    var condition = result.getFieldRefinement(fields.next());
                    if (condition != null && universallyValid(solverContext, compiler, conjunction, condition)) {
                        fields.remove();
                    }
                }
            }
        }
    }

    private SolverContext createSolverContext() {
        try {
            return SolverContextFactory.createSolverContext(SolverContextFactory.Solvers.SMTINTERPOL);
        } catch (InvalidConfigurationException e) {
            throw new RuntimeException(e);
        }
    }

    private Deque<BooleanFormula> contextConjunction(SmtCompiler compiler, Tree tree, Set<SmtExpression> context) {
        var lineMap = root.getLineMap();
        var pos = trees.getSourcePositions().getStartPosition(root, tree);
        System.out.printf("=== Mending type errors for \033[1;33m%s (%d:%d)\033[0m using combined context:%n",
                describeTree(tree), lineMap.getLineNumber(pos), lineMap.getColumnNumber(pos));
        Deque<BooleanFormula> conjunction = new ArrayDeque<>();

        // add context formulae
        for (SmtExpression expr : context) {
            try {
                conjunction.push((BooleanFormula) compiler.compile(expr));
                System.out.println(expr);
            } catch (UnsupportedOperationException e) {
                // drop context constraints that aren't representable
                System.out.printf("(Ignoring context formula %s due to use of unsupported feature: %s%n)",
                        expr, e.getMessage());
            }
        }
        System.out.println("== Proof attempts");
        return conjunction;
    }

    private String describeTree(Tree tree) {
        var path = atypeFactory.getPath(tree);
        final Tree parent = path.getParentPath().getLeaf();
        return switch (tree) {
            case MethodTree m -> "postconditions on `this` (%s(...))".formatted(m.getName());
            case VariableTree v ->
                    "postconditions on `%s` (%s(...))".formatted(v.getName(), ((MethodTree) parent).getName());
            case ExpressionTree e -> switch (parent) {
                case MethodInvocationTree m -> "%s in method call `%s`".formatted(TypeUtils.getArgumentIndex(m, e) == 0
                        ? "receiver"
                        : "argument `%s`".formatted(e), m);
                case NewClassTree n -> "argument `%s` in constructor call `%s`".formatted(e, n);
                case VariableTree a -> "assignment `%s = %s` ".formatted(a.getName(), e);
                case AssignmentTree a -> "assignment `%s` ".formatted(a);
                default -> "`%s`".formatted(e);
            };
            default -> "???";
        };
    }

    private boolean universallyValid(SolverContext solverContext, SmtCompiler compiler, Deque<BooleanFormula> contextConjunction, SmtExpression condition) {
        BooleanFormulaManager bmgr = solverContext.getFormulaManager().getBooleanFormulaManager();

        // add proof goal to conjunction
        try {
            contextConjunction.push(bmgr.not((BooleanFormula) compiler.compile(condition)));
        } catch (UnsupportedOperationException e) {
            System.out.printf("(Skipping proof goal %s due to use of unsupported feature: %s%n)",
                    condition, e.getMessage());
            return false;
        }

        System.out.printf("\033[1mProof goal:\033[0m %s", condition);
        try (var proverEnv = solverContext.newProverEnvironment()) {
            proverEnv.addConstraint(bmgr.and(contextConjunction));
            var assignmentValid = proverEnv.isUnsat();
            System.out.println((assignmentValid ? " \033[32m(success)" : " \033[31m(failed)") + "\033[0m");
            return assignmentValid;
        } catch (InterruptedException | SolverException e) {
            System.out.println("Encountered exception while trying to prove goal " + condition);
            e.printStackTrace();
        } finally {
            // context formulae stay in the conjunction, we only remove the proof goal (which was added last)
            contextConjunction.pop();
        }
        return false;
    }

    TreePath getPath() {
        return path;
    }

    CompilationUnitTree getRoot() {
        return root;
    }

    @Override
    public Void visitMethod(MethodTree tree, Void p) {
        inputPackingTypes.put(tree, new AnnotationMirror[tree.getParameters().size() + 1]);
        outputPackingTypes.put(tree, new AnnotationMirror[tree.getParameters().size() + 1]);

        for (int i = 0; i < tree.getParameters().size(); ++i) {
            VariableTree param = tree.getParameters().get(i);
            AnnotationMirror anno = atypeFactory.getAnnotatedType(param).getEffectiveAnnotationInHierarchy(atypeFactory.getInitialized());
            if (anno == null) {
                anno = atypeFactory.getInitialized();
            }

            inputPackingTypes.get(tree)[i + 1] = anno;
        }

        if (TreeUtils.isConstructor(tree)) {
            inputPackingTypes.get(tree)[0] = getDeclaredConstructorResult(tree);
        } else if (tree.getReceiverParameter() != null) {
            AnnotationMirror anno = atypeFactory.getAnnotatedType(tree.getReceiverParameter()).getEffectiveAnnotationInHierarchy(atypeFactory.getInitialized());
            if (anno == null) {
                anno = atypeFactory.getInitialized();
            }

            inputPackingTypes.get(tree)[0] = anno;
        }
        return super.visitMethod(tree, p);
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        int paramIdx = TypeUtils.getParameterIndex(methodTree, expression);
        outputPackingTypes.get(methodTree)[paramIdx] = annotation;
        super.checkPostcondition(methodTree, annotation, expression);
    }

    @Override
    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingStore exitStore) {
        int paramIdx = TypeUtils.getParameterIndex(methodTree, param);
        AnnotationMirror anno = atypeFactory.getAnnotatedTypeLhs(param).getAnnotationInHierarchy(atypeFactory.getInitialized());
        if (anno == null) {
            anno = atypeFactory.getInitialized();
        }

        outputPackingTypes.get(methodTree)[paramIdx] = anno;
        super.checkDefaultContract(param, methodTree, exitStore);
    }

    @Override
    protected void reportUninitializedFieldsError(Tree tree, BaseTypeChecker targetChecker, List<VariableElement> uninitializedFields) {
        super.reportUninitializedFieldsError(tree, targetChecker, uninitializedFields);

        // Add uninitialized fields to LatticeVisitor for JML printer to use
        if (targetChecker instanceof LatticeSubchecker) {
            LatticeVisitor latticeVisitor = (LatticeVisitor) targetChecker.getVisitor();
            latticeVisitor.addUninitializedFields(tree, uninitializedFields);
        }
    }

    @Override
    protected void inferPackStatement(Tree tree, TypeMirror frame) {
        this.inferredPackStatements.put(tree, frame);
    }

    @Override
    protected void inferUnpackStatement(Tree tree, TypeMirror frame) {
        this.inferredUnpackStatements.put(tree, frame);
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        return new PropertyAnnotatedTypeFactory(checker);
    }

    public PropertyChecker getPropertyChecker() {
        return (PropertyChecker) checker;
    }
}
