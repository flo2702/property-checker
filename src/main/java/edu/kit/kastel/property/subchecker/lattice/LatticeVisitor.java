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
package edu.kit.kastel.property.subchecker.lattice;

import com.sun.source.tree.*;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.SourcePositions;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingClientVisitor;
import edu.kit.kastel.property.smt.JavaToSmtExpression;
import edu.kit.kastel.property.smt.SmtExpression;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.*;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.Resolver;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeVisitor extends PackingClientVisitor<LatticeAnnotatedTypeFactory> implements CooperativeVisitor {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;
    private final Resolver resolver;
    private final TypeMirror bool;

    private CooperativeVisitor.Result result;

    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;

    protected LatticeVisitor(BaseTypeChecker checker, LatticeAnnotatedTypeFactory typeFactory) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
        resolver = new Resolver(checker.getProcessingEnvironment());
        bool = types.getPrimitiveType(TypeKind.BOOLEAN);

        result = new CooperativeVisitor.Result(getLatticeSubchecker());
    }

    public LatticeVisitor(BaseTypeChecker checker) {
        this(checker, null);
    }

    @Override
    public void visit(TreePath path) {
        super.visit(path);

        ((PropertyChecker) checker.getParentChecker()).addResult(getAbsoluteSourceFileName(), result);
    }

    @Override
    public Void visitAnnotation(AnnotationTree tree, Void p) {
        // do nothing
        return p;
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        call(() -> super.visitReturn(node, p), () -> result.illTypedMethodResults.add(enclMethod));
        return null;
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        final int paramIdx = TypeUtils.getParameterIndex(methodTree, expression);
        result.methodOutputTypes.get(methodTree)[paramIdx] = annotation;
        var treeKey = postconditionKey(methodTree, paramIdx);
        var goal = computePostconditionSmt(treeKey, annotation, expression, atypeFactory.getRegularExitStore(methodTree));

        call(
                () -> super.checkPostcondition(methodTree, annotation, expression),
                () -> {
                    if (goal != null) {
                        result.addMendingCondition(treeKey, goal);
                    }
                    result.addIllTypedMethodOutputParam(methodTree, paramIdx);
                });
    }

    @Override
    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingClientStore<?, ?> exitStore) {
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(TreeUtils.typeOf(param));
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }
        final int paramIdx = TypeUtils.getParameterIndex(methodTree, param);
        var treeKey = postconditionKey(methodTree, paramIdx);
        var annotation = atypeFactory.getAnnotatedTypeLhs(param).getEffectiveAnnotationInHierarchy(atypeFactory.getTop());
        var goal = computePostconditionSmt(treeKey, annotation, paramExpr, (LatticeStore) exitStore);
        if (!paramsInContract.contains(paramExpr)) {
            result.methodOutputTypes.get(methodTree)[paramIdx] = annotation;
        }
        call(
                () -> super.checkDefaultContract(param, methodTree, exitStore),
                () -> {
                    if (goal != null) {
                        result.addMendingCondition(treeKey, goal);
                    }
                    result.addIllTypedMethodOutputParam(methodTree, paramIdx);
                });
    }

    private Tree postconditionKey(MethodTree tree, int paramIndex) {
        // postcondition for the receiver: use the method tree as the key (there is no tree for implicit receivers)
        // parameter postcondition: use the variable tree of the parameter
        return paramIndex == 0 ? tree : tree.getParameters().get(paramIndex - 1);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
        if (enclMethod == null) {
            // Don't check implicit constructors
            return null;
        }

        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();
        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            // compute smt context for packing calls and put it in result
            // this can later potentially be used to mend uninitialized field errors
            computeSmtContext(atypeFactory.getStoreBefore(tree), tree);
            // Don't type-check arguments of packing calls.
            return p;
        }
        return super.visitMethodInvocation(tree, p);
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        if (TreeUtils.isFieldAccess(node.getVariable())) {
            // Fields assignments are handled in the PackingVisitor.
            // Nothing to do here.
            return null;
        }
        call(() -> super.visitAssignment(node, p), () -> result.illTypedAssignments.add(node));
        return null;
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        call(() -> super.visitVariable(node, p), () -> result.illTypedVars.add(node));

        AnnotatedTypeMirror varType = atypeFactory.getAnnotatedTypeLhs(node);
        ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
        AnnotatedTypeMirror exclType = exclFactory.getAnnotatedTypeLhs(node);

        // Check abstract state for fields and parameters, not for local variables
        if ((methodTree == null || isParam(node)) && !getTypeValidator().dependsOnlyOnAbstractState(varType, exclType, node)) {
            checker.reportError(node, "type.invalid.abstract.state");
        }

        if (enclMethod == null) {
            if (node.getModifiers().getFlags().contains(Modifier.STATIC)) {
                result.addStaticInvariant(
                        getEnclClassName().toString(),
                        new Invariant(node, varType));

                if (node.getInitializer() != null) {
                    result.addStaticInitializer(getEnclClassName().toString(), Union.left(node));
                }
            } else {   
            	result.addInstanceInvariant(
            			getEnclClassName().toString(),
            			new CooperativeVisitor.Invariant(node, varType));

            	if (node.getInitializer() != null) {
                    result.addInstanceInitializer(getEnclClassName().toString(), Union.left(node));
                }
            }
        }

        return null;
    }

    @Override
    public void processClassTree(ClassTree classTree) {
        ClassTree prevEnclClass = enclClass;
        enclClass = classTree;

        // add refinements for all fields in this class and its super classes to the result
        // these are the _declared_ types that may need to be proven later for packing calls.
        addFieldRefinements(classTree);

        super.processClassTree(classTree);

        enclClass = prevEnclClass;
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        MethodTree prevEnclMethod = enclMethod;
        enclMethod = node;

        result.methodOutputTypes.put(node, new AnnotationMirror[node.getParameters().size() + 1]);

        AnnotatedTypeMirror returnType = atypeFactory.getMethodReturnType(node);
        AnnotatedTypeMirror exclReturnType = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class).getMethodReturnType(node);

        if (!(returnType == null || returnType.getKind() == TypeKind.VOID) && !getTypeValidator().dependsOnlyOnAbstractState(returnType, exclReturnType, node)) {
            checker.reportError(node, "return.type.invalid.abstract.state");
        }

        ExecutableElement methodElement = TreeUtils.elementFromDeclaration(node);
        Map<AnnotatedDeclaredType, ExecutableElement> overriddenMethods =
                AnnotatedTypes.overriddenMethods(elements, atypeFactory, methodElement);

        result.overriddenMethods.put(node, overriddenMethods.entrySet().stream().map(e -> Pair.of(
                        e.getKey(),
                        AnnotatedTypes.asMemberOf(
                                types, atypeFactory, e.getKey(), e.getValue())))
                .collect(Collectors.toList()));

        super.visitMethod(node, p);

        enclMethod = prevEnclMethod;

        return null;
    }

    @Override
    public Void visitBlock(BlockTree node, Void p) {
        boolean prevEnclStaticInitBlock = enclStaticInitBlock;
        boolean prevEnclInstanceInitBlock = enclInstanceInitBlock;

        if (node.isStatic()) {
            enclStaticInitBlock = true;
            result.addStaticInitializer(getEnclClassName().toString(), Union.right(node));
        } else if (enclMethod == null && !enclInstanceInitBlock) {
            enclInstanceInitBlock = true;
            result.addInstanceInitializer(getEnclClassName().toString(), Union.right(node));
        }

        super.visitBlock(node, p);

        enclStaticInitBlock = prevEnclStaticInitBlock;
        enclInstanceInitBlock = prevEnclInstanceInitBlock;

        return null;
    }

    public Name getEnclClassName() {
        return ((JCClassDecl) enclClass).sym.getQualifiedName();
    }

    public Name getEnclMethodNameName() {
        return ((JCMethodDecl) enclMethod).sym.getQualifiedName();
    }

    public LatticeSubchecker getLatticeSubchecker() {
        return (LatticeSubchecker) checker;
    }

    @Override
    public CooperativeChecker getChecker() {
        return (LatticeSubchecker) checker;
    }

    @Override
    public Result getResult() {
        return result;
    }

    @Override
    public CompilationUnitTree getRoot() {
        return root;
    }

    @Override
    public SourcePositions getPositions() {
        return positions;
    }

    protected LatticeTypeValidator getTypeValidator() {
        return (LatticeTypeValidator) typeValidator;
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new LatticeTypeValidator(checker, this, atypeFactory);
    }

    @Override
    protected void checkConstructorInvocation(AnnotatedDeclaredType invocation, AnnotatedExecutableType constructor, NewClassTree newClassTree) {
        super.checkConstructorInvocation(invocation, constructor, newClassTree);
    }

    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {
        for (int i = 0; i < requiredArgs.size(); ++i) {
            int paramIndex = i;
            call(
                    () -> commonAssignmentCheck(
                            requiredArgs.get(paramIndex),
                            passedArgs.get(paramIndex),
                            "argument.type.incompatible", //$NON-NLS-1$
                            paramNames.get(paramIndex).toString(),
                            executableName.toString()),
                    () -> {
                        Tree leaf = getCurrentPath().getLeaf();
                        if (leaf instanceof MethodInvocationTree) {
                            result.addillTypedMethodParam((MethodInvocationTree) getCurrentPath().getLeaf(), paramIndex);
                        } else {
                            result.addillTypedConstructorParam((NewClassTree) getCurrentPath().getLeaf(), paramIndex);
                        }
                    });

            scan(passedArgs.get(i), null);
        }
    }

    @Override
    protected boolean commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        commonAssignmentCheckStartDiagnostic(varType, valueType, valueTree);

        AnnotatedTypeMirror widenedValueType = atypeFactory.getWidenedType(valueType, varType);
        boolean success = atypeFactory.getTypeHierarchy().isSubtype(widenedValueType, varType);

        if (!success && (TypesUtils.isPrimitive(valueType.getUnderlyingType()) || valueTree instanceof LiteralTree)) {
            Lattice lattice = getLatticeSubchecker().getTypeFactory().getLattice();
            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(varType);
            EvaluatedPropertyAnnotation epa = lattice.getEvaluatedPropertyAnnotation(varType);

            if (pa.getAnnotationType().isInv() && pa.getAnnotationType().isNonNull()) {
                success = true;
            } else if (epa != null && epa.isCheckable() && valueTree instanceof LiteralTree literal) {
                PropertyAnnotationType pat = epa.getAnnotationType();

                if (types.isSameType(valueType.getUnderlyingType(), pat.getSubjectType())) {
                    success = epa.checkProperty(literal.getValue());
                } else if (literal.getKind() == Kind.NULL_LITERAL && !pat.getSubjectType().getKind().isPrimitive()) {
                    success = epa.checkProperty(null);
                }
            }
        }

        commonAssignmentCheckEndDiagnostic(success, null, varType, valueType, valueTree);

        if (!(valueType instanceof AnnotatedTypeMirror.AnnotatedTypeVariable)) { // generic types are not supported here
            amendSmtResultForValue(varType, valueType, valueTree, success);
        }

        if (!success) {
            return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
        }

        return success;
    }

    @Override
    protected void checkMethodInvocability(AnnotatedExecutableType method, MethodInvocationTree node) {
        if (method.getReceiverType() != null && method.getElement().getKind() != ElementKind.CONSTRUCTOR) {
            AnnotatedTypeMirror methodReceiver = method.getReceiverType().getErased();
            AnnotatedTypeMirror treeReceiver = methodReceiver.shallowCopy(false);
            AnnotatedTypeMirror rcv = this.atypeFactory.getReceiverType(node);
            treeReceiver.addAnnotations(rcv.getEffectiveAnnotations());
            call(() -> {
                this.commonAssignmentCheckStartDiagnostic(methodReceiver, treeReceiver, node);
                boolean success = this.typeHierarchy.isSubtype(treeReceiver, methodReceiver);
                amendSmtResultForReceiver(methodReceiver, rcv, node, success);
                this.commonAssignmentCheckEndDiagnostic(success, null, methodReceiver, treeReceiver, node);
                if (!success) {
                    this.reportMethodInvocabilityError(node, treeReceiver, methodReceiver);
                }
            }, () -> result.illTypedMethodReceivers.add(node));
        }
    }

    @Override
    protected void checkSuperConstructorCall(MethodInvocationTree superCall) {
        // Nothing to do
    }

    @Override
    protected AnnotationMirror defaultConstructorQualifier(Type classType) {
        return atypeFactory.getTop();
    }

    @Override
    protected void checkImplicitConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);
        if (!qualifierHierarchy.isSubtypeQualifiersOnly(top, constructorAnno) &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isNonNull() &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isInv()) {
            // Report an error instead of a warning.
            checker.reportError(
                    constructorElement, "inconsistent.constructor.type", constructorAnno, top);

            result.illTypedConstructors.add(enclMethod);
        }
    }

    @Override
    protected void checkExplicitConstructorResult(MethodTree tree) {
        AnnotatedExecutableType constructorType = atypeFactory.getAnnotatedType(tree);
        ExecutableElement constructorElement = TreeUtils.elementFromDeclaration(tree);

        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);

        result.methodOutputTypes.get(tree)[0] = constructorAnno;

        if (!qualifierHierarchy.isSubtypeQualifiersOnly(top, constructorAnno) &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isNonNull() &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isInv()) {
            // Report an error instead of a warning.
            checker.reportError(
                    constructorElement, "inconsistent.constructor.type", constructorAnno, top);

            result.illTypedConstructors.add(enclMethod);
        }
    }

    protected static boolean isConstructor(MethodTree tree) {
        JCMethodDecl t = (JCMethodDecl) tree;
        return t.name == t.name.table.names.init;
    }

    /* ==== SMT SOLVING CODE ==== */

    // parse refinement goal for postcondition, compute and add context to result, return goal (or null)
    @Nullable
    private SmtExpression computePostconditionSmt(
            Tree treeKey, AnnotationMirror annotation,
            JavaExpression subject, LatticeStore exitStore) {


        var property = atypeFactory.getLattice().getPropertyAnnotation(annotation);
        var goal = convertGoal(
                viewpointAdapt(parseOrUnknown(property, getCurrentPath()), List.of(subject)),
                subject.toString()
        );

        if (exitStore != null) {
            computeSmtContext(exitStore, treeKey);
        }

        if (goal != null) {
            return goal.smt();
        }
        return null;
    }

    private void amendSmtResultForReceiver(AnnotatedTypeMirror expectedType, AnnotatedTypeMirror valueType,
                                           MethodInvocationTree invocation, boolean typeCheckSuccess) {
        ExpressionTree receiverTree = TreeUtils.getReceiverTree(invocation);
        JavaExpression subject = receiverTree != null
                ? expressionFromTree(receiverTree)
                : JavaExpression.getImplicitReceiver(TreeUtils.elementFromUse(invocation));
        amendSmtResult(expectedType, valueType, invocation.getMethodSelect(),
                subject, typeCheckSuccess, getCurrentPath());
    }

    public void amendSmtResultForValue(AnnotatedTypeMirror varType, AnnotatedTypeMirror valueType,
                                        Tree valueTree, boolean typeCheckSuccess) {
        amendSmtResult(varType, valueType, valueTree,
                expressionFromTree((ExpressionTree) valueTree), typeCheckSuccess, getCurrentPath());
    }

    public void amendSmtResultForValue(AnnotatedTypeMirror varType, AnnotatedTypeMirror valueType,
                                       Tree valueTree, boolean typeCheckSuccess, TreePath path) {
        amendSmtResult(varType, valueType, valueTree,
                expressionFromTree((ExpressionTree) valueTree), typeCheckSuccess, path);
    }

    private void amendSmtResult(
            AnnotatedTypeMirror goalType,
            AnnotatedTypeMirror knownType,
            Tree contextKey,
            JavaExpression subject,
            boolean typeCheckSuccess,
            TreePath path
    ) {
        if (checker.getParentChecker().getBooleanOption(Config.NO_SMT_OPTION, false)) {
            return;
        }

        var property = atypeFactory.getLattice().getPropertyAnnotation(goalType);

        JavaExpression toProve = viewpointAdapt(
                parseOrUnknown(property, path),
                List.of(subject)
        );

        JavaToSmtExpression.Result smtGoal = convertGoal(toProve, subject.toString());

        computeSmtContext(atypeFactory.getStoreBefore(contextKey), contextKey);
        var valueProperty = atypeFactory.getLattice().getPropertyAnnotation(knownType);
        var valueRefinement = viewpointAdapt(
                parseOrUnknown(valueProperty, path),
                List.of(subject)
        );
        tryConvertToSmt(valueRefinement).ifPresent(res -> result.addContext(contextKey, res.smt()));

        if (smtGoal != null) {
            if (typeCheckSuccess) {
                // if we already know that the goal is true (expr is well-typed), we add it to the context
                result.addContext(contextKey, smtGoal.smt());
            } else {
                // if expr is ill-typed, we add the proof goal to the mending conditions
                result.addMendingCondition(contextKey, smtGoal.smt());
            }
        }
    }

    private JavaExpression expressionFromTree(ExpressionTree tree) {
        // the checker framework expression parser does not support constructor calls yet.
        // but we want to support (pure) constructor calls in property subjects anyway, so we represent them as a
        // special method call. Currently, this only works for top level constructor calls, and not if they're nested
        // in a deeper expression.
        // TODO: allow nested constructor calls as well (need to implement own version of JavaExpression.fromTree for that)
        return tree instanceof NewClassTree nc
                ? JavaExpressionUtil.constructorCall(nc)
                : JavaExpression.fromTree(tree);
    }

    private JavaToSmtExpression.Result convertGoal(JavaExpression goal, String subject) {
        if (goal.containsUnknown()) {
            // checker framework couldn't parse the goal refinement
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses language features not supported by the Checker Framework%n",
                    subject, goal);
            return null;
        }

        // all method calls that appear in the goal must be pure, otherwise we won't do analysis
        var impureScanner = new JavaExpressionScanner<>() {
            boolean found = false;

            @Override
            protected Void visitMethodCall(MethodCall methodCallExpr, Object o) {
                var element = methodCallExpr.getElement();
                if (!atypeFactory.isDeterministic(element) || !atypeFactory.isSideEffectFree(element)) {
                    found = true;
                    return null;
                }
                return super.visitMethodCall(methodCallExpr, o);
            }
        };

        goal.accept(impureScanner, null);

        if (impureScanner.found) {
            System.out.printf("Skipping SMT analysis for expression %s because its refinement %s uses an impure method call%n",
                    subject, goal);
            return null;
        }

        try {
            return JavaToSmtExpression.convert(goal);
        } catch (UnsupportedOperationException e) {
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses features currently not supported in SMT: %s%n",
                    subject, goal, e.getMessage());
            return null;
        }
    }

    private void computeSmtContext(LatticeStore store, Tree tree) {
        if (store == null) {
            return;
        }

        store.allRefinements()
                .flatMap(expr -> tryConvertToSmt(expr).stream())
                .forEach(smtResult -> result.addContext(tree, smtResult.smt()));
    }

    /**
     * Parse the refinement of a PropertyAnnotation to a JavaExpression. If there is a parse error, return Unknown type.
     *
     * @param property PropertyAnnotation
     * @param localVarPath TreePath at which the variables used in the property are available.
     * @return resulting expression, or expression of type Unknown
     */
    private JavaExpression parseOrUnknown(PropertyAnnotation property, TreePath localVarPath) {
        try {
            return property.parseRefinement(localVarPath, checker);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            return new Unknown(bool, property.combinedRefinement("$subject"));
        }
    }

    private JavaExpression parseOrUnknown(PropertyAnnotation property, VariableElement field) {
        try {
            return property.parseRefinement(field, checker);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            return new Unknown(bool, property.combinedRefinement("$subject"));
        }
    }


    private Optional<JavaToSmtExpression.Result> tryConvertToSmt(JavaExpression expr) {
        try {
            return Optional.of(JavaToSmtExpression.convert(expr));
        } catch (UnsupportedOperationException e) {
            return Optional.empty();
        }
    }

    private void addFieldRefinements(ClassTree classTree) {
        var top = atypeFactory.getTop();
        TypeElement classElement = TreeUtils.elementFromDeclaration(classTree);
        List<VariableElement> fields = ElementUtils.getAllFieldsIn(classElement, elements);
        for (VariableElement field : fields) {
            if (result.hasFieldRefinement(field)) {
                // field refinement in this lattice has already been collected
                continue;
            }
            FieldAccess fieldAccess = new FieldAccess(new ThisReference(field.getEnclosingElement().asType()), field);
            var fieldType = atypeFactory.getAnnotatedType(field);
            if (!qualHierarchy.isSubtypeQualifiersOnly(top, fieldType.getEffectiveAnnotationInHierarchy(top))) {
                // only include refinement if field type is not a top type
                var property = atypeFactory.getLattice().getPropertyAnnotation(fieldType);
                JavaExpression expr =
                        viewpointAdapt(parseOrUnknown(property, field), List.of(fieldAccess));
                try {
                    result.addFieldRefinement(field, JavaToSmtExpression.convert(expr).smt());
                } catch (UnsupportedOperationException e) {
                    System.out.printf("Skipping SMT analysis of field %s.%s: %s%n",
                            classElement, field.getSimpleName(), e.getMessage());
                }
            }
        }
    }

}
