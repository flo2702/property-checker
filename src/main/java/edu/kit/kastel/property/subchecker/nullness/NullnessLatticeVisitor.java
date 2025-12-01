package edu.kit.kastel.property.subchecker.nullness;

import com.sun.source.tree.*;
import com.sun.source.util.SourcePositions;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.util.Pair;
import edu.kit.kastel.property.util.TypeUtils;
import edu.kit.kastel.property.util.Union;
import org.apache.commons.lang3.tuple.Triple;
import org.checkerframework.checker.nullness.NullnessNoInitAnnotatedTypeFactory;
import org.checkerframework.checker.nullness.NullnessNoInitVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.Name;
import java.util.*;
import java.util.stream.Collectors;

public class NullnessLatticeVisitor extends NullnessNoInitVisitor implements CooperativeVisitor {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    private CooperativeVisitor.Result result;

    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;

    protected Set<JavaExpression> paramsInContract = new HashSet<>();

    public NullnessLatticeVisitor(BaseTypeChecker checker, NullnessLatticeAnnotatedTypeFactory typeFactory) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());

        result = new CooperativeVisitor.Result(getNullnessLatticeSubchecker());
    }

    public NullnessLatticeVisitor(BaseTypeChecker checker) {
        this(checker, null);
    }

    @Override
    public NullnessNoInitAnnotatedTypeFactory createTypeFactory() {
        return new NullnessLatticeAnnotatedTypeFactory(checker);
    }

    @Override
    public NullnessLatticeSubchecker getChecker() {
        return (NullnessLatticeSubchecker) checker;
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

    @Override
    public void visit(TreePath path) {
        super.visit(path);

        ((PropertyChecker) checker.getParentChecker()).addResult(getAbsoluteSourceFileName(), result);
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        call(() -> super.visitReturn(node, p), () -> result.illTypedMethodResults.add(enclMethod));
        return null;
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();
        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            // Don't type-check arguments of packing calls.
            return p;
        }
        return super.visitMethodInvocation(tree, p);
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        if (TreeUtils.isFieldAccess(node.getVariable())) {
            // Fields can be assigned any value if the receiver is sufficiently unpacked, and cannot be assigned at all
            // otherwise. Nothing to check.
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

        if (enclMethod == null) {
            if (node.getModifiers().getFlags().contains(Modifier.STATIC)) {
                result.addStaticInvariant(
                        getEnclClassName().toString(),
                        new LatticeVisitor.Invariant(node.getName().toString(), varType));

                if (node.getInitializer() != null) {
                    result.addStaticInitializer(getEnclClassName().toString(), Union.left(node));
                }
            } else {
                result.addInstanceInvariant(
                        getEnclClassName().toString(),
                        new LatticeVisitor.Invariant(node.getName().toString(), varType));

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

        super.processClassTree(classTree);

        enclClass = prevEnclClass;
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        call(
                () -> super.checkPostcondition(methodTree, annotation, expression),
                () -> this.result.nullnessPostconditions.get(methodTree).addLast(Pair.of(annotation, expression)));
    }

    @Override
    protected void checkConditionalPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression, boolean result) {
        call(
                () -> super.checkConditionalPostcondition(methodTree, annotation, expression, result),
                () -> this.result.nullnessCondPostconditions.get(methodTree).addLast(Triple.of(annotation, expression, result)));
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        MethodTree prevEnclMethod = enclMethod;
        enclMethod = node;

        result.methodOutputTypes.put(node, new AnnotationMirror[node.getParameters().size() + 1]);
        result.nullnessPostconditions.put(node, new ArrayList<>());
        result.nullnessCondPostconditions.put(node, new ArrayList<>());

        ExecutableElement methodElement = TreeUtils.elementFromDeclaration(node);
        Map<AnnotatedTypeMirror.AnnotatedDeclaredType, ExecutableElement> overriddenMethods =
                AnnotatedTypes.overriddenMethods(elements, atypeFactory, methodElement);

        result.overriddenMethods.put(node, overriddenMethods.entrySet().stream().map(e -> Pair.of(
                        e.getKey(),
                        AnnotatedTypes.asMemberOf(
                                types, atypeFactory, e.getKey(), e.getValue())))
                .collect(Collectors.toList()));

        // check that params not covered by explicit contract fulfill their input type
        VariableTree receiver = node.getReceiverParameter();
        if (receiver != null) {
            result.methodOutputTypes.get(node)[0] = atypeFactory.getAnnotatedTypeLhs(receiver).getEffectiveAnnotationInHierarchy(getLattice().getTop());
        }
        for (VariableTree param : node.getParameters()) {
            final int paramIdx = TypeUtils.getParameterIndex(node, param);
            result.methodOutputTypes.get(node)[paramIdx] = atypeFactory.getAnnotatedTypeLhs(param).getEffectiveAnnotationInHierarchy(getLattice().getTop());
        }

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
        return ((JCTree.JCClassDecl) enclClass).sym.getQualifiedName();
    }

    public Name getEnclMethodNameName() {
        return ((JCTree.JCMethodDecl) enclMethod).sym.getQualifiedName();
    }

    public NullnessLatticeSubchecker getNullnessLatticeSubchecker() {
        return (NullnessLatticeSubchecker) checker;
    }

    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {
        for (int i = 0; i < requiredArgs.size(); ++i) {
            final int idx = i;
            call(
                    () -> commonAssignmentCheck(
                            requiredArgs.get(idx),
                            passedArgs.get(idx),
                            "argument.type.incompatible", //$NON-NLS-1$
                            // idx >= paramNames.size() is true if the called method has varargs
                            idx >= paramNames.size() ? paramNames.getLast().toString() : paramNames.get(idx).toString(),
                            executableName.toString()),
                    () -> {
                        Tree leaf = getCurrentPath().getLeaf();
                        if (leaf instanceof MethodInvocationTree) {
                            result.addillTypedMethodParam((MethodInvocationTree) getCurrentPath().getLeaf(), idx);
                        } else {
                            result.addillTypedConstructorParam((NewClassTree) getCurrentPath().getLeaf(), idx);
                        }
                    });

            scan(passedArgs.get(i), null);
        }
    }

    @Override
    protected void checkMethodInvocability(AnnotatedTypeMirror.AnnotatedExecutableType method, MethodInvocationTree node) {
        call(
                () -> super.checkMethodInvocability(method, node),
                () -> result.illTypedMethodReceivers.add(node));
    }

}
