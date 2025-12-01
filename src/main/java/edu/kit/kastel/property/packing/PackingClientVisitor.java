package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.TargetType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.JavaExpressionScanner;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.plumelib.util.ArraySet;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public abstract class PackingClientVisitor<
        Factory extends PackingClientAnnotatedTypeFactory<
                ? extends PackingClientValue<?>,
                ? extends PackingClientStore<?, ?>,
                ? extends PackingClientTransfer<?, ?, ?>,
                ? extends PackingClientAnalysis<?, ?, ?>>>
        extends BaseTypeVisitor<Factory> {

    protected Set<JavaExpression> paramsInContract = new HashSet<>();

    public PackingClientVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    protected PackingClientVisitor(BaseTypeChecker checker, @Nullable Factory typeFactory) {
        super(checker, typeFactory);
    }

    protected abstract AnnotationMirror defaultConstructorQualifier(Type classType);

    @Override
    public Void visitMethod(MethodTree tree, Void p) {
        super.visitMethod(tree, p);

        // check that params not covered by explicit contract fulfill their input type
        VariableTree receiver = tree.getReceiverParameter();
        if (receiver != null) {
            checkDefaultContract(receiver, tree, atypeFactory.getRegularExitStore(tree));
        }
        for (VariableTree param : tree.getParameters()) {
            checkDefaultContract(param, tree, atypeFactory.getRegularExitStore(tree));
        }

        if (TreeUtils.isConstructor(tree) && ! TreeUtils.isSynthetic(tree)) {
            checkExplicitConstructorResult(tree);
        }

        return p;
    }

    @Override
    protected void checkThisConstructorCall(MethodInvocationTree thisCall) {
        // nothing to do
    }

    @Override
    protected final void checkConstructorResult(AnnotatedTypeMirror.AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // Explicit constructurs are treated by ::checkExplicitConstructorResult, which is called directly by visitMethod.
        checkImplicitConstructorResult(constructorType, constructorElement);
    }

    protected void checkImplicitConstructorResult(AnnotatedTypeMirror.AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        super.checkConstructorResult(constructorType, constructorElement);
    }

    protected void checkExplicitConstructorResult(MethodTree tree) {
        if (atypeFactory.getRegularExitStore(tree) == null) {
            return;
        }

        // Compare the this value in the constructor's exit store to the declared
        // constructor type.
        PackingClientValue<?> thisValue = atypeFactory.getRegularExitStore(tree).getValue((ThisNode) null);
        Type classType = ((JCTree.JCMethodDecl) tree).sym.owner.type;
        AnnotationMirror declared;
        // Default declared type if no explicit annotation is given
        declared = defaultConstructorQualifier(classType);
        for (AnnotationMirror anno : getConstructorAnnotations(tree)) {
            if (atypeFactory.isSupportedQualifier(anno)) {
                declared = anno;
                break;
            }
        }
        AnnotationMirror top = qualHierarchy.getTopAnnotations().first();

        if (thisValue == null) {
            if (!AnnotationUtils.areSame(top, declared)) {
                checker.reportError(tree, "inconsistent.constructor.type", tree);
            }
        } else {
            AnnotationMirror actual = qualHierarchy.findAnnotationInHierarchy(
                    thisValue.getAnnotations(), atypeFactory.getQualifierHierarchy().getTopAnnotations().first());
            if (!qualHierarchy.isSubtypeQualifiersOnly(actual, declared)) {
                checker.reportError(tree, "inconsistent.constructor.type", tree);
            }
        }
    }

    protected final boolean isParam(Tree expr) {
        if (methodTree == null) {
            // We're in an initialization block; so there are no params
            return false;
        }

        if (expr instanceof IdentifierTree) {
            IdentifierTree ident = (IdentifierTree) expr;
            if (ident.getName().toString().equals("this")) {
                return true;
            }

            for (VariableTree param : methodTree.getParameters()) {
                if (param.getName().equals(ident.getName())) {
                    return true;
                }
            }
        } else if (expr instanceof VariableTree) {
            VariableTree var = (VariableTree) expr;
            if (var.getName().toString().equals("this")) {
                return true;
            }

            for (VariableTree param : methodTree.getParameters()) {
                if (param.getName().equals(var.getName())) {
                    return true;
                }
            }
        }

        return false;
    }

    private AnnotationMirrorSet getConstructorAnnotations(MethodTree tree) {
        if (TreeUtils.isConstructor(tree)) {
            com.sun.tools.javac.code.Symbol meth =
                    (com.sun.tools.javac.code.Symbol) TreeUtils.elementFromDeclaration(tree);
            return new AnnotationMirrorSet(
                    meth.getRawTypeAttributes().stream().filter(anno -> anno.position.type.equals(TargetType.METHOD_RETURN))
                            .collect(Collectors.toList()));
        }
        return AnnotationMirrorSet.emptySet();
    }

    protected String getContractPostconditionNotSatisfiedMessage() {
        return "contracts.postcondition.not.satisfied";
    }

    /**
     * Scans a {@link JavaExpression} and adds all the parameters in the {@code JavaExpression} to
     * the passed set.
     */
    private final JavaExpressionScanner<Set<Element>> findParameters =
            new JavaExpressionScanner<Set<Element>>() {
                @Override
                protected Void visitLocalVariable(
                        LocalVariable localVarExpr, Set<Element> parameters) {
                    if (localVarExpr.getElement().getKind() == ElementKind.PARAMETER) {
                        parameters.add(localVarExpr.getElement());
                    }
                    return super.visitLocalVariable(localVarExpr, parameters);
                }
            };

    /**
     * Check that the parameters used in {@code javaExpression} are effectively final for method
     * {@code method}.
     *
     * @param methodDeclTree a method declaration
     * @param javaExpression a Java expression
     */
    protected boolean checkParametersAreEffectivelyFinal(
            MethodTree methodDeclTree, JavaExpression javaExpression) {
        // Paremeters must be effectively final, so we can check their corresponding postcondition.
        // For nullness, there is nothing to check. For exclusivity, reassigning parameters is allowed as long as this
        // always preserves the parameter's postcondition, which is checked in the ExclusivityVisitor.

        if (this instanceof ExclusivityVisitor || (this instanceof LatticeVisitor lv && lv.getLattice().getIdent().equals("nullness"))) {
            return true;
        }

        Set<Element> parameters = new ArraySet<>(2);
        findParameters.scan(javaExpression, parameters);
        for (Element parameter : parameters) {
            if (!ElementUtils.isEffectivelyFinal(parameter)) {
                checker.reportError(
                        methodDeclTree,
                        "flowexpr.parameter.not.final",
                        parameter.getSimpleName(),
                        javaExpression);
                return false;
            }
        }
        return true;
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        paramsInContract.add(expression);
        if (!checkParametersAreEffectivelyFinal(methodTree, expression)) {
            return;
        }

        CFAbstractStore<?, ?> exitStore = atypeFactory.getRegularExitStore(methodTree);
        if (exitStore == null) {
            // If there is no regular exitStore, then the method cannot reach the regular exit and
            // there is no need to check anything.
        } else if (atypeFactory.getQualifierHierarchy().getTopAnnotations().contains(annotation)) {
            // top annotation is always fulfilled
        } else {
            CFAbstractValue<?> value = exitStore.getValue(expression);
            AnnotationMirror inferredAnno = null;
            if (value != null) {
                AnnotationMirrorSet annos = value.getAnnotations();
                inferredAnno = qualHierarchy.findAnnotationInSameHierarchy(annos, annotation);
            }
            if (!checkContract(expression, annotation, inferredAnno, exitStore)) {
                if (expression.toString().equals("this") && atypeFactory instanceof LatticeAnnotatedTypeFactory latticeFactory
                        && latticeFactory.getLattice().getPropertyAnnotation(annotation).getAnnotationType().isNonNull()) {
                    return;
                }

                checker.reportError(
                        methodTree,
                        getContractPostconditionNotSatisfiedMessage(),
                        methodTree.getName(),
                        contractExpressionAndType(expression.toString(), inferredAnno),
                        contractExpressionAndType(expression.toString(), annotation));
            }
        }
    }

    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingClientStore<?, ?> exitStore) {
        // Paremeters must be effectively final, so we can check their corresponding postcondition.
        // For nullness, there is nothing to check. For exclusivity, reassigning parameters is allowed as long as this
        // always preserves the parameter's postcondition, which is checked in the ExclusivityVisitor.
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(((JCTree) param).type);
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }

        if (!paramsInContract.contains(paramExpr)) {
            if (!checkParametersAreEffectivelyFinal(methodTree, paramExpr)) {
                return;
            }

            Element paramElem = TreeUtils.elementFromDeclaration(param);
            AnnotatedTypeMirror currentType = atypeFactory.getAnnotatedType(param);
            if (exitStore != null) {
                PackingClientValue<?> valueAfterMethod = exitStore.getValue(paramExpr);
                if (valueAfterMethod != null) {
                    currentType.replaceAnnotations(valueAfterMethod.getAnnotations());
                }
            }

            AnnotatedTypeMirror declType = atypeFactory.getAnnotatedTypeLhs(param);

            // TODO: There's a better way of doing this.
            if (paramExpr instanceof ThisReference && declType.getAnnotations().stream().anyMatch(a -> a.getAnnotationType().asElement().getSimpleName().contentEquals("NonNull"))) {
                return;
            }

            if (!typeHierarchy.isSubtype(currentType, declType)) {
                checker.reportError(
                        methodTree,
                        getContractPostconditionNotSatisfiedMessage(),
                        methodTree.getName(),
                        contractExpressionAndType(paramElem.toString(), currentType.getAnnotationInHierarchy(atypeFactory.getQualifierHierarchy().getTopAnnotations().first())),
                        contractExpressionAndType(paramElem.toString(), declType.getAnnotationInHierarchy(atypeFactory.getQualifierHierarchy().getTopAnnotations().first())));
            }
        }
    }
}
