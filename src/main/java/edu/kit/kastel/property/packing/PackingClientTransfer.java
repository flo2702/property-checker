package edu.kit.kastel.property.packing;

import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.tools.javac.code.Symbol;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractTransfer;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.*;
import org.checkerframework.javacutil.BugInCF;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Set;

public abstract class PackingClientTransfer<
        V extends PackingClientValue<V>,
        S extends PackingClientStore<V, S>,
        T extends PackingClientTransfer<V, S, T>>
        extends CFAbstractTransfer<V, S, T> {

    protected PackingClientTransfer(CFAbstractAnalysis<V, S, T> analysis) {
        super(analysis);
    }

    protected PackingClientTransfer(CFAbstractAnalysis<V, S, T> analysis, boolean forceConcurrentSemantics) {
        super(analysis, forceConcurrentSemantics);
    }

    @SuppressWarnings("unchecked")
    public PackingClientAnalysis<?,?,?> getAnalysis() {
        return (PackingClientAnalysis<?,?,?>) analysis;
    }

    protected abstract V initialThisValue(MethodTree methodDeclTree);

    @Override
    public S initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        ((PackingClientAnalysis<?, ?, ?>) analysis).setPosition(underlyingAST.getCode());
        S initStore = super.initialStore(underlyingAST, parameters);
        PackingClientAnnotatedTypeFactory<?, ?, ?, ?> factory = getAnalysis().getTypeFactory();

        if (underlyingAST.getKind() == UnderlyingAST.Kind.METHOD) {
            // Add receiver value
            UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
            MethodTree methodDeclTree = method.getMethod();
            V initialThisValue = null;
            if (TreeUtils.isConstructor(methodDeclTree) || methodDeclTree.getReceiverParameter() != null) {
                initialThisValue = initialThisValue(methodDeclTree);
                initStore.initializeThisValue(initialThisValue);
            }

            if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                // add fields declared in this class and all superclasses to store
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                AnnotatedTypeMirror receiverType =
                        factory.getSelfType(methodDeclTree.getBody());
                if (initialThisValue != null) {
                    receiverType.replaceAnnotations(initStore.getValue((ThisNode) null).getAnnotations());
                }

                AnnotatedTypeMirror receiverPackingType =
                        packingFactory.getSelfType(methodDeclTree.getBody());
                insertFieldsUpToFrame(initStore, receiverType, receiverPackingType, true, TreeUtils.isConstructor(methodDeclTree));
            }
            addInformationFromPreconditions(initStore, factory, method, methodDeclTree, TreeUtils.elementFromDeclaration(methodDeclTree));
        }

        return initStore;
    }

    protected void insertFieldsUpToFrame(
            S store, AnnotatedTypeMirror receiverType, AnnotatedTypeMirror receiverPackingType, boolean removeUncommitted, boolean beginningOfConstructor) {
        var factory = getAnalysis().getTypeFactory();
        PackingFieldAccessAnnotatedTypeFactory packingFactory =
                factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
        List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                TypesUtils.getTypeElement(receiverType.getUnderlyingType()),
                factory.getElementUtils());
        for (VariableElement field : allFields) {
            if (!ElementUtils.isStatic(field)) {
                ((PackingClientAnalysis<V, S, T>) analysis).setPosition(field);
                FieldAccess fieldAccess = new FieldAccess(new ThisReference(receiverType.getUnderlyingType()), field);
                TypeMirror fieldOwnerType = field.getEnclosingElement().asType();
                AnnotatedTypeMirror declaredType = factory.getAnnotatedType(field);

                // Viewpoint-adapt type
                AnnotatedTypeMirror adaptedType =
                        AnnotatedTypes.asMemberOf(
                                analysis.getTypes(),
                                analysis.getTypeFactory(),
                                receiverType,
                                field,
                                declaredType);

                if (adaptedType == null) {
                    adaptedType = declaredType;
                }


                if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)
                        && (!adaptedType.getKind().isPrimitive() || uncommitPrimitiveFields())) {
                    if (store.getValue(fieldAccess) == null || removeUncommitted) {
                        // If field is not initialized and not in store yet or uncommitted field values
                        // should be removed, insert the top value
                        adaptedType.clearAnnotations();
                        // Special case: At the beginning of a constructor, fields have the default value null,
                        // which we can consider @Unique
                        if (beginningOfConstructor && factory instanceof ExclusivityAnnotatedTypeFactory exclFactory) {
                            adaptedType.addAnnotation(exclFactory.UNIQUE);
                        } else {
                            adaptedType.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
                        }
                        V value = analysis.createAbstractValue(adaptedType);
                        store.insertValue(fieldAccess, value);
                    }
                } else {
                    // if field is initialized, insert its declared type
                    V value = analysis.createAbstractValue(adaptedType);
                    store.insertValue(fieldAccess, value);
                }
            }
        }
    }

    protected abstract boolean uncommitPrimitiveFields();

    @Override
    public TransferResult<V, S> visitMethodInvocation(MethodInvocationNode n, TransferInput<V, S> in) {
        return addExceptionalStores(n, in, super.visitMethodInvocation(n, in));
    }

    protected TransferResult<V, S> addExceptionalStores(MethodInvocationNode n, TransferInput<V, S> in, TransferResult<V, S> result) {
        /*if (n.getBlock() instanceof ExceptionBlock eb) {
            Map<TypeMirror, S> exceptionalStores = new HashMap<>();
            S excStore = in.getRegularStore().copy();

            in.getRegularStore().getFieldValues().keySet().forEach(f -> excStore.insertValue(f, topValue(f.getType())));
            n.getArguments().forEach(a -> excStore.insertValue(JavaExpression.fromNode(n), topValue(n.getType())));
            excStore.insertValue(JavaExpression.fromNode(n.getTarget().getReceiver()), topValue(n.getTarget().getReceiver().getType()));
            eb.getExceptionalSuccessors().keySet().forEach(cause -> exceptionalStores.put(cause, excStore));

            return new RegularTransferResult<>(result.getResultValue(), result.getRegularStore(), exceptionalStores);
        }*/
        return result;
    }

    public V topValue(TypeMirror underlyingType) {
        return analysis.createSingleAnnotationValue(
                analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().first(),
                underlyingType);
    }

    @Override
    protected void processPostconditions(Node invocationNode, S store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        if (executableElement instanceof Symbol.MethodSymbol meth && meth.owner.toString().equals("java.lang.Enum")) {
            // nothing to check
            return;
        }

        ContractsFromMethod contractsUtils = analysis.getTypeFactory().getContractsFromMethod();
        Set<Contract.Postcondition> postconditions = contractsUtils.getPostconditions(executableElement);
        ExclusivityAnnotatedTypeFactory exclFactory;
        if (this instanceof ExclusivityTransfer) {
            exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory();
        } else {
            exclFactory = analysis.getTypeFactory().getTypeFactoryOfSubchecker(ExclusivityChecker.class);
        }

        boolean sideEffectFree;
        StringToJavaExpression stringToJavaExpr;
        if (invocationNode instanceof MethodInvocationNode) {
            sideEffectFree = analysis.getTypeFactory().isSideEffectFree(((MethodInvocationNode) invocationNode).getTarget().getMethod());
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    (MethodInvocationNode) invocationNode,
                                    analysis.getTypeFactory().getChecker());

            // Set receiver output type to input type by default (unless receiver is @ReadOnly).
            Node receiver = ((MethodInvocationNode) invocationNode).getTarget().getReceiver();

            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse((MethodInvocationTree) invocationNode.getTree());
            AnnotatedTypeFactory.ParameterizedExecutableType exclMethod =
                    exclFactory.methodFromUse((MethodInvocationTree) invocationNode.getTree());
            AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
            AnnotatedTypeMirror exclReceiverType = exclMethod.executableType.getReceiverType();

            if (receiverType != null && !exclReceiverType.hasAnnotation(ReadOnly.class)) {
                V receiverDefaultValue = analysis.createAbstractValue(
                        receiverType.getAnnotations(),
                        receiverType.getUnderlyingType());

                AnnotationMirror nonNull = receiverType.getAnnotations().stream()
                        .filter(a -> a.getAnnotationType().asElement().getSimpleName().contentEquals("NonNull"))
                        .findAny().orElse(null);
                if (nonNull != null) {
                    store.insertOrRefine(JavaExpression.fromNode(receiver), nonNull);
                } else if (sideEffectFree) {
                    store.insertOrRefine(JavaExpression.fromNode(receiver), receiverDefaultValue.getAnnotations().first());
                } else {
                    store.insertValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
                }
            }

            try {
                // Set parameter output types to input type by default (unless param is @ReadOnly or primitive).
                int i = 0;
                List<AnnotatedTypeMirror> exclParamTypes = exclMethod.executableType.getParameterTypes();
                for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                    boolean paramReadOnly = exclParamTypes.get(i).hasAnnotation(ReadOnly.class);
                    if (!paramReadOnly && !paramType.getKind().isPrimitive()) {
                        V paramDefaultValue = analysis.createAbstractValue(
                                paramType.getAnnotations(),
                                paramType.getUnderlyingType());
                        if (sideEffectFree) {
                            if (!paramDefaultValue.getAnnotations().isEmpty()) {
                                store.insertOrRefine(
                                        JavaExpression.fromNode(TypeUtils.getArgumentWithVarargs((MethodInvocationNode) invocationNode, i)),
                                        paramDefaultValue.getAnnotations().first());
                            }
                        } else {
                            store.insertValue(
                                    JavaExpression.fromNode(TypeUtils.getArgumentWithVarargs((MethodInvocationNode) invocationNode, i)),
                                    paramDefaultValue);
                        }
                    }

                    ++i;
                }
            } catch (IndexOutOfBoundsException e) {
                //TODO
                return;
            }
        } else if (invocationNode instanceof ObjectCreationNode) {
            sideEffectFree = false;
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atConstructorInvocation(
                                    stringExpr, (NewClassTree) invocationTree, analysis.getTypeFactory().getChecker());

            // Set parameter output types to input type by default.
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().constructorFromUse((NewClassTree) invocationNode.getTree());
            AnnotatedTypeFactory.ParameterizedExecutableType exclMethod =
                    exclFactory.constructorFromUse((NewClassTree) invocationNode.getTree());
            int i = 0;
            List<AnnotatedTypeMirror> exclParamTypes = exclMethod.executableType.getParameterTypes();
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                boolean paramReadOnly = exclParamTypes.get(i).hasAnnotation(ReadOnly.class);
                if (!paramReadOnly) {
                    V paramDefaultValue = analysis.createAbstractValue(
                            paramType.getAnnotations(),
                            paramType.getUnderlyingType());
                    store.insertValue(
                            JavaExpression.fromNode(((ObjectCreationNode) invocationNode).getArgument(i)),
                            paramDefaultValue);
                }

                ++i;
            }
        } else {
            throw new BugInCF(
                    "CFAbstractTransfer.processPostconditionsAndConditionalPostconditions"
                            + " expects a MethodInvocationNode or ObjectCreationNode argument;"
                            + " received a "
                            + invocationNode.getClass().getSimpleName());
        }

        for (Contract p : postconditions) {
            // Viewpoint-adapt to the method use (the call site).
            AnnotationMirror anno =
                    p.viewpointAdaptDependentTypeAnnotation(
                            analysis.getTypeFactory(), stringToJavaExpr, /* errorTree= */ null);

            String expressionString = p.expressionString;
            try {
                JavaExpression je = stringToJavaExpr.toJavaExpression(expressionString);

                // Unlike the superclass implementation, this calls
                // "insertValue" which for our type system replaces existing information instead of adding to it.
                // This is done because we use postconditions to implement output types for the parameters, which may
                // be incompatible with the input types. If a parameter has no explicit output type, we use its input
                // type as default, which is implemented above.
                if (sideEffectFree) {
                    store.insertOrRefine(je, anno);
                } else {
                    store.insertValue(je, anno);
                }
            } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                // report errors here
                if (e.isFlowParseError()) {
                    Object[] args = new Object[e.args.length + 1];
                    args[0] =
                            ElementUtils.getSimpleSignature(
                                    (ExecutableElement) TreeUtils.elementFromUse(invocationTree));
                    System.arraycopy(e.args, 0, args, 1, e.args.length);
                    analysis.getTypeFactory().getChecker().reportError(
                            invocationTree, "flowexpr.parse.error.postcondition", args);
                } else {
                    analysis.getTypeFactory().getChecker().report(invocationTree, e.getDiagMessage());
                }
            }
        }
    }
}
