package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.Symbol;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.checker.initialization.InitializationAbstractTransfer;
import org.checkerframework.checker.initialization.qual.FBCBottom;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.Contract;
import org.checkerframework.framework.util.ContractsFromMethod;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Set;

public class PackingTransfer extends InitializationAbstractTransfer<CFValue, PackingStore, PackingTransfer> {

    public PackingTransfer(PackingAnalysis analysis) {
        super(analysis);
    }

    @Override
    public PackingStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        PackingStore initStore = super.initialStore(underlyingAST, parameters);

        // Add receiver value
        if (underlyingAST instanceof UnderlyingAST.CFGMethod method) {
            MethodTree methodDeclTree = method.getMethod();
            if (TreeUtils.isConstructor(methodDeclTree)) {
                @SuppressWarnings("deprecation")
                TypeMirror thisType = TreeUtils.elementFromTree(method.getClassTree()).asType();
                TypeMirror superType = TypesUtils.getSuperclass(thisType, atypeFactory.types);
                initStore.initializeThisValue(atypeFactory.createUnderInitializationAnnotation(superType), thisType);
            } else if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                VariableTree recvParam = methodDeclTree.getReceiverParameter();
                boolean thisUnique;
                AnnotationMirror thisAnno;

                @SuppressWarnings("deprecation")
                TypeMirror thisUnderlyingType;

                if (recvParam != null) {
                    AnnotatedTypeMirror thisType = atypeFactory.getAnnotatedType(recvParam);
                    thisAnno = thisType.getAnnotationInHierarchy(
                            AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), UnderInitialization.class));
                    thisUnique = recvParam.getModifiers().getAnnotations().stream().anyMatch(anno -> anno.toString().equals("@Unique"));
                    thisUnderlyingType = thisType.getUnderlyingType();
                } else {
                    thisUnique = false;
                    thisAnno = ((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).getInitialized();
                    thisUnderlyingType = TreeUtils.elementFromTree(method.getClassTree()).asType();
                }

                PackingChecker checker = ((PackingFieldAccessSubchecker) atypeFactory.getChecker()).getPackingChecker();
                if (atypeFactory.isUnknownInitialization(thisAnno) || !thisUnique || !checker.shouldInferUnpack()) {
                    // Variables of type @UnknownInitialization or not of type @Unique must not be unpacked,
                    // so we use the input type in the initial store
                    initStore.initializeThisValue(thisAnno, thisUnderlyingType);
                } else {
                    // Other variables may be unpacked. We make them @UnderInitialization(Object.class) in the initial
                    // store, so the programmer doesn't need to write the unpack statement explicitly.
                    initStore.initializeThisValue(atypeFactory.createUnderInitializationAnnotation(Object.class), thisUnderlyingType);
                }
            }
        }

        return initStore;
    }

    @Override
    public TransferResult<CFValue, PackingStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<CFValue, PackingStore> in) {
        PackingStore store = in.getRegularStore();
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        if (receiver instanceof ClassNameNode) {
            String receiverName = ((ClassNameNode) receiver).getElement().toString();

            if (receiverName.equals(Packing.class.getName())) {
                JavaExpression objToPack = JavaExpression.fromNode(n.getArgument(0));

                ClassNameNode className = (ClassNameNode) ((FieldAccessNode) n.getArgument(1)).getReceiver();
                TypeMirror typeArg = ClassUtils.typeForName(
                        ((Symbol.ClassSymbol) className.getElement()).getQualifiedName().toString(),
                        (PackingFieldAccessSubchecker) atypeFactory.getChecker()
                );

                TypeMirror typeToPackTo;

                if (method.getSimpleName().contentEquals("pack")) {
                    typeToPackTo = typeArg;
                } else /*if (method.getSimpleName().contentEquals("unpack"))*/ {
                    typeToPackTo = TypesUtils.getSuperclass(typeArg, analysis.getTypes());
                }

                if (typeToPackTo == null) {
                    // This happens when the user tries to unpack from a type with no super type.
                    store.insertValue(objToPack, AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), FBCBottom.class));
                    return new RegularTransferResult<>(null, store, true);
                }

                CFValue oldVal = store.getValue(objToPack);
                AnnotationMirror newAnnotation;
                if (TypesUtils.getTypeElement(typeToPackTo).getModifiers().contains(Modifier.FINAL)) {
                    newAnnotation = AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), Initialized.class);
                } else if (oldVal != null && AnnotationUtils.containsSameByClass(oldVal.getAnnotations(), UnknownInitialization.class)) {
                    newAnnotation = atypeFactory.createUnknownInitializationAnnotation(typeToPackTo);
                } else {
                    newAnnotation = atypeFactory.createUnderInitializationAnnotation(typeToPackTo);
                }

                store.insertValue(objToPack, newAnnotation);
                return new RegularTransferResult<>(null, store, true);
            }
        }

        if (n.getTarget().getReceiver() instanceof ThisNode
                && (n.getTarget().getMethod().getReceiverType().getAnnotation(UnderInitialization.class) != null
                    || n.getTarget().getMethod().getReceiverType().getAnnotation(UnknownInitialization.class) != null)) {
            TransferResult<CFValue, PackingStore> result = super.visitMethodInvocation(n, in);
            result.getRegularStore().helperFunctionWasCalled();
            return result;
        }

        TransferResult<CFValue, PackingStore> result = super.visitMethodInvocation(n, in);
        /*if (n.getBlock() instanceof ExceptionBlock eb) {
            Map<TypeMirror, PackingStore> exceptionalStores = new HashMap<>();
            PackingStore excStore = in.getRegularStore().copy();

            in.getRegularStore().getFieldValues().keySet().forEach(f -> excStore.insertValue(f, topValue(f.getType())));
            n.getArguments().forEach(a -> excStore.insertValue(JavaExpression.fromNode(n), topValue(n.getType())));
            excStore.insertValue(JavaExpression.fromNode(n.getTarget().getReceiver()), topValue(n.getTarget().getReceiver().getType()));
            eb.getExceptionalSuccessors().keySet().forEach(cause -> exceptionalStores.put(cause, excStore));

            return new RegularTransferResult<>(result.getResultValue(), result.getRegularStore(), exceptionalStores);
        }*/

        return result;
    }

    @Override
    public TransferResult<CFValue, PackingStore> visitAssignment(AssignmentNode n, TransferInput<CFValue, PackingStore> in) {
        TransferResult<CFValue, PackingStore> result = super.visitAssignment(n, in);
        if (n.getTarget() instanceof FieldAccessNode fa && PackingAnnotatedTypeFactory.isDependableField(fa.getElement())) {
            result.getRegularStore().setDependableFieldAssigned(true);
            result.storeChanged();
        }
        return result;
    }

    public CFValue topValue(TypeMirror underlyingType) {
        return analysis.createSingleAnnotationValue(
                analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().first(),
                underlyingType);
    }

    @Override
    protected void processPostconditions(Node invocationNode, PackingStore store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        if (executableElement instanceof Symbol.MethodSymbol meth && meth.owner.toString().equals("java.lang.Enum")) {
            // nothing to check
            return;
        }

        ContractsFromMethod contractsUtils = analysis.getTypeFactory().getContractsFromMethod();
        Set<Contract.Postcondition> postconditions = contractsUtils.getPostconditions(executableElement);

        StringToJavaExpression stringToJavaExpr = null;
        if (invocationNode instanceof MethodInvocationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    (MethodInvocationNode) invocationNode,
                                    analysis.getTypeFactory().getChecker());

            Node receiver = ((MethodInvocationNode) invocationNode).getTarget().getReceiver();
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse((MethodInvocationTree) invocationNode.getTree());

            if (executableElement.getKind().equals(ElementKind.CONSTRUCTOR)) {
                // For this() and super() calls, set receiver output type to constructor type
                AnnotatedTypeMirror receiverType = atypeFactory.getAnnotatedType(executableElement).getReturnType();
                if (receiverType != null) {
                    CFValue receiverDefaultValue = new CFValue(
                            analysis,
                            receiverType.getAnnotations(),
                            receiverType.getUnderlyingType());
                    store.replaceValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
                }
            } else {
                // For normal method calls, set receiver output type to input type by default.
                AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
                if (receiverType != null && !receiverType.getUnderlyingType().toString().equals("Array")) {
                    JavaExpression expr = JavaExpression.fromNode(receiver);
                    CFValue newVal = new CFValue(
                            analysis,
                            receiverType.getAnnotations(),
                            receiverType.getUnderlyingType());
                    if ((atypeFactory.isSideEffectFree(executableElement) || ((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(executableElement))
                            && TypeUtils.isStoreExpression(expr)) {
                        CFValue oldVal = store.getValue(expr);
                        if (oldVal == null) {
                            oldVal = new CFValue(
                                    analysis,
                                    AnnotationMirrorSet.singleton(((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).getInitialized()),
                                    receiverType.getUnderlyingType());
                        }

                        newVal = newVal.mostSpecific(oldVal, newVal);
                    }
                    store.replaceValue(expr, newVal);
                }
            }

            // Set parameter output types to input type by default.
            try {
                int i = 0;
                for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                    JavaExpression expr = JavaExpression.fromNode(TypeUtils.getArgumentWithVarargs((MethodInvocationNode) invocationNode, i++));
                    CFValue newVal = new CFValue(
                            analysis,
                            paramType.getAnnotations(),
                            paramType.getUnderlyingType());
                    if ((atypeFactory.isSideEffectFree(executableElement) || ((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(executableElement))
                            && TypeUtils.isStoreExpression(expr)) {
                        newVal = newVal.mostSpecific(store.getValue(expr), newVal);
                    }
                    store.replaceValue(expr, newVal);
                }
            } catch (IndexOutOfBoundsException e) {
                //TODO
                return;
            }
        } else if (invocationNode instanceof ObjectCreationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atConstructorInvocation(
                                    stringExpr, (NewClassTree) invocationTree, analysis.getTypeFactory().getChecker());

            // Set parameter output types to input type by default.
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().constructorFromUse((NewClassTree) invocationNode.getTree());
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                CFValue paramDefaultValue = new CFValue(
                        analysis,
                        paramType.getAnnotations(),
                        paramType.getUnderlyingType());
                JavaExpression expr = JavaExpression.fromNode(((ObjectCreationNode) invocationNode).getArgument(i++));
                CFValue oldValue = TypeUtils.isStoreExpression(expr) ? store.getValue(expr) : null;
                if (oldValue != null && AnnotationUtils.containsSameByClass(paramDefaultValue.getAnnotations(), UnknownInitialization.class)) {
                    // UnknownInit params cannot be (un-)packed
                    store.insertValue(
                            expr,
                            paramDefaultValue.mostSpecific(oldValue, paramDefaultValue));
                } else {
                    store.replaceValue(expr, paramDefaultValue);
                }
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

                if (je.toString().equals("this") && !atypeFactory.isInitialized(anno)) {
                    store.helperFunctionWasCalled();
                }

                // Unlike the superclass implementation, this calls
                // "insertValue" which for our type system replaces existing information instead of adding to it.
                // This is done because we use postconditions to implement output types for the parameters, which may
                // be incompatible with the input types. If a parameter has no explicit output type, we use its input
                // type as default, which is implemented above.
                CFValue value = analysis.createSingleAnnotationValue(anno, je.getType());
                if (atypeFactory.isSideEffectFree(executableElement) || ((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(executableElement)) {
                    value = value.mostSpecific(store.getValue(je), value);
                }
                if (p.kind == Contract.Kind.CONDITIONALPOSTCONDITION) {
                    // TODO
                } else {
                    store.insertValue(je, value);
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
