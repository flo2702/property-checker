package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import edu.kit.kastel.property.subchecker.exclusivity.rules.*;

import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

public class ExclusivityTransfer extends PackingClientTransfer<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> {

    private final ExclusivityAnnotatedTypeFactory factory;

    public ExclusivityTransfer(ExclusivityAnalysis analysis,
                               ExclusivityAnnotatedTypeFactory factory) {
        super(analysis);
        assert factory == analysis.getTypeFactory();
        this.factory = factory;
    }

    public ExclusivityAnalysis getAnalysis() {
        return (ExclusivityAnalysis) analysis;
    }

    @Override
    protected ExclusivityValue initialThisValue(MethodTree methodDeclTree) {
        if (!TreeUtils.isConstructor(methodDeclTree)) {
            AnnotatedTypeMirror thisType = factory.getAnnotatedType(methodDeclTree.getReceiverParameter());
            return analysis.createSingleAnnotationValue(
                    thisType.getAnnotationInHierarchy(
                            AnnotationBuilder.fromClass(factory.getElementUtils(), Unique.class)),
                    thisType.getUnderlyingType());
        } else {
            AnnotatedTypeMirror thisType = factory.getSelfType(methodDeclTree.getBody());
            return analysis.createSingleAnnotationValue(
                    factory.UNIQUE,
                    thisType.getUnderlyingType());
        }
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitAssignment(
            AssignmentNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        if (node.getExpression() instanceof MethodInvocationNode) {
            new TMethodInvocationHelper(store, factory, getAnalysis())
                    .applyOrInvalidate(node.getTarget(), node.getExpression());
        } else {
            new TAssign(store, factory, getAnalysis()).applyOrInvalidate(node.getTarget(), node.getExpression());
        }

        return new RegularTransferResult<>(null, in.getRegularStore());
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<ExclusivityValue, ExclusivityStore> in
    ) {
        ExclusivityStore store = in.getRegularStore();
        ExpressionTree invocationTree = n.getTree();
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        JavaExpression receiverExpr = JavaExpression.fromNode(receiver);

        ExclusivityValue oldReceiverValue = null;
        if (CFAbstractStore.canInsertJavaExpression(receiverExpr)) {
            oldReceiverValue = store.getValue(receiverExpr);
        }

        if (receiver instanceof ClassNameNode && ((ClassNameNode) receiver).getElement().toString().equals(Packing.class.getName())) {
            // Packing statements don't change the store
            return new RegularTransferResult<>(null, store, false);
        }

        try {
            new TMethodInvocation(store, factory, getAnalysis()).apply(n);
        } catch (RuleNotApplicable e) {
            new TInvalidate(store, factory, getAnalysis()).apply(n);
        }

        processPostconditions(n, store, method, invocationTree);

        // Set receiver type to old type if input type is @ReadOnly.
        // This is independent of the output type since any typing @ReadOnly -> @T where @T != @ReadOnly is necessarily ill-typed
        AnnotatedTypeFactory.ParameterizedExecutableType methodType =
                analysis.getTypeFactory().methodFromUse((MethodInvocationTree) n.getTree());
        AnnotatedTypeMirror receiverType = methodType.executableType.getReceiverType();
        if (oldReceiverValue != null && receiverType != null && receiverType.hasAnnotation(ReadOnly.class)) {
            store.insertOrRefine(receiverExpr, factory.getExclusivityAnnotation(oldReceiverValue.getAnnotations()));
        }

        return new RegularTransferResult<>(null, store, true);
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitReturn(
            ReturnNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        MethodTree methodTree = (MethodTree) factory.getEnclosingClassOrMethod(node.getTree());
        assert methodTree != null;
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(
                factory.getAnnotatedType(methodTree).getReturnType());

        new TAssign(store, factory, getAnalysis()).applyOrInvalidate(returnTypeAnno, node.getResult());

        return new RegularTransferResult<>(null, store);
    }

    //TODO handle constructors
}
