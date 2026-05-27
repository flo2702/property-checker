package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.util.stream.Stream;

public class PackingStore extends InitializationAbstractStore<CFValue, PackingStore> {

    private boolean helperFunctionCalled = false;
    private boolean dependableFieldAssigned = false;

    public PackingStore(PackingAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    public PackingStore(PackingStore other) {
        super(other);
    }

    @Override
    public void insertValue(
            JavaExpression expr, @Nullable CFValue value, boolean permitNondeterministic) {
        if (!shouldInsert(expr, value, permitNondeterministic)) {
            return;
        }

        computeNewValueAndInsert(
                expr,
                value,
                (old, newValue) -> newValue,
                permitNondeterministic);

        if (expr instanceof FieldAccess) {
            FieldAccess fa = (FieldAccess) expr;
            if (fa.getReceiver() instanceof ThisReference
                    || fa.getReceiver() instanceof ClassName) {
                addInitializedField(fa.getField());
            }
        }
    }

    @Override
    public @Nullable CFValue getValue(JavaExpression expr) {
        if (expr instanceof ThisReference || (expr instanceof LocalVariable && expr.toString().equals("this"))) {
            return thisValue;
        }
        return super.getValue(expr);
    }

    @Override
    public void clearValue(JavaExpression expr) {
        if (expr instanceof ThisReference) {
            thisValue = null;
        } else {
            super.clearValue(expr);
        }
    }

    @Override
    public boolean isFieldInitialized(Element f) {
        // We don't use the fbc commitment mechanism.
        return false;
    }

    public boolean isFieldAssigned(Element f) {
        return super.isFieldInitialized(f);
    }

    @Override
    public void updateForMethodCall(
            MethodInvocationNode methodInvocationNode,
            GenericAnnotatedTypeFactory<CFValue, PackingStore, ?, ?> atypeFactory,
            CFValue val) {
        ExecutableElement method = methodInvocationNode.getTarget().getMethod();

        if (((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(method)) {
            // store information about method call if possible, but don't change the store otherwise
            JavaExpression methodCall = JavaExpression.fromNode(methodInvocationNode);
            replaceValue(methodCall, val);
        } else {
            updateForNonMonotonicMethodCall(methodInvocationNode, atypeFactory, val);
        }
    }

    private void updateForNonMonotonicMethodCall(
            MethodInvocationNode node,
            GenericAnnotatedTypeFactory<CFValue, PackingStore, ?, ?> atypeFactory,
            CFValue val
    ) {
        super.updateForMethodCall(node, atypeFactory, val);

        MethodCall invocation = (MethodCall) JavaExpression.fromNode(node);
        ExecutableElement method = invocation.getElement();

        if (atypeFactory.isSideEffectFree(method) && atypeFactory.isDeterministic(method)) {
            // insert return value into store if method is pure and not a constructor call (like this(...) or super(...))
            if (method.getKind() != ElementKind.CONSTRUCTOR || invocation.getReceiver() instanceof ClassName) {
                insertValue(invocation, val);
            }
            return;
        }

        // If `this` was passed to the method call, we first clear all field values, then restore some field values
        // based on the method signature.
        boolean thisPassed = Stream.concat(Stream.of(invocation.getReceiver()), invocation.getArguments().stream())
                .anyMatch(v -> v instanceof ThisReference);
        if (!thisPassed) {
            return;
        }
        fieldValues.clear();

        PackingFieldAccessAnnotatedTypeFactory packingFactory = (PackingFieldAccessAnnotatedTypeFactory) atypeFactory;
        CFValue outputPackingValue = getValue((ThisNode) null);

        if (outputPackingValue != null) {
            TypeMirror thisType = outputPackingValue.getUnderlyingType();
            AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(thisType, packingFactory, false);
            outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
            var packingAnno = outputPackingType.getAnnotationInHierarchy(packingFactory.getUnknownInitialization());

            TypeMirror frame;
            if (packingFactory.isInitialized(packingAnno)) {
                frame = thisType;
            } else {
                frame = packingFactory.getTypeFrameFromAnnotation(packingAnno);
            }

            var initializedFields = ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), packingFactory.getElementUtils());
            for (var field : initializedFields) {
                AnnotatedTypeMirror adaptedType = analysis.getTypeFactory().getAnnotatedType(field);
                insertValue(new FieldAccess(new ThisReference(thisType), field), analysis.createAbstractValue(adaptedType));
            }
        }
    }

    /**
     * Whether a helper function, i.e., a function that may leave the receiver not @Initialized was called on {@code this}.
     *
     * @return whether a helper function was called on {@code this}
     */
    public boolean isHelperFunctionCalled() {
        return helperFunctionCalled;
    }

    public void helperFunctionWasCalled() {
        this.helperFunctionCalled = true;
    }

    public boolean isDependableFieldAssigned() {
        return dependableFieldAssigned;
    }

    public void setDependableFieldAssigned(boolean dependableFieldAssigned) {
        this.dependableFieldAssigned = dependableFieldAssigned;
    }
}
