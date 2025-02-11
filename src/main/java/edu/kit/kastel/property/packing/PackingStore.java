package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;

public class PackingStore extends InitializationAbstractStore<CFValue, PackingStore> {

    private boolean helperFunctionCalled = false;

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
    public void updateForMethodCall(MethodInvocationNode methodInvocationNode, GenericAnnotatedTypeFactory<CFValue, PackingStore, ?, ?> atypeFactory, CFValue val) {
        ExecutableElement method = methodInvocationNode.getTarget().getMethod();

        if (((PackingFieldAccessAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(method)) {
            // store information about method call if possible, but don't change the store otherwise
            JavaExpression methodCall = JavaExpression.fromNode(methodInvocationNode);
            replaceValue(methodCall, val);
        } else {
            // change the store normally
            super.updateForMethodCall(methodInvocationNode, atypeFactory, val);
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

    public void setHelperFunctionCalled(boolean helperFunctionCalled) {
        this.helperFunctionCalled = helperFunctionCalled;
    }
}
