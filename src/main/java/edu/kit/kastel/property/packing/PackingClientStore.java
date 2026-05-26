package edu.kit.kastel.property.packing;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;

import java.util.function.BinaryOperator;

public abstract class PackingClientStore<V extends PackingClientValue<V>, S extends PackingClientStore<V, S>>
        extends CFAbstractStore<V, S> {

    protected PackingClientStore(CFAbstractAnalysis<V, S, ?> analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    protected PackingClientStore(CFAbstractStore<V, S> other) {
        super(other);
    }

    @Override
    public void insertValue(
            JavaExpression expr, @Nullable V value, boolean permitNondeterministic) {
        if (!shouldInsert(expr, value, permitNondeterministic)) {
            return;
        }

        computeNewValueAndInsert(
                expr,
                value,
                (old, newValue) -> newValue,
                permitNondeterministic);
    }

    @Override
    protected void computeNewValueAndInsert(JavaExpression expr, @Nullable V value, BinaryOperator<V> merger, boolean permitNondeterministic) {
        if (sequentialSemantics || !(expr instanceof FieldAccess)) {
            super.computeNewValueAndInsert(expr, value, merger, permitNondeterministic);
        } else {
            // Always use sequential semantics for field accesses if the receiver is Unique
            FieldAccess fieldAcc = (FieldAccess) expr;
            if (isCurrentReceiverUnique() || isMonotonicUpdate(fieldAcc, value) || fieldAcc.isUnassignableByOtherCode()) {
                V oldValue = fieldValues.get(fieldAcc);
                V newValue = merger.apply(oldValue, value);
                if (newValue != null) {
                    fieldValues.put(fieldAcc, newValue);
                }
            }
        }
    }

    protected void updateForFieldAccessAssignment(FieldAccess fieldAccess, @Nullable V val) {
        removeConflicting(fieldAccess, val);
        if (!fieldAccess.containsUnknown() && val != null) {
            // Always use sequential semantics for field accesses if the receiver is Unique
            if (sequentialSemantics || isCurrentReceiverUnique()
                    || isMonotonicUpdate(fieldAccess, val)
                    || fieldAccess.isUnassignableByOtherCode()) {
                fieldValues.put(fieldAccess, val);
            }
        }
    }

    protected boolean isCurrentReceiverUnique() {
        ExclusivityAnnotatedTypeFactory exclFactory = getFactory().getPackingChecker().getTypeFactoryOfSubcheckerOrNull(ExclusivityChecker.class);
        ExclusivityStore exclStore = exclFactory.getStoreBefore(((PackingClientAnalysis) analysis).getLocalTree());
        return exclStore != null && exclStore.thisValue.getAnnotations().contains(exclFactory.UNIQUE);
    }

    @SuppressWarnings("unchecked")
    PackingClientAnnotatedTypeFactory<?,?,?,?> getFactory() {
        return (PackingClientAnnotatedTypeFactory<?,?,?,?>) analysis.getTypeFactory();
    }

    @Override
    public @Nullable V getValue(JavaExpression expr) {
        if (expr instanceof ThisReference || (expr instanceof LocalVariable && expr.toString().equals("this"))) {
            return thisValue;
        }
        return super.getValue(expr);
    }

    protected void initializeThisValue(V value) {
        thisValue = value;
    }

    @Override
    public void clearValue(JavaExpression expr) {
        if (expr instanceof ThisReference) {
            thisValue = null;
        } else {
            super.clearValue(expr);
        }
    }
}
