package edu.kit.kastel.property.subchecker.nullness;

import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.NullnessNoInitStore;
import org.checkerframework.checker.nullness.NullnessNoInitValue;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.util.Set;
import java.util.function.BinaryOperator;

public class NullnessLatticeStore extends NullnessNoInitStore {

    public NullnessLatticeStore(CFAbstractAnalysis<NullnessNoInitValue, NullnessNoInitStore, ?> analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    public NullnessLatticeStore(NullnessNoInitStore s) {
        super(s);
    }

    @SuppressWarnings("unchecked")
    NullnessLatticeAnnotatedTypeFactory getFactory() {
        return (NullnessLatticeAnnotatedTypeFactory) analysis.getTypeFactory();
    }

    @Override
    protected void computeNewValueAndInsert(JavaExpression expr, @Nullable NullnessNoInitValue value, BinaryOperator<NullnessNoInitValue> merger, boolean permitNondeterministic) {
        if (sequentialSemantics || !(expr instanceof FieldAccess)) {
            super.computeNewValueAndInsert(expr, value, merger, permitNondeterministic);
        } else {
            // Always use sequential semantics for field accesses if the receiver is Unique
            FieldAccess fieldAcc = (FieldAccess) expr;
            if (isCurrentReceiverUnique() || isMonotonicUpdate(fieldAcc, value) || fieldAcc.isUnassignableByOtherCode()) {
                NullnessNoInitValue oldValue = fieldValues.get(fieldAcc);
                NullnessNoInitValue newValue = merger.apply(oldValue, value);
                if (newValue != null) {
                    fieldValues.put(fieldAcc, newValue);
                }
            }
        }
    }

    protected void updateForFieldAccessAssignment(FieldAccess fieldAccess, @Nullable NullnessNoInitValue val) {
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
        ExclusivityStore exclStore = exclFactory.getStoreBefore(((NullnessLatticeAnalysis) analysis).getLocalTree());
        return exclStore != null && exclStore.getValue((ThisNode) null).getAnnotations().contains(exclFactory.UNIQUE);
    }

    @Override
    public void updateForMethodCall(MethodInvocationNode node, GenericAnnotatedTypeFactory<NullnessNoInitValue, NullnessNoInitStore, ?, ?> atypeFactory, NullnessNoInitValue val) {
        ExecutableElement method = node.getTarget().getMethod();
        if (((NullnessLatticeAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(method)) {
            super.updateForMethodCall(node, atypeFactory, val);
        } else {
            Node receiver = node.getTarget().getReceiver();
            TypeMirror receiverType = node.getTarget().getMethod().getReceiverType();
            ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
            AnnotationMirror receiverExclAnno = receiverType == null ? null : exclFactory.getExclusivityAnnotation(
                    receiverType.getAnnotationMirrors());

            // Clear field values if they were possibly changed
            boolean thisPassedAsArgument = receiverExclAnno != null &&
                    receiver instanceof ThisNode &&
                    exclFactory.getQualifierHierarchy().isSubtypeQualifiersOnly(receiverExclAnno, exclFactory.MAYBE_ALIASED);
            for (int i = 0; i < node.getArguments().size(); ++i) {
                Node arg = node.getArgument(i);
                AnnotationMirror argAnno = exclFactory.getExclusivityAnnotation(
                        node.getTarget().getMethod().getParameters().get(i).asType().getAnnotationMirrors());
                if (arg instanceof ThisNode && exclFactory.getQualifierHierarchy()
                        .isSubtypeQualifiersOnly(argAnno, exclFactory.MAYBE_ALIASED)) {
                    thisPassedAsArgument = true;
                    break;
                }
            }

            if (!atypeFactory.isSideEffectFree(node.getTarget().getMethod())
                    && !((NullnessLatticeAnnotatedTypeFactory) atypeFactory).isMonotonicMethod(node.getTarget().getMethod())
                    && thisPassedAsArgument) {
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                CFValue receiverOutputPackingValue = packingFactory.getStoreAfter(node).getValue((ThisNode) null);
                AnnotatedTypeMirror receiverOutputPackingType = AnnotatedTypeMirror.createType(receiverType, packingFactory, false);
                if (receiverOutputPackingValue != null) {
                    receiverOutputPackingType.addAnnotations(receiverOutputPackingValue.getAnnotations());
                }

                AnnotatedTypeMirror receiverInputPackingType = packingFactory.getReceiverType(node.getTree());

                for (FieldAccess field : Set.copyOf(getFieldValues().keySet())) {
                    TypeMirror fieldOwnerType = field.getField().getEnclosingElement().asType();

                    // Don't clear fields in frame of UnknownInit input type
                    if (receiverInputPackingType.hasAnnotation(UnknownInitialization.class) &&
                            packingFactory.isInitializedForFrame(receiverInputPackingType, fieldOwnerType)) {
                        continue;
                    }

                    // For remaining fields in frame of output type, add declared type to store
                    if (receiverOutputPackingValue != null &&
                            packingFactory.isInitializedForFrame(receiverOutputPackingType, fieldOwnerType)) {
                        AnnotatedTypeMirror adaptedType = atypeFactory.getAnnotatedType(field.getField());
                        replaceValue(
                                field,
                                new NullnessNoInitValue(analysis,
                                        adaptedType.getAnnotations(),
                                        adaptedType.getUnderlyingType()));
                        continue;
                    }

                    // For remaining params, clear value
                    clearValue(field);
                    //System.out.printf("Clearing refinement for %s after %s\n", field, node);
                }
            }
        }
    }
}
