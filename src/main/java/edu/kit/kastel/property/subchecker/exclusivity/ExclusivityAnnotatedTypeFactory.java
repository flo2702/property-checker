package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import edu.kit.kastel.property.packing.PackingClientAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessTreeAnnotator;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ExclBottom;
import edu.kit.kastel.property.subchecker.exclusivity.qual.MaybeAliased;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import java.util.*;
import java.util.stream.Stream;

public final class ExclusivityAnnotatedTypeFactory
        extends PackingClientAnnotatedTypeFactory<ExclusivityValue, ExclusivityStore, ExclusivityTransfer, ExclusivityAnalysis> {

    public final AnnotationMirror EXCL_BOTTOM =
            AnnotationBuilder.fromClass(elements, ExclBottom.class);
    public final AnnotationMirror UNIQUE =
            AnnotationBuilder.fromClass(elements, Unique.class);
    public final AnnotationMirror READ_ONLY =
            AnnotationBuilder.fromClass(elements, ReadOnly.class);
    public final AnnotationMirror MAYBE_ALIASED =
            AnnotationBuilder.fromClass(elements, MaybeAliased.class);

    private @Nullable Tree useIFlowAfter;

    public ExclusivityAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    public AnnotationMirror getDefaultPrimitiveQualifier() {
        return UNIQUE;
    }

    @Override
    public AnnotationMirror getDefaultStringQualifier() {
        return MAYBE_ALIASED;
    }

    @Override
    public AnnotatedTypeMirror.AnnotatedNullType getAnnotatedNullType(Set<? extends AnnotationMirror> annotations) {
        AnnotatedTypeMirror.AnnotatedNullType result = super.getAnnotatedNullType(annotations);
        result.replaceAnnotation(getDefaultPrimitiveQualifier());
        return result;
    }

    @Override
    public ExclusivityTransfer createFlowTransferFunction(CFAbstractAnalysis<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> analysis) {
        return new ExclusivityTransfer((ExclusivityAnalysis) analysis, this);
    }

    public AnnotationMirror getExclusivityAnnotation(Collection<? extends AnnotationMirror> qualifiers) {
        for (AnnotationMirror qualifier : qualifiers) {
            if (AnnotationUtils.areSame(READ_ONLY, qualifier)
                    || AnnotationUtils.areSame(MAYBE_ALIASED, qualifier)
                    || AnnotationUtils.areSame(UNIQUE, qualifier)
                    || AnnotationUtils.areSame(EXCL_BOTTOM, qualifier)) {
                return qualifier;
            }
        }
        return null;
    }

    public void useIFlowAfter(@NonNull Tree useIFlowAfter) {
        this.useIFlowAfter = useIFlowAfter;
    }

    public void useRegularIFlow() {
        this.useIFlowAfter = null;
    }

    @Override
    public @Nullable ExclusivityValue getInferredValueFor(Tree tree) {
        if (useIFlowAfter != null) {
            Tree oldUseIFlowAfter = useIFlowAfter;
            // getStoreAfter needs to use the regular information flow
            useRegularIFlow();
            final ExclusivityStore store;
            if (oldUseIFlowAfter instanceof VariableTree) {
                ExclusivityStore s = null;
                Set<Node> nodes = flowResult.getNodesForTree(oldUseIFlowAfter);
                if (nodes != null) {
                    for (Node n : nodes) {
                        if (n instanceof AssignmentNode) {
                            s = flowResult.getStoreAfter(n);
                            break;
                        }
                    }
                }
                store = s;
            } else {
                store = flowResult.getStoreAfter(oldUseIFlowAfter);
            }
            Set<Node> nodes = flowResult.getNodesForTree(tree);
            useIFlowAfter(oldUseIFlowAfter);
            if (store == null || nodes == null) {
                return null;
            }

            return nodes.stream()
                    .map(node -> {
                        JavaExpression expr;
                        if (node instanceof ValueLiteralNode
                                || node instanceof BinaryOperationNode
                                || node instanceof UnaryOperationNode) {
                            return analysis.createAbstractValue(AnnotationMirrorSet.singleton(getDefaultPrimitiveQualifier()), node.getType());
                        } else if (node instanceof MethodInvocationNode) {
                            return store.getValue((MethodInvocationNode) node);
                        } else if (node instanceof FieldAccessNode) {
                            return store.getValue((FieldAccessNode) node);
                        } else if (node instanceof ArrayAccessNode) {
                            return store.getValue((ArrayAccessNode) node);
                        } else if (node instanceof LocalVariableNode) {
                            return store.getValue((LocalVariableNode) node);
                        } else if (node instanceof ThisNode) {
                            return store.getValue((ThisNode) node);
                        } else {
                            return null;  // No refined value available
                        }})
                    .filter(Objects::nonNull)
                    .reduce(ExclusivityValue::leastUpperBound)
                    .orElse(null);
        } else {
            return super.getInferredValueFor(tree);
        }
    }

    public AnnotationMirror getExclusivityAnnotation(AnnotatedTypeMirror annotatedTypeMirror) {
        return Objects.requireNonNullElse(annotatedTypeMirror.getAnnotationInHierarchy(READ_ONLY), MAYBE_ALIASED);
    }

    public AnnotationMirror getExclusivityAnnotation(Node node) {
        return getExclusivityAnnotation(getAnnotatedType(node.getTree()));
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(2);
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this, false));
        treeAnnotators.add(new ExclusivityPropagationTreeAnnotator(this));
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected ExclusivityViewpointAdapter createViewpointAdapter() {
        return new ExclusivityViewpointAdapter(this);
    }

    /**
     * Given a field access like `a.b.c.d`, determine the associated uniqueness type.
     *
     * @param exclType The uniqueness type of `a`, i.e. the root of the expression
     * @param expression The Java expression for which to determine the uniqueness type.
     *                   This is treated as a field access expression chain, whose root has the type {@code exclType}.
     * @return the viewpoint-adapted uniqueness type, or {@code exclType} if {@code expression} is not a field access.
     */
    @SuppressWarnings("unchecked")
    @Nullable
    public AnnotationMirror deriveExclusivityValue(AnnotatedTypeMirror exclType, JavaExpression expression) {
        var factory = ((ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory());
        // a.b, a.b.c, ..., expression (or empty if expression is not a field access)
        List<? extends JavaExpression> fieldPath = Stream.iterate(expression,
                        e -> e instanceof FieldAccess,
                        e -> ((FieldAccess) e).getReceiver())
                .toList()
                .reversed();

        if (fieldPath.isEmpty()) {
            // expression isn't a field access
            return factory.getExclusivityAnnotation(exclType);
        }

        // first component of field path. based on that, we derive the exclusivity type of the complete field access.=
        var adaptedExclType = AnnotatedTypeMirror.createType(exclType.getUnderlyingType(), factory, false);
        adaptedExclType.addAnnotations(exclType.getAnnotations());
        // fieldPath only contains FieldAccesses but can't be declared as List<FieldAccess> due to generics limitations
        //noinspection unchecked
        for (FieldAccess component : (List<FieldAccess>) fieldPath) {
            var field = component.getField();
            var declaredType = factory.getAnnotatedType(field);
            viewpointAdapter.viewpointAdaptMember(adaptedExclType, field, declaredType);
            adaptedExclType = declaredType;
        }

        return factory.getExclusivityAnnotation(adaptedExclType);
    }
}
