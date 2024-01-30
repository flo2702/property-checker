package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.QualifierHierarchy;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;

abstract class AbstractTypeRule<N extends Node> implements TypeRule {

    /*
     * If store is null, type rule shall just check for applicability without actually refining types.
     */
    protected final @Nullable ExclusivityStore store;
    protected final QualifierHierarchy hierarchy;
    protected final ExclusivityAnnotatedTypeFactory factory;
    protected @Nullable ExclusivityAnalysis analysis;

    public AbstractTypeRule(@Nullable ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory,
                            ExclusivityAnalysis analysis) {
        this.store = store;
        this.analysis = analysis;
        this.hierarchy = factory.getQualifierHierarchy();
        this.factory = factory;
    }

    @Override
    public final void apply(Node abstractNode) throws RuleNotApplicable {
        N node;
        try {
            @SuppressWarnings("unchecked")
            N concreteNode = (N) abstractNode;
            node = concreteNode;
        } catch (ClassCastException e) {
            throw new RuleNotApplicable(getName(), abstractNode, "wrong node type");
        }
        applyInternal(node);
        if (getName() != null) {
            System.out.println("Applied " + getName());
        }
    }

    protected abstract void applyInternal(N node) throws RuleNotApplicable;

    /**
     * Update type of node in store to newRefinedType, ensuring that newRefinedType
     * is a subtype of node's declared type.
     *
     * @param node        The node whose type is to be updated
     * @param refinedType The new, refined type of node
     * @throws RuleNotApplicable if the refinement would violate the declaration
     */
    protected final void updateType(
            Node node, AnnotationMirror refinedType
    ) throws RuleNotApplicable {
        updateType(node, refinedType, true);
    }

    /**
     * Update type of node in store to newRefinedType.
     *
     * @param node        The node whose type is to be updated
     * @param refinedType The new, refined type of node
     * @param checkValidity Whether to check that newRefinedType is a subtype of node's declared type
     * @throws RuleNotApplicable if the refinement would violate the declaration
     */
    protected final void updateType(
            Node node, AnnotationMirror refinedType, boolean checkValidity
    ) throws RuleNotApplicable {
        // Cannot update the type of a non-lhs expression in the store,
        // so we just check if the old type fits.
        if (!isLhs(node)) {
            if (AnnotationUtils.areSame(getRefinedTypeAnnotation(node), refinedType)) {
                return;
            } else {
                throw new RuleNotApplicable(
                        getName(), getRefinedTypeAnnotation(node), "refinement violates non-lhs expression type");
            }
        }

        if (checkValidity) {
            canUpdateType(getDeclaredTypeAnnotation(node), refinedType);
        }

        if (store != null && analysis != null) {
            ExclusivityValue abstractValue = analysis.createAbstractValue(
                AnnotationMirrorSet.singleton(refinedType), node.getType());
            store.replaceValue(JavaExpression.fromNode(node),
                    abstractValue);
        }
    }

    protected final boolean isLhs(Node node) {
        switch (node.getTree().getKind()) {
            case VARIABLE:
            case IDENTIFIER:
            case MEMBER_SELECT:
            case ARRAY_ACCESS:
            case PARENTHESIZED:
                return true;
            default:
                return TreeUtils.isTypeTree(node.getTree());
        }
    }

    protected final void canUpdateType(AnnotationMirror declTypeAnno, AnnotationMirror refinedType)
            throws RuleNotApplicable {
        if (!isValidRefinement(declTypeAnno, refinedType)) {
            throw new RuleNotApplicable(getName(), declTypeAnno, "refinement violates declaration");
        }
    }

    protected final boolean isValidRefinement(AnnotationMirror declaredType, AnnotationMirror refinedType) {
        assert declaredType != null;
        return hierarchy.isSubtypeQualifiersOnly(refinedType, declaredType);
    }

    private AnnotationMirror getDeclaredTypeAnnotation(Node node) {
        return factory.getExclusivityAnnotation(
                // TODO Do we need to get declared types for nodes not supported by getAnnotatedTypeLhs?
                factory.getAnnotatedTypeLhs(node.getTree()).getAnnotations());
    }

    protected final AnnotationMirror getRefinedTypeAnnotation(Node node) {
        AnnotationMirror oldAnno;
        if (node instanceof ImplicitThisNode) {
            //TODO
            assert false;
            oldAnno = null;
        } else if (node instanceof ValueLiteralNode) {
            return factory.MAYBE_ALIASED;
        } else {
            ExclusivityValue value = null;
            if (node instanceof FieldAccessNode) {
                value = store.getValue((FieldAccessNode) node);
            } else if (node instanceof LocalVariableNode) {
                value = store.getValue((LocalVariableNode) node);
            }

            if (value != null) {
                oldAnno = factory.getExclusivityAnnotation(value.getAnnotations());
            } else {
                oldAnno = factory.getExclusivityAnnotation(factory.getAnnotatedType(node.getTree()).getAnnotations());
            }
        }
        assert oldAnno != null;
        return oldAnno;
    }

    protected final String prettyPrint(@Nullable AnnotationMirror anno) {
        // TODO: There has to be a better way to do this
        String pkgName = "edu.kit.kastel.property.subchecker.exclusivity.qual.";
        StringBuilder s = new StringBuilder(anno != null ? anno.toString() : "");
        s.delete(s.indexOf(pkgName), s.indexOf(pkgName) + pkgName.length());
        return s.toString();
    }
}
