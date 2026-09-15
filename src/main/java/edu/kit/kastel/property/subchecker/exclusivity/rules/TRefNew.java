package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.cfg.node.ArrayCreationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TRefNew extends AssignmentRule {

    public TRefNew(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    public String getName() {
        return "U-Ref-New";
    }

    @Override
    public void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        checkRhsNode(rhsNode);
        try {
            updateType(lhsNode, factory.UNIQUE);
        } catch (RuleNotApplicable e) {
            // While a constructor result can be refined to ExclMut,
            // a constructor can also be made to return any other type.
            // So if the lhs is incompatible with ExclMut, we leave it as is.
        }
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        checkRhsNode(rhsNode);
        try {
            canUpdateType(lhsType, factory.UNIQUE);
        } catch (RuleNotApplicable e) {
            // While a constructor result can be refined to Unique,
            // a constructor can also be made to return any other type.
            // So if the lhs is incompatible with Unique, we leave it as is.
        }
    }

    private void checkRhsNode(Node rhsNode) throws RuleNotApplicable {
        if (!(rhsNode instanceof ObjectCreationNode) && !(rhsNode instanceof ArrayCreationNode)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs node is no object creation");
        }
    }
}
