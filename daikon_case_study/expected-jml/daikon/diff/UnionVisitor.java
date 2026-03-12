package daikon.diff;

import daikon.PptTopLevel;
import daikon.inv.Invariant;

/**
 * Computes A union B, where A and B are the two sets of invariants. 
 */
public class UnionVisitor extends DepthFirstVisitor  {

    //@ public invariant_free packed <: daikon.diff.UnionVisitor ==> result.packed == \typeof(result);
    //@ public invariant_free \invariant_free_for(result);
    //@ public invariant_free packed <: daikon.diff.UnionVisitor ==> currentPpt.packed == \typeof(currentPpt);
    //@ public invariant_free \invariant_free_for(currentPpt);
    //@ public invariant_free packed <: daikon.diff.UnionVisitor ==> ((true) && (result != null));

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.UnionVisitor;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ UnionVisitor() {
        super();
        result = InvMap.__INIT_trampoline();


    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.UnionVisitor __INIT_trampoline() {
        return new daikon.diff.UnionVisitor();
    }

    public /*@nullable@*/ daikon.diff.InvMap result;

    public /*@nullable@*/ daikon.PptTopLevel currentPpt;

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ InvMap getResult() {
        return result;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.InvMap __getResult_trampoline(boolean this_nullness) {
        return getResult();
    }

    
    /**
     * Every node has at least one non-null ppt. Add one of the non-null ppt to the result. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (node != null);
      @ requires (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free node.packed == \typeof(node);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.PptNode node) {
        daikon.PptTopLevel ppt1;
        daikon.PptTopLevel temp0 = node.__getPpt1_trampoline(true, true);
        ppt1 = temp0;
        daikon.PptTopLevel ppt2;
        daikon.PptTopLevel temp1 = node.__getPpt2_trampoline(true, true);
        ppt2 = temp1;
        daikon.PptTopLevel pptNonNull;
        daikon.PptTopLevel temp2 = (ppt1 != null ? ppt1 : ppt2);
        //@ assert (true) && (temp2 != null);
        pptNonNull = temp2;
        result.__addPpt_trampoline(pptNonNull, true, true);
        daikon.PptTopLevel temp3 = pptNonNull;
        currentPpt = temp3;
        super.__visit_trampoline(node, true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires node_nullness || ((true) && (node != null));
      @ requires node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !node_nullness || ((true) && (node != null));
      @ requires_free !node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @*/
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.PptNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
    }

    
    /**
     * If only one invariant is non-null, always add it. If two invariants are non-null, add the
     * invariant with the better (higher) confidence.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (node != null);
      @ requires (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ requires this.currentPpt != null;
      @ requires_free this.packed == \typeof(this);
      @ requires_free node.packed == \typeof(node);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.InvNode node) {
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp4 = node.__getInv1_trampoline(true, true);
        inv1 = temp4;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp5 = node.__getInv2_trampoline(true, true);
        inv2 = temp5;
        if (inv1 == null) {
            result.__add_trampoline(currentPpt, inv2, true, true, false);
        } else if (inv2 == null) {
            result.__add_trampoline(currentPpt, inv1, true, true, true);
        } else {
            if (inv1.getConfidence() >= inv2.getConfidence()) {
                result.__add_trampoline(currentPpt, inv1, true, true, true);
            } else {
                result.__add_trampoline(currentPpt, inv2, true, true, true);
            }
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires node_nullness || ((true) && (node != null));
      @ requires node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ requires this.currentPpt != null;
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !node_nullness || ((true) && (node != null));
      @ requires_free !node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @*/
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.InvNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
    }

}
