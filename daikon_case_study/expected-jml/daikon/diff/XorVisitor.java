package daikon.diff;

import daikon.PptTopLevel;
import daikon.inv.Invariant;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Computes A xor B, where A and B are the two sets of invariants. 
 */
public class XorVisitor extends DepthFirstVisitor  {
    static {
        java.util.logging.Logger temp0 = Logger.getLogger("daikon.diff.XorVisitor");
        //@ assume (true) && (temp0 != null);
        debug = temp0;

    }


    //@ public invariant_free packed <: daikon.diff.XorVisitor ==> result.packed == \typeof(result);
    //@ public invariant_free \invariant_free_for(result);
    //@ public invariant_free packed <: daikon.diff.XorVisitor ==> currentPpt.packed == \typeof(currentPpt);
    //@ public invariant_free \invariant_free_for(currentPpt);
    //@ public static invariant_free (true) && (daikon.diff.XorVisitor.debug != null);
    //@ public invariant_free packed <: daikon.diff.XorVisitor ==> ((true) && (result != null));

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.XorVisitor;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ XorVisitor() {
        super();
        result = InvMap.__INIT_trampoline();


    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.XorVisitor __INIT_trampoline() {
        return new daikon.diff.XorVisitor();
    }

    public /*@nullable@*/ daikon.diff.InvMap result;

    public /*@nullable@*/ daikon.PptTopLevel currentPpt;

    public static /*@nullable@*/ java.util.logging.Logger debug;

    
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
        daikon.PptTopLevel temp1 = node.__getPpt1_trampoline(true, true);
        ppt1 = temp1;
        daikon.PptTopLevel ppt2;
        daikon.PptTopLevel temp2 = node.__getPpt2_trampoline(true, true);
        ppt2 = temp2;
        daikon.PptTopLevel pptNonNull;
        daikon.PptTopLevel temp3 = (ppt1 != null ? ppt1 : ppt2);
        //@ assert (true) && (temp3 != null);
        pptNonNull = temp3;
        result.__addPpt_trampoline(pptNonNull, true, true);
        daikon.PptTopLevel temp4 = pptNonNull;
        currentPpt = temp4;
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
     * If one invariant is null and the other is not, add the non-null invariant to the result set.
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
        daikon.inv.Invariant temp5 = node.__getInv1_trampoline(true, true);
        inv1 = temp5;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp6 = node.__getInv2_trampoline(true, true);
        inv2 = temp6;
        if (debug.isLoggable(Level.FINE)) {
            debug.fine("visit: " + ((inv1 != null) ? inv1.ppt.parent.name() : "NULL") + " " + ((inv1 != null) ? inv1.repr() : "NULL") + " - " + ((inv2 != null) ? inv2.repr() : "NULL"));
        }
        if (shouldAddInv1(inv1, inv2)) {
            assert inv1 != null;
            result.__add_trampoline(currentPpt, inv1, true, true, true);
        } else if (shouldAddInv2(inv1, inv2)) {
            assert inv2 != null;
            result.__add_trampoline(currentPpt, inv2, true, true, true);
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

    
    /*@ private normal_behavior
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv1 != null;
      @*/
    private static /*@helper@*/ boolean shouldAddInv1(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return (inv1 != null) && (inv2 == null);
    }

    /*@ public normal_behavior
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv1 != null;
      @*/
    public static /*@helper@*/ boolean __shouldAddInv1_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return shouldAddInv1(inv1, inv2);
    }

    
    /*@ private normal_behavior
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv2 != null;
      @*/
    private static /*@helper@*/ boolean shouldAddInv2(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return (inv2 != null) && (inv1 == null);
    }

    /*@ public normal_behavior
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv2 != null;
      @*/
    public static /*@helper@*/ boolean __shouldAddInv2_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return shouldAddInv2(inv1, inv2);
    }

    
    /**
     * Returns the InvMap generated as a result of the traversal. 
     */
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

}
