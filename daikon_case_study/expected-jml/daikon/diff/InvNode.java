package daikon.diff;

import daikon.inv.Invariant;

/**
 * Contains a pair of Invariants. Resides in the third level of the tree. Has no children. 
 */
public class InvNode extends Node  {


    
    /**
     * Either inv1 or inv2 may be null, but not both.
     *
     * @param inv1 an invariant
     * @param inv2 an invariant
     */
        /*@ public normal_behavior
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free this.packed == daikon.diff.InvNode;
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (this != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ InvNode(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        super(inv1, inv2);

    }

    /*@ public normal_behavior
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ daikon.diff.InvNode __INIT_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        return new daikon.diff.InvNode(inv1, inv2);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures (true) && (this.userObject.second != null || \result != null);
      @ ensures \result == userObject.first;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ Invariant getInv1() {
        //@ assume userObject.first instanceof Invariant;
        return (Invariant)__getUserLeft_trampoline(true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures \result == userObject.first;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.second != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.inv.Invariant __getInv1_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getInv1();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures (true) && (this.userObject.first != null || \result != null);
      @ ensures \result == userObject.second;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ Invariant getInv2() {
        //@ assume userObject.second instanceof Invariant;
        return (Invariant)__getUserRight_trampoline(true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures \result == userObject.second;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.first != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.inv.Invariant __getInv2_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getInv2();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (v != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free v.packed == \typeof(v);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free v.packed == \typeof(v);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void accept(/*@nullable@*/ daikon.diff.Visitor v) {
        v.__visit_trampoline(this, true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires v_nullness || ((true) && (v != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !v_nullness || ((true) && (v != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free v.packed == \typeof(v);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @*/
    public  /*@helper@*/ void __accept_trampoline(/*@nullable@*/ daikon.diff.Visitor v, boolean this_nullness, boolean v_nullness, boolean this_nullnessnode) {
        accept(v);
    }

}
