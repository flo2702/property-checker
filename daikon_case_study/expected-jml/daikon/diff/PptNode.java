package daikon.diff;

import daikon.PptTopLevel;

/**
 * Contains a pair of Ppts. Resides in the second level of the tree. All its children are InvNodes. 
 */
public class PptNode extends Node  {


    
    /**
     * Either ppt1 or ppt2 may be null, but not both.
     *
     * @param ppt1 a program point
     * @param ppt2 a program point
     */
        /*@ public normal_behavior
      @ requires (true) && (ppt2 != null || ppt1 != null);
      @ requires (true) && (ppt1 != null || ppt2 != null);
      @ requires_free this.packed == daikon.diff.PptNode;
      @ requires_free ppt1.packed == \typeof(ppt1);
      @ requires_free ppt2.packed == \typeof(ppt2);
      @ ensures (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free (true) && (this != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ PptNode(/*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2) {
        super(ppt1, ppt2);

    }

    /*@ public normal_behavior
      @ requires ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ requires_free !ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires_free !ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ daikon.diff.PptNode __INIT_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2, boolean ppt1_nullnessnode, boolean ppt2_nullnessnode) {
        return new daikon.diff.PptNode(ppt1, ppt2);
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
    public /*@nullable@*/ /*@helper@*/ PptTopLevel getPpt1() {
        //@ assume userObject.first instanceof PptTopLevel;
        return (PptTopLevel)__getUserLeft_trampoline(true, true);
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
    public  /*@nullable@*/ /*@helper@*/ daikon.PptTopLevel __getPpt1_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getPpt1();
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
    public /*@nullable@*/ /*@helper@*/ PptTopLevel getPpt2() {
        //@ assume userObject.second instanceof PptTopLevel;
        return (PptTopLevel)__getUserRight_trampoline(true, true);
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
    public  /*@nullable@*/ /*@helper@*/ daikon.PptTopLevel __getPpt2_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getPpt2();
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
