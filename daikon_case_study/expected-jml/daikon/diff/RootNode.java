package daikon.diff;


/**
 * The root of the tree. All its children are PptNodes. 
 */
public class RootNode extends Node  {


    
    /**
     * Creates a new RootNode object. 
     */
        /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.RootNode;
      @ ensures_free (true) && (this != null);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ RootNode() {
        super(null, null);

    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ daikon.diff.RootNode __INIT_trampoline() {
        return new daikon.diff.RootNode();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ IPair getUserObject() {
        throw new Error("Shouldn\'t ask for userObject for RootNode");
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.IPair __getUserObject_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserObject();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.second != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ Void getUserLeft() {
        throw new Error("Shouldn\'t ask for userObject for RootNode");
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.second != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.Void __getUserLeft_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserLeft();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.first != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ Void getUserRight() {
        throw new Error("Shouldn\'t ask for userObject for RootNode");
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (this.userObject.first != null || \result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.Void __getUserRight_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserRight();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newChild != null);
      @ requires (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free newChild.packed == \typeof(newChild);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newChild.packed == \typeof(newChild);
      @ ensures_free (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void add(/*@nullable@*/ daikon.diff.PptNode newChild) {
        super.__add_trampoline(newChild, true, true, false, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newChild_nullness || ((true) && (newChild != null));
      @ requires newChild_nullnessnode || ((true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newChild_nullness || ((true) && (newChild != null));
      @ requires_free !newChild_nullnessnode || ((true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newChild.packed == \typeof(newChild);
      @ ensures_free (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @*/
    public  /*@helper@*/ void __add_trampoline(/*@nullable@*/ daikon.diff.PptNode newChild, boolean this_nullness, boolean newChild_nullness, boolean newChild_nullnessnode) {
        add(newChild);
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
