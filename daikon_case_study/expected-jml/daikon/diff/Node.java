package daikon.diff;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * All nodes must subclass this class.
 *
 * @param <CONTENT> half of the type of the objects stored in this node, which are {@code
 *     IPair<CONTENT,CONTENT>}
 * @param <CHILD> the type of the children; it is is ignored if there are no children
 */
public abstract class Node  {

    //@ public invariant_free packed <: daikon.diff.Node ==> children.packed == \typeof(children);
    //@ public invariant_free \invariant_free_for(children);
    //@ public invariant_free packed <: daikon.diff.Node ==> userObject.packed == \typeof(userObject);
    //@ public invariant_free \invariant_free_for(userObject);
    //@ public invariant_free packed <: daikon.diff.Node ==> ((true) && (children != null));
    //@ public invariant_free packed <: daikon.diff.Node ==> ((true) && (userObject != null));

    public /*@nullable@*/ java.util.List children;

    public /*@nullable@*/ daikon.diff.IPair userObject;

    
    /*@ protected normal_behavior
      @ requires (true) && (right != null || left != null);
      @ requires (true) && (left != null || right != null);
      @ requires_free this.packed == daikon.diff.Node;
      @ requires_free left.packed == \typeof(left);
      @ requires_free right.packed == \typeof(right);
      @ ensures (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free left.packed == \typeof(left);
      @ ensures_free right.packed == \typeof(right);
      @ ensures_free (true) && (this != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free (true) && (right != null || left != null);
      @ ensures_free (true) && (left != null || right != null);
      @ assignable \nothing;
      @*/
    protected /*@helper@*/ Node(/*@nullable@*/ Object left, /*@nullable@*/ Object right) {
        super();
        children = new ArrayList();


        this.userObject = IPair.of(left, right);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newChild != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free newChild.packed == \typeof(newChild);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newChild.packed == \typeof(newChild);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void add(/*@nullable@*/ Object newChild) {
        children.add(newChild);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newChild_nullness || ((true) && (newChild != null));
      @ requires this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires newChild_nullnessnode || ((true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newChild_nullness || ((true) && (newChild != null));
      @ requires_free !this_nullnessnode || ((true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null)));
      @ requires_free !newChild_nullnessnode || ((true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newChild.packed == \typeof(newChild);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free (true) && (newChild instanceof Void || newChild instanceof daikon.diff.Node && ((daikon.diff.Node)newChild).userObject != null && (((daikon.diff.Node)newChild).userObject.first != null || ((daikon.diff.Node)newChild).userObject.second != null));
      @*/
    public  /*@helper@*/ void __add_trampoline(/*@nullable@*/ Object newChild, boolean this_nullness, boolean newChild_nullness, boolean this_nullnessnode, boolean newChild_nullnessnode) {
        add(newChild);
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
      @*/
    public /*@nullable@*/ /*@helper@*/ Iterator children() {
        return children.iterator();
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
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.util.Iterator __children_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return children();
    }

    
    /**
     * Returns the user object pair.
     *
     * @return the user object pair
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (this instanceof Void || this instanceof daikon.diff.Node && ((daikon.diff.Node)this).userObject != null && (((daikon.diff.Node)this).userObject.first != null || ((daikon.diff.Node)this).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ IPair getUserObject() {
        return userObject;
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
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.IPair __getUserObject_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserObject();
    }

    
    /**
     * Returns the first element of the user object pair.
     *
     * @return the first element of the user object pair
     */
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
    public /*@nullable@*/ /*@helper@*/ Object getUserLeft() {
        return userObject.first;
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
    public  /*@nullable@*/ /*@helper@*/ Object __getUserLeft_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserLeft();
    }

    
    /**
     * Returns the second element of the user object pair.
     *
     * @return the second element of the user object pair
     */
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
    public /*@nullable@*/ /*@helper@*/ Object getUserRight() {
        return userObject.second;
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
    public  /*@nullable@*/ /*@helper@*/ Object __getUserRight_trampoline(boolean this_nullness, boolean this_nullnessnode) {
        return getUserRight();
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
    public abstract /*@helper@*/ void accept(/*@nullable@*/ daikon.diff.Visitor v);
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
