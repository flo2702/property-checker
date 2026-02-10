package case_study;


public final class SortedList  {

    //@ public ghost \locset footprint;
    //@ public accessible \inv: footprint;
    //@ public invariant this.footprint == \set_union(\singleton(this.first), \singleton(this.footprint), this.first == null ? \empty : this.first.footprint);
    //@ public invariant this.first != null ==> \invariant_for(this.first);
    //@ public invariant this.first != null ==> \disjoint(this.*, this.first.footprint);
    //@ public invariant_free packed <: case_study.SortedList ==> first.packed == \typeof(first);
    //@ public invariant_free \invariant_free_for(first);
    //@ public invariant_free packed <: case_study.SortedList ==> ((true) && (first == null || first.tail == null || (first.tail != null &&first.tail.head.product.price >= first.head.product.price)));

    public /*@nullable@*/ case_study.Node first;

    
    /*@ public normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures this.first == null;
      @ ensures \fresh(this.footprint);
      @ ensures_free (true) && (this != null);
      @ ensures_free (true) && (this != null);
      @ ensures_free (true) && (this != null);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public SortedList() {
        super();

        this.first = null;
        //@ set footprint = \set_union(\singleton(this.first), \singleton(this.footprint));
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.first == null;
      @ ensures \fresh(\result.footprint);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.SortedList __INIT_trampoline() {
        return new case_study.SortedList();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newHead != null);
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free newHead.packed == \typeof(newHead);
      @ requires_free this != newHead;
      @ ensures (true) && (this != null && this.first != null);
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ assignable this.footprint;
      @*/
    public void insert(/*@nullable@*/ case_study.Order newHead) {
        if (this.first == null) {
            this.first = Node.__INIT_trampoline(newHead, true);
        } else {
            this.first.__insert_trampoline(newHead, true, true, true);
        }
        //@ set footprint = \set_union(\singleton(this.first), \singleton(this.footprint), this.first.footprint);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newHead_nullness || ((true) && (newHead != null));
      @ requires this_empty || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newHead_nullness || ((true) && (newHead != null));
      @ requires_free !this_empty || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ ensures_free (true) && (this != null && this.first != null);
      @ assignable this.footprint;
      @*/
    public  void __insert_trampoline(/*@nullable@*/ case_study.Order newHead, boolean this_nullness, boolean newHead_nullness, boolean this_empty) {
        insert(newHead);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this != null && this.first != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures \old(this.first).head == \result;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (this != null);
      @ assignable this.footprint, this.first.packed;
      @*/
    public /*@nullable@*/ Order remove() {
        ;
        case_study.Order result;
        case_study.Order temp2 = this.first.__getHead_trampoline(true, true);
        result = temp2;
        this.first = this.first.__stealTail_trampoline(true, true);
        ;
        //@ set footprint = \set_union(\singleton(this.first), \singleton(this.footprint), this.first == null ? \empty : this.first.footprint);
        return result;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_empty || ((true) && (this != null && this.first != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_empty || ((true) && (this != null && this.first != null));
      @ ensures \invariant_free_for(this);
      @ ensures \old(this.first).head == \result;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (this != null);
      @ assignable this.footprint, this.first.packed;
      @*/
    public  /*@nullable@*/ case_study.Order __remove_trampoline(boolean this_nullness, boolean this_empty) {
        return remove();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures \old(this.first) != null ==> \result == \old(this.first).head;
      @ ensures \old(this.first) == null ==> \result == null;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ assignable this.footprint, this.first.packed;
      @*/
    public /*@nullable@*/ Order removeIfPresent() {
        if (this.first != null) {
            return this.__remove_trampoline(true, false);
        } else {
            return null;
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_empty || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_empty || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures \old(this.first) != null ==> \result == \old(this.first).head;
      @ ensures \old(this.first) == null ==> \result == null;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ assignable this.footprint, this.first.packed;
      @*/
    public  /*@nullable@*/ case_study.Order __removeIfPresent_trampoline(boolean this_nullness, boolean this_empty) {
        return removeIfPresent();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this != null && this.first != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures (true) && (\result != null);
      @ ensures \result == this.first.head;
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public /*@nullable@*/ Order getHead() {
        return this.first.__getHead_trampoline(true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_empty || ((true) && (this != null && this.first != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_empty || ((true) && (this != null && this.first != null));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.first.head;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public  /*@nullable@*/ case_study.Order __getHead_trampoline(boolean this_nullness, boolean this_empty) {
        return getHead();
    }

}
