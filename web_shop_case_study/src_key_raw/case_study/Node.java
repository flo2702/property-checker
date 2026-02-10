package case_study;


public final class Node  {

    //@ public ghost \locset footprint;
    //@ public accessible \inv: footprint;
    //@ public invariant this.footprint == \set_union(\singleton(this.head), \singleton(this.tail), \singleton(this.footprint), this.tail == null ? \empty : this.tail.footprint);
    //@ public invariant this.tail != null ==> \disjoint(this.*, this.tail.footprint);
    //@ public invariant this.tail == null || \invariant_for(this.tail);
    //@ public invariant_free packed <: case_study.Node ==> head.packed == \typeof(head);
    //@ public invariant_free \invariant_free_for(head);
    //@ public invariant_free packed <: case_study.Node ==> tail.packed == \typeof(tail);
    //@ public invariant_free \invariant_free_for(tail);
    //@ public invariant_free packed <: case_study.Node ==> tail != head;
    //@ public invariant_free packed <: case_study.Node ==> ((true) && (head != null));
    //@ public invariant_free packed <: case_study.Node ==> ((true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price)));

    public /*@nullable@*/ case_study.Order head;

    public /*@nullable@*/ case_study.Node tail;

    
    /*@ public normal_behavior
      @ requires (true) && (head != null);
      @ requires (true) && (tail != null);
      @ requires (true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price));
      @ requires \invariant_for(tail);
      @ requires head.product.price <= tail.head.product.price;
      @ requires_free this.packed == \typeof(this);
      @ requires_free head.packed == \typeof(head);
      @ requires_free tail.packed == \typeof(tail);
      @ requires_free tail != head;
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ ensures this.tail == tail && this.head == head;
      @ ensures_free head.packed == \typeof(head);
      @ ensures_free tail.packed == \typeof(tail);
      @ ensures (true) && (this != null);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ ensures (true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price));
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Node(/*@nullable@*/ case_study.Order head, /*@nullable@*/ case_study.Node tail) {
        super();

        this.head = head;
        this.tail = tail;
        //@ set footprint = \set_union(\singleton(this.head), \singleton(this.tail), \singleton(this.footprint), this.tail.footprint);
        ;
        ;
    }

    /*@ public normal_behavior
      @ requires head_nullness || ((true) && (head != null));
      @ requires tail_nullness || ((true) && (tail != null));
      @ requires tail_sorted || ((true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price)));
      @ requires \invariant_for(tail);
      @ requires head.product.price <= tail.head.product.price;
      @ requires_free !head_nullness || ((true) && (head != null));
      @ requires_free !tail_nullness || ((true) && (tail != null));
      @ requires_free !tail_sorted || ((true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price)));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.tail == tail && \result.head == head;
      @ ensures_free head.packed == \typeof(head);
      @ ensures_free tail.packed == \typeof(tail);
      @ ensures (true) && (\result != null);
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ ensures (true) && (tail == null || tail.tail == null || (tail.tail != null &&tail.tail.head.product.price >= tail.head.product.price));
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Node __INIT_trampoline(/*@nullable@*/ case_study.Order head, /*@nullable@*/ case_study.Node tail, boolean head_nullness, boolean tail_nullness, boolean tail_sorted) {
        return new case_study.Node(head, tail);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (head != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free head.packed == \typeof(head);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ ensures this.head == head && this.tail == null;
      @ ensures_free head.packed == \typeof(head);
      @ ensures (true) && (this != null);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Node(/*@nullable@*/ case_study.Order head) {
        super();

        this.head = head;
        this.tail = null;
        //@ set footprint = \set_union(\singleton(this.head), \singleton(this.tail), \singleton(this.footprint));
    }

    /*@ public normal_behavior
      @ requires head_nullness || ((true) && (head != null));
      @ requires_free !head_nullness || ((true) && (head != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.head == head && \result.tail == null;
      @ ensures_free head.packed == \typeof(head);
      @ ensures (true) && (\result != null);
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Node __INIT_trampoline(/*@nullable@*/ case_study.Order head, boolean head_nullness) {
        return new case_study.Node(head);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newHead != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires_free this.packed == \typeof(this);
      @ requires_free newHead.packed == \typeof(newHead);
      @ requires_free this != newHead;
      @ ensures this.head == \old(this.head) || this.head == newHead;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.footprint;
      @*/
    public void insert(/*@nullable@*/ case_study.Order newHead) {
        ;
        ;
        ;
        ;
        ;
        ;
        if (newHead.__getPrice_trampoline(false) <= this.head.__getPrice_trampoline(false)) {
            ;
            ;
            this.__insertHead_trampoline(newHead, false, false, false);
        } else {
            ;
            ;
            this.__insertTail_trampoline(newHead, false, false, false);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newHead_nullness || ((true) && (newHead != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newHead_nullness || ((true) && (newHead != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures this.head == \old(this.head) || this.head == newHead;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.footprint;
      @*/
    public  void __insert_trampoline(/*@nullable@*/ case_study.Order newHead, boolean this_nullness, boolean newHead_nullness, boolean this_sorted) {
        insert(newHead);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newHead != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires newHead.product.price <= this.head.product.price;
      @ requires_free this.packed == \typeof(this);
      @ requires_free newHead.packed == \typeof(newHead);
      @ requires_free this != newHead;
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ ensures this.head == newHead;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ assignable this.footprint;
      @*/
    private void insertHead(/*@nullable@*/ case_study.Order newHead) {
        if (this.tail == null) {
            this.tail = Node.__INIT_trampoline(this.head, false);
        } else {
            this.tail = Node.__INIT_trampoline(this.head,this.tail, false, false, false);
        }
        this.head = newHead;
        ;
        ;
        //@ set footprint = \set_union(\singleton(this.head), \singleton(this.tail), \singleton(this.footprint), this.tail.footprint);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newHead_nullness || ((true) && (newHead != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires newHead.product.price <= this.head.product.price;
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newHead_nullness || ((true) && (newHead != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures this.head == newHead;
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.footprint;
      @*/
    public  void __insertHead_trampoline(/*@nullable@*/ case_study.Order newHead, boolean this_nullness, boolean newHead_nullness, boolean this_sorted) {
        insertHead(newHead);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (newHead != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires this.head.product.price <= newHead.product.price;
      @ requires_free this.packed == \typeof(this);
      @ requires_free newHead.packed == \typeof(newHead);
      @ requires_free this != newHead;
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ ensures this.head == \old(this.head);
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ assignable this.footprint;
      @*/
    private void insertTail(/*@nullable@*/ case_study.Order newHead) {
        if (tail == null) {
            this.tail = Node.__INIT_trampoline(newHead, false);
        } else {
            this.tail.__insert_trampoline(newHead, false, false, false);
        }
        ;
        ;
        //@ set footprint = \set_union(\singleton(this.head), \singleton(this.tail), \singleton(this.footprint), this.tail.footprint);
        //@ assume this.head == \old(this.head) ==> this.head.product.price == \old(this.head.product.price);
        //@ assume this.tail.head == \old(this.tail.head) ==> this.tail.head.product.price == \old(this.tail.head.product.price);
        //@ assume this.tail.head == \old(newHead) ==> this.tail.head.product.price == \old(newHead.product.price);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires newHead_nullness || ((true) && (newHead != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires this.head.product.price <= newHead.product.price;
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !newHead_nullness || ((true) && (newHead != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures this.head == \old(this.head);
      @ ensures \new_elems_fresh(this.footprint);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free newHead.packed == \typeof(newHead);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.footprint;
      @*/
    public  void __insertTail_trampoline(/*@nullable@*/ case_study.Order newHead, boolean this_nullness, boolean newHead_nullness, boolean this_sorted) {
        insertTail(newHead);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires_free this.packed == \typeof(this);
      @ ensures \result == this.head;
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (\result != null);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public /*@nullable@*/ Order getHead() {
        return this.head;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.head;
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (\result != null);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public  /*@nullable@*/ case_study.Order __getHead_trampoline(boolean this_nullness, boolean this_sorted) {
        return getHead();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires_free this.packed == \typeof(this);
      @ ensures \result == this.tail;
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public /*@nullable@*/ Node getTail() {
        return this.tail;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.tail;
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public  /*@nullable@*/ case_study.Node __getTail_trampoline(boolean this_nullness, boolean this_sorted) {
        return getTail();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ requires_free this.packed == \typeof(this);
      @ ensures \result == this.tail;
      @ ensures \result != null ==> \invariant_for(\result);
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.packed;
      @*/
    public /*@nullable@*/ Node stealTail() {
        return this.tail;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !this_sorted || ((true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price)));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.tail;
      @ ensures \result != null ==> \invariant_for(\result);
      @ ensures_free this.packed == \typeof(this);
      @ ensures (true) && (\result == null || \result.tail == null || (\result.tail != null &&\result.tail.head.product.price >= \result.head.product.price));
      @ ensures (true) && (this == null || this.tail == null || (this.tail != null &&this.tail.head.product.price >= this.head.product.price));
      @ assignable this.packed;
      @*/
    public  /*@nullable@*/ case_study.Node __stealTail_trampoline(boolean this_nullness, boolean this_sorted) {
        return stealTail();
    }

}
