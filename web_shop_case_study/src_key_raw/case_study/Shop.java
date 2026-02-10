package case_study;


public final class Shop  {

    //@ public accessible \inv: this.orders, this.orders.footprint;
    //@ public invariant this.orders != null ==> \invariant_for(this.orders);
    //@ public invariant this.orders != null ==> \disjoint(this.*, this.orders.footprint);
    //@ public invariant_free packed <: case_study.Shop ==> orders.packed == \typeof(orders);
    //@ public invariant_free \invariant_free_for(orders);
    //@ public invariant_free packed <: case_study.Shop ==> ((true) && (orders != null));
    //@ public invariant_free packed <: case_study.Shop ==> ((true) && (orders != null));
    //@ public invariant_free packed <: case_study.Shop ==> ((true) && (orders != null ==> \invariant_for(orders)));

    public /*@nullable@*/ case_study.SortedList orders;

    
    /*@ public normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures (true) && (this != null);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Shop() {
        super();

        this.orders = SortedList.__INIT_trampoline();
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures (true) && (\result != null);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Shop __INIT_trampoline() {
        return new case_study.Shop();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (order != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free order.packed == \typeof(order);
      @ requires_free this != order;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free order.packed == \typeof(order);
      @ assignable this.orders.footprint;
      @*/
    public void addOrder(/*@nullable@*/ case_study.Order order) {
        this.orders.__insert_trampoline(order, false, false, false);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires order_nullness || ((true) && (order != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !order_nullness || ((true) && (order != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free order.packed == \typeof(order);
      @ assignable this.orders.footprint;
      @*/
    public  void __addOrder_trampoline(/*@nullable@*/ case_study.Order order, boolean this_nullness, boolean order_nullness) {
        addOrder(order);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures_free this.packed == \typeof(this);
      @ assignable this.orders.footprint, this.orders.first.packed;
      @*/
    public boolean processNextOrder() {
        case_study.Order result;
        case_study.Order temp1 = this.orders.__removeIfPresent_trampoline(false, false);
        result = temp1;
        return result != null;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ assignable this.orders.footprint, this.orders.first.packed;
      @*/
    public  boolean __processNextOrder_trampoline(boolean this_nullness) {
        return processNextOrder();
    }

}
