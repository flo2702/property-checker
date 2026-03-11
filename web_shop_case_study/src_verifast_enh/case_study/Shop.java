package case_study;


//@ predicate Shop_OwnFields(Shop subject; SortedList orders) = subject.orders |-> orders;
//@ predicate Shop_FieldTypes(SortedList orders; ) = orders != null &*& PossiblyEmpty(orders) &*& (SortedList_OwnFields(orders, ?orders_first) &*& SortedList_FieldTypes(orders_first));

public final class Shop  {

    public case_study.SortedList orders;

    
    public Shop()
        //@ requires true;
        //@ ensures [_]Shop_OwnFields(this, ?this_orders_e) &*& [_]Shop_FieldTypes(this_orders_e);
    {
        super();

        this.orders = SortedList.__INIT_restorePermissions();
    }

    
    public void addOrder(Order order)
        //@ requires this.orders |-> ?this_orders_r &*& this_orders_r != null &*& PossiblyEmpty(this_orders_r) &*& (SortedList_OwnFields(this_orders_r, ?this_orders_first_r) &*& SortedList_FieldTypes(this_orders_first_r)) &*& this != null &*& order != null &*& (Order_OwnFields(order, ?order_witness_r, ?order_customer_r, ?order_product_r) &*& Order_FieldTypes(order_witness_r, order_customer_r, order_product_r));
        //@ ensures [_]Shop_OwnFields(this, ?this_orders_e) &*& [_]Shop_FieldTypes(this_orders_e) &*& order != null &*& ([_](Order_OwnFields(order, ?order_witness_e, ?order_customer_e, ?order_product_e)) &*& [_](Order_FieldTypes(order_witness_e, order_customer_e, order_product_e)));
    {
        this.orders.__insert_restorePermissions(order);
    }

    
    public boolean processNextOrder()
        //@ requires this.orders |-> ?this_orders_r &*& this_orders_r != null &*& PossiblyEmpty(this_orders_r) &*& (SortedList_OwnFields(this_orders_r, ?this_orders_first_r) &*& SortedList_FieldTypes(this_orders_first_r)) &*& this != null;
        //@ ensures [_]Shop_OwnFields(this, ?this_orders_e) &*& [_]Shop_FieldTypes(this_orders_e) &*& true;
    {
        case_study.Order result;
        case_study.Order temp1 = this.orders.__removeIfPresent_restorePermissions();
        result = temp1;
        return result != null;
    }


// GENERATED METHODS; UNPROVABLE


    public static Shop __INIT_restorePermissions()
        //@ requires true;
        //@ ensures result != null &*& Shop_OwnFields(result, ?result_orders_e) &*& Shop_FieldTypes(result_orders_e) &*& result != null;
    {}

    public void __addOrder_restorePermissions(Order order)
        //@ requires [_]Shop_OwnFields(this, ?this_orders_r) &*& [_]Shop_FieldTypes(this_orders_r) &*& this != null &*& order != null &*& ([_](Order_OwnFields(order, ?order_witness_r, ?order_customer_r, ?order_product_r)) &*& [_](Order_FieldTypes(order_witness_r, order_customer_r, order_product_r)));
        //@ ensures Shop_OwnFields(this, ?this_orders_e) &*& Shop_FieldTypes(this_orders_e) &*& this != null &*& order != null &*& (Order_OwnFields(order, ?order_witness_e, ?order_customer_e, ?order_product_e) &*& Order_FieldTypes(order_witness_e, order_customer_e, order_product_e));
    {}

    public boolean __processNextOrder_restorePermissions()
        //@ requires [_]Shop_OwnFields(this, ?this_orders_r) &*& [_]Shop_FieldTypes(this_orders_r) &*& this != null;
        //@ ensures Shop_OwnFields(this, ?this_orders_e) &*& Shop_FieldTypes(this_orders_e) &*& this != null &*& true;
    {}
}
