package case_study;


//@ predicate SortedList_OwnFields(SortedList subject; Node first) = subject.first |-> first;
//@ predicate SortedList_FieldTypes(Node first; ) = (first != null ? (Node_OwnFields(first, ?first_head, ?first_tail) &*& Node_FieldTypes(first_head, first_tail) &*& Sorted(first_head, first_tail)) : true);

public final class SortedList  {

    public case_study.Node first;

    
    public SortedList()
        //@ requires true;
        //@ ensures [_]SortedList_OwnFields(this, ?this_first_e) &*& [_]SortedList_FieldTypes(this_first_e) &*& this_first_e == null;
    {
        super();

        this.first = null;
        ;
    }

    
    public void insert(Order newHead)
        //@ requires this.first |-> ?this_first_r &*& (this_first_r != null ? (Node_OwnFields(this_first_r, ?this_first_head_r, ?this_first_tail_r) &*& Node_FieldTypes(this_first_head_r, this_first_tail_r) &*& Sorted(this_first_head_r, this_first_tail_r)) : true) &*& this != null &*& PossiblyEmpty(this) &*& newHead != null &*& (Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r) &*& Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r));
        //@ ensures [_]SortedList_OwnFields(this, ?this_first_e) &*& [_]SortedList_FieldTypes(this_first_e) &*& [_]NonEmpty(this_first_e) &*& newHead != null &*& ([_](Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e)) &*& [_](Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e)));
    {
        if (this.first == null) {
            this.first = Node.__INIT_restorePermissions(newHead);
        } else {
            this.first.__insert_restorePermissions(newHead);
        }
        ;
    }

    
    public Order remove()
        //@ requires this.first |-> ?this_first_r &*& (this_first_r != null ? (Node_OwnFields(this_first_r, ?this_first_head_r, ?this_first_tail_r) &*& Node_FieldTypes(this_first_head_r, this_first_tail_r) &*& Sorted(this_first_head_r, this_first_tail_r)) : true) &*& this != null &*& NonEmpty(this_first_r);
        //@ ensures [_]SortedList_OwnFields(this, ?this_first_e) &*& [_]SortedList_FieldTypes(this_first_e) &*& (result != null ? ([_](Order_OwnFields(result, ?result_witness_e, ?result_customer_e, ?result_product_e)) &*& [_](Order_FieldTypes(result_witness_e, result_customer_e, result_product_e))) : true) &*& [_](this_first_r.head |-> result);
    {
        //@ open NonEmpty(this_first_r);
        case_study.Order result;
        case_study.Order temp2 = this.first.__getHead_restorePermissions();
        result = temp2;
        this.first = this.first.__stealTail_restorePermissions();
        //@ close SortedList_FieldTypes(this.first);
        ;
        return result;
    }

    
    public Order removeIfPresent()
        //@ requires this.first |-> ?this_first_r &*& (this_first_r != null ? (Node_OwnFields(this_first_r, ?this_first_head_r, ?this_first_tail_r) &*& Node_FieldTypes(this_first_head_r, this_first_tail_r) &*& Sorted(this_first_head_r, this_first_tail_r)) : true) &*& this != null &*& PossiblyEmpty(this);
        //@ ensures [_]SortedList_OwnFields(this, ?this_first_e) &*& [_]SortedList_FieldTypes(this_first_e) &*& (result != null ? ([_](Order_OwnFields(result, ?result_witness_e, ?result_customer_e, ?result_product_e)) &*& [_](Order_FieldTypes(result_witness_e, result_customer_e, result_product_e))) : true) &*& this_first_r == null ? result == null : [_](this_first_r.head |-> result);
    {
        if (this.first != null) {
            return this.__remove_restorePermissions();
        } else {
            return null;
        }
    }

    
    public Order getHead()
        //@ requires [_](this.first |-> ?this_first_r) &*& this_first_r != null &*& [_](this_first_r.head |-> ?this_first_head_r);
        //@ ensures [_](this.first |-> this_first_r) &*& this_first_r != null &*& [_](this_first_r.head |-> this_first_head_r) &*& this_first_head_r == result;
    {
        return this.first.__getHead_restorePermissions();
    }


// GENERATED METHODS; UNPROVABLE


    public static SortedList __INIT_restorePermissions()
        //@ requires true;
        //@ ensures result != null &*& SortedList_OwnFields(result, ?result_first_e) &*& SortedList_FieldTypes(result_first_e) &*& result != null &*& PossiblyEmpty(result) &*& result_first_e == null;
    {}

    public void __insert_restorePermissions(Order newHead)
        //@ requires [_]SortedList_OwnFields(this, ?this_first_r) &*& [_]SortedList_FieldTypes(this_first_r) &*& this != null &*& [_]PossiblyEmpty(this) &*& newHead != null &*& ([_](Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r)) &*& [_](Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r)));
        //@ ensures SortedList_OwnFields(this, ?this_first_e) &*& SortedList_FieldTypes(this_first_e) &*& this != null &*& NonEmpty(this_first_e) &*& newHead != null &*& (Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e) &*& Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e));
    {}

    public Order __remove_restorePermissions()
        //@ requires [_]SortedList_OwnFields(this, ?this_first_r) &*& [_]SortedList_FieldTypes(this_first_r) &*& this != null &*& [_]NonEmpty(this_first_r);
        //@ ensures SortedList_OwnFields(this, ?this_first_e) &*& SortedList_FieldTypes(this_first_e) &*& this != null &*& PossiblyEmpty(this) &*& (Order_OwnFields(result, ?result_witness_e, ?result_customer_e, ?result_product_e) &*& Order_FieldTypes(result_witness_e, result_customer_e, result_product_e) &*& result != null) &*& [_](this_first_r.head |-> result);
    {}

    public Order __removeIfPresent_restorePermissions()
        //@ requires [_]SortedList_OwnFields(this, ?this_first_r) &*& [_]SortedList_FieldTypes(this_first_r) &*& this != null &*& [_]PossiblyEmpty(this);
        //@ ensures SortedList_OwnFields(this, ?this_first_e) &*& SortedList_FieldTypes(this_first_e) &*& this != null &*& (result != null ? (Order_OwnFields(result, ?result_witness_e, ?result_customer_e, ?result_product_e) &*& Order_FieldTypes(result_witness_e, result_customer_e, result_product_e)) : true) &*& this_first_r == null ? result == null : [_](this_first_r.head |-> result);
    {}

    public Order __getHead_restorePermissions()
        //@ requires [_](this.first |-> ?this_first_r) &*& this_first_r != null &*& [_](this_first_r.head |-> ?this_first_head_r);
        //@ ensures [_](this.first |-> this_first_r) &*& this_first_r != null &*& [_](this_first_r.head |-> this_first_head_r) &*& this_first_head_r == result;
    {}
}
