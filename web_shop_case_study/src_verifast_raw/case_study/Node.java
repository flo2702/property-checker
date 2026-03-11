package case_study;


//@ predicate Node_OwnFields(Node subject; Order head, Node tail) = subject.head |-> head &*& subject.tail |-> tail;
//@ predicate Node_FieldTypes(Order head, Node tail; ) = head != null &*& (Order_OwnFields(head, ?head_witness, ?head_customer, ?head_product) &*& Order_FieldTypes(head_witness, head_customer, head_product)) &*& (tail != null ? (Node_OwnFields(tail, ?tail_head, ?tail_tail) &*& Node_FieldTypes(tail_head, tail_tail) &*& Sorted(tail_head, tail_tail)) : true);

public final class Node  {

    public case_study.Order head;

    public case_study.Node tail;

    
    public Node(Order head, Node tail)
        //@ requires head != null &*& tail != null &*& (Order_OwnFields(head, ?head_witness_r, ?head_customer_r, ?head_product_r) &*& Order_FieldTypes(head_witness_r, head_customer_r, head_product_r)) &*& (Node_OwnFields(tail, ?tail_head_r, ?tail_tail_r) &*& Node_FieldTypes(tail_head_r, tail_tail_r) &*& Sorted(tail_head_r, tail_tail_r)) &*& Sorted(head, tail);
        //@ ensures [_]Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& [_]Node_FieldTypes(this_head_e, this_tail_e) &*& [_]Sorted(this_head_e, this_tail_e) &*& (head != null) &*& (tail != null &*& [_](Sorted(tail_head_r, tail_tail_r))) &*& this_tail_e == tail &*& this_head_e == head;
    {
        super();

        this.head = head;
        this.tail = tail;
        ;
        //@ close [0.5]Node_FieldTypes(this.head, this.tail);
        //@ close [0.5]Sorted(tail_head_r, tail_tail_r);
    }

    
    public Node(Order head)
        //@ requires head != null &*& (Order_OwnFields(head, ?head_witness_r, ?head_customer_r, ?head_product_r) &*& Order_FieldTypes(head_witness_r, head_customer_r, head_product_r));
        //@ ensures [_]Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& [_]Node_FieldTypes(this_head_e, this_tail_e) &*& [_]Sorted(this_head_e, this_tail_e) &*& (head != null) &*& this_tail_e == null &*& this_head_e == head;
    {
        super();

        this.head = head;
        this.tail = null;
        ;
    }

    
    public void insert(Order newHead)
        //@ requires this.head |-> ?this_head_r &*& this.tail |-> ?this_tail_r &*& this_head_r != null &*& (Order_OwnFields(this_head_r, ?this_head_witness_r, ?this_head_customer_r, ?this_head_product_r) &*& Order_FieldTypes(this_head_witness_r, this_head_customer_r, this_head_product_r)) &*& (this_tail_r != null ? (Node_OwnFields(this_tail_r, ?this_tail_head_r, ?this_tail_tail_r) &*& Node_FieldTypes(this_tail_head_r, this_tail_tail_r) &*& Sorted(this_tail_head_r, this_tail_tail_r)) : true) &*& this != null &*& Sorted(this_head_r, this_tail_r) &*& newHead != null &*& (Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r) &*& Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r));
        //@ ensures [_]Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& [_]Node_FieldTypes(this_head_e, this_tail_e) &*& [_]Sorted(this_head_e, this_tail_e) &*& ([_](Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e)) &*& [_](Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e)) &*& newHead != null) &*& (this_head_e == this_head_r || this_head_e == newHead);
    {
        //@ open [0.5]Order_OwnFields(this_head_r, _, _, ?oldHead_product);
        //@ open [0.5]Product_OwnFields(oldHead_product, _, ?oldPrice, _);
        //@ close [0.5]OrderPred(this_head_r, oldPrice);
        //@ open [0.5]Order_OwnFields(newHead, _, _, ?newHead_product);
        //@ open [0.5]Product_OwnFields(newHead_product, _, ?newPrice, _);
        //@ close [0.5]OrderPred(newHead, newPrice);
        if (newHead.__getPrice_restorePermissions() <= this.head.__getPrice_restorePermissions()) {
            //@ close [0.5]SortedOrders(newHead, this_head_r);
            //@ close [0.5]Node_FieldTypes(this_head_r, this_tail_r);
            this.__insertHead_restorePermissions(newHead);
        } else {
            //@ close [0.5]SortedOrders(this_head_r, newHead);
            //@ close [0.5]Node_FieldTypes(this_head_r, this_tail_r);
            this.__insertTail_restorePermissions(newHead);
        }
    }

    
    private void insertHead(Order newHead)
        //@ requires this.head |-> ?this_head_r &*& this.tail |-> ?this_tail_r &*& this_head_r != null &*& (Order_OwnFields(this_head_r, ?this_head_witness_r, ?this_head_customer_r, ?this_head_product_r) &*& Order_FieldTypes(this_head_witness_r, this_head_customer_r, this_head_product_r)) &*& (this_tail_r != null ? (Node_OwnFields(this_tail_r, ?this_tail_head_r, ?this_tail_tail_r) &*& Node_FieldTypes(this_tail_head_r, this_tail_tail_r) &*& Sorted(this_tail_head_r, this_tail_tail_r)) : true) &*& this != null &*& Sorted(this_head_r, this_tail_r) &*& newHead != null &*& (Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r) &*& Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r)) &*& SortedOrders(newHead, this_head_r);
        //@ ensures [_]Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& [_]Node_FieldTypes(this_head_e, this_tail_e) &*& [_]Sorted(this_head_e, this_tail_e) &*& ([_](Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e)) &*& [_](Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e)) &*& newHead != null) &*& this_head_e == newHead;
    {
        if (this.tail == null) {
            this.tail = Node.__INIT_restorePermissions(this.head);
        } else {
            this.tail = Node.__INIT_restorePermissions(this.head,this.tail);
        }
        this.head = newHead;
        //@ close [0.5]Node_OwnFields(this.tail, this_head_r, _);
        //@ close [0.5]Sorted(newHead, this.tail);
        ;
    }

    
    private void insertTail(Order newHead)
        //@ requires this.head |-> ?this_head_r &*& this.tail |-> ?this_tail_r &*& this_head_r != null &*& (Order_OwnFields(this_head_r, ?this_head_witness_r, ?this_head_customer_r, ?this_head_product_r) &*& Order_FieldTypes(this_head_witness_r, this_head_customer_r, this_head_product_r)) &*& (this_tail_r != null ? (Node_OwnFields(this_tail_r, ?this_tail_head_r, ?this_tail_tail_r) &*& Node_FieldTypes(this_tail_head_r, this_tail_tail_r) &*& Sorted(this_tail_head_r, this_tail_tail_r)) : true) &*& this != null &*& Sorted(this_head_r, this_tail_r) &*& newHead != null &*& (Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r) &*& Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r)) &*& SortedOrders(this_head_r, newHead);
        //@ ensures [_]Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& [_]Node_FieldTypes(this_head_e, this_tail_e) &*& [_]Sorted(this_head_e, this_tail_e) &*& ([_](Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e)) &*& [_](Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e)) &*& newHead != null) &*& this_head_e == this_head_r;
    {
        if (tail == null) {
            this.tail = Node.__INIT_restorePermissions(newHead);
        } else {
            this.tail.__insert_restorePermissions(newHead);
        }
        //@ close [0.5]Node_OwnFields(this.tail, _, _);
        //@ close [0.5]Sorted(this.head, this.tail);
        ;
        ;
        ;
        ;
    }

    
    public Order getHead()
        //@ requires [?frac](this.head |-> ?this_head_r);
        //@ ensures [frac](this.head |-> this_head_r) &*& this_head_r == result;
    {
        return this.head;
    }

    
    public Node getTail()
        //@ requires [?frac](this.tail |-> ?this_tail_r);
        //@ ensures [frac](this.tail |-> this_tail_r) &*& this_tail_r == result;
    {
        return this.tail;
    }

    
    public Node stealTail()
        //@ requires [?frac](this.tail |-> ?this_tail_r);
        //@ ensures [frac](this.tail |-> this_tail_r) &*& this_tail_r == result;
    {
        return this.tail;
    }


// GENERATED METHODS; UNPROVABLE


    public static Node __INIT_restorePermissions(Order head, Node tail)
        //@ requires head != null &*& tail != null &*& ([_](Order_OwnFields(head, ?head_witness_r, ?head_customer_r, ?head_product_r)) &*& [_](Order_FieldTypes(head_witness_r, head_customer_r, head_product_r))) &*& ([_](Node_OwnFields(tail, ?tail_head_r, ?tail_tail_r)) &*& [_](Node_FieldTypes(tail_head_r, tail_tail_r)) &*& [_](Sorted(tail_head_r, tail_tail_r))) &*& Sorted(head, tail);
        //@ ensures result != null &*& Node_OwnFields(result, ?result_head_e, ?result_tail_e) &*& Node_FieldTypes(result_head_e, result_tail_e) &*& result != null &*& Sorted(result_head_e, result_tail_e) &*& (Order_OwnFields(head, head_witness_r, head_customer_r, head_product_r) &*& Order_FieldTypes(head_witness_r, head_customer_r, head_product_r) &*& head != null) &*& (Node_OwnFields(tail, tail_head_r, tail_tail_r) &*& Node_FieldTypes(tail_head_r, tail_tail_r) &*& tail != null &*& Sorted(tail_head_r, tail_tail_r)) &*& result_tail_e == tail &*& result_head_e == head;
    {}

    public static Node __INIT_restorePermissions(Order head)
        //@ requires head != null &*& ([_](Order_OwnFields(head, ?head_witness_r, ?head_customer_r, ?head_product_r)) &*& [_](Order_FieldTypes(head_witness_r, head_customer_r, head_product_r)));
        //@ ensures result != null &*& Node_OwnFields(result, ?result_head_e, ?result_tail_e) &*& Node_FieldTypes(result_head_e, result_tail_e) &*& result != null &*& Sorted(result_head_e, result_tail_e) &*& (Order_OwnFields(head, head_witness_r, head_customer_r, head_product_r) &*& Order_FieldTypes(head_witness_r, head_customer_r, head_product_r) &*& head != null) &*& result_tail_e == null &*& result_head_e == head;
    {}

    public void __insert_restorePermissions(Order newHead)
        //@ requires [_]Node_OwnFields(this, ?this_head_r, ?this_tail_r) &*& [_]Node_FieldTypes(this_head_r, this_tail_r) &*& this != null &*& [_]Sorted(this_head_r, this_tail_r) &*& newHead != null &*& ([_](Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r)) &*& [_](Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r)));
        //@ ensures Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& Node_FieldTypes(this_head_e, this_tail_e) &*& Sorted(this_head_e, this_tail_e) &*& (Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e) &*& Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e) &*& newHead != null) &*& (this_head_e == this_head_r || this_head_e == newHead);
    {}

    private void __insertHead_restorePermissions(Order newHead)
        //@ requires [_]Node_OwnFields(this, ?this_head_r, ?this_tail_r) &*& [_]Node_FieldTypes(this_head_r, this_tail_r) &*& this != null &*& [_]Sorted(this_head_r, this_tail_r) &*& newHead != null &*& ([_](Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r)) &*& [_](Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r))) &*& SortedOrders(newHead, this_head_r);
        //@ ensures Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& Node_FieldTypes(this_head_e, this_tail_e) &*& Sorted(this_head_e, this_tail_e) &*& (Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e) &*& Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e) &*& newHead != null) &*& this_head_e == newHead;
    {}

    private void __insertTail_restorePermissions(Order newHead)
        //@ requires [_]Node_OwnFields(this, ?this_head_r, ?this_tail_r) &*& [_]Node_FieldTypes(this_head_r, this_tail_r) &*& this != null &*& [_]Sorted(this_head_r, this_tail_r) &*& newHead != null &*& ([_](Order_OwnFields(newHead, ?newHead_witness_r, ?newHead_customer_r, ?newHead_product_r)) &*& [_](Order_FieldTypes(newHead_witness_r, newHead_customer_r, newHead_product_r))) &*& SortedOrders(this_head_r, newHead);
        //@ ensures Node_OwnFields(this, ?this_head_e, ?this_tail_e) &*& Node_FieldTypes(this_head_e, this_tail_e) &*& Sorted(this_head_e, this_tail_e) &*& (Order_OwnFields(newHead, ?newHead_witness_e, ?newHead_customer_e, ?newHead_product_e) &*& Order_FieldTypes(newHead_witness_e, newHead_customer_e, newHead_product_e) &*& newHead != null) &*& this_head_e == this_head_r;
    {}

    public Order __getHead_restorePermissions()
        //@ requires [?frac](this.head |-> ?this_head_r);
        //@ ensures [frac](this.head |-> this_head_r) &*& this_head_r == result;
    {}

    public Node __getTail_restorePermissions()
        //@ requires [?frac](this.tail |-> ?this_tail_r);
        //@ ensures [frac](this.tail |-> this_tail_r) &*& this_tail_r == result;
    {}

    public Node __stealTail_restorePermissions()
        //@ requires [?frac](this.tail |-> ?this_tail_r);
        //@ ensures [frac](this.tail |-> this_tail_r) &*& this_tail_r == result;
    {}
}
