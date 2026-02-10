package case_study;


//@ predicate Order_OwnFields(Order subject; int witness, Customer customer, Product product) = subject.witness |-> witness &*& subject.customer |-> customer &*& subject.product |-> product;
//@ predicate Order_FieldTypes(int witness, Customer customer, Product product; ) = customer != null &*& product != null &*& (Customer_OwnFields(customer, ?customer_name, ?customer_age) &*& Customer_FieldTypes(customer_name, customer_age) &*& AgedOver(customer_age, witness)) &*& (Product_OwnFields(product, ?product_title, ?product_price, ?product_ageRestriction) &*& Product_FieldTypes(product_title, product_price, product_ageRestriction) &*& AllowedFor(product_ageRestriction, witness)) &*& true;

public final class Order  {

    public int witness;

    public case_study.Customer customer;

    public case_study.Product product;

    
    public Order(int witness, Customer customer, Product product)
        //@ requires customer != null &*& product != null &*& (Customer_OwnFields(customer, ?customer_name_r, ?customer_age_r) &*& Customer_FieldTypes(customer_name_r, customer_age_r) &*& AgedOver(customer_age_r, witness)) &*& (Product_OwnFields(product, ?product_title_r, ?product_price_r, ?product_ageRestriction_r) &*& Product_FieldTypes(product_title_r, product_price_r, product_ageRestriction_r) &*& AllowedFor(product_ageRestriction_r, witness)) &*& true;
        //@ ensures [_]Order_OwnFields(this, ?this_witness_e, ?this_customer_e, ?this_product_e) &*& [_]Order_FieldTypes(this_witness_e, this_customer_e, this_product_e) &*& (customer != null &*& [_](AgedOver(customer_age_r, witness))) &*& (product != null &*& [_](AllowedFor(product_ageRestriction_r, witness))) &*& true &*& this_customer_e == customer &*& this_product_e == product &*& this_witness_e == witness;
    {
        super();

        this.witness = witness;
        this.customer = customer;
        this.product = product;
        //@ open AgedOver(customer_age_r, witness);
        //@ close AgedOver(customer_age_r, witness);
        //@ open AllowedFor(product_ageRestriction_r, witness);
        //@ close AllowedFor(product_ageRestriction_r, witness);
    }

    
    public int getPrice()
        //@ requires [?frac0](this.product |-> ?this_product_r) &*& [?frac1](this_product_r.price |-> ?this_product_price_r);
        //@ ensures [frac0](this.product |-> this_product_r) &*& [frac1](this_product_r.price |-> this_product_price_r) &*& this_product_price_r == result;
    {
        return product.__getPrice_restorePermissions();
    }


// GENERATED METHODS; UNPROVABLE


    public static Order __INIT_restorePermissions(int witness, Customer customer, Product product)
        //@ requires customer != null &*& product != null &*& ([_](Customer_OwnFields(customer, ?customer_name_r, ?customer_age_r)) &*& [_](Customer_FieldTypes(customer_name_r, customer_age_r)) &*& [_](AgedOver(customer_age_r, witness))) &*& ([_](Product_OwnFields(product, ?product_title_r, ?product_price_r, ?product_ageRestriction_r)) &*& [_](Product_FieldTypes(product_title_r, product_price_r, product_ageRestriction_r)) &*& [_](AllowedFor(product_ageRestriction_r, witness))) &*& true;
        //@ ensures result != null &*& Order_OwnFields(result, ?result_witness_e, ?result_customer_e, ?result_product_e) &*& Order_FieldTypes(result_witness_e, result_customer_e, result_product_e) &*& result != null &*& (Customer_OwnFields(customer, customer_name_r, customer_age_r) &*& Customer_FieldTypes(customer_name_r, customer_age_r) &*& customer != null &*& AgedOver(customer_age_r, witness)) &*& (Product_OwnFields(product, product_title_r, product_price_r, product_ageRestriction_r) &*& Product_FieldTypes(product_title_r, product_price_r, product_ageRestriction_r) &*& product != null &*& AllowedFor(product_ageRestriction_r, witness)) &*& true &*& result_customer_e == customer &*& result_product_e == product &*& result_witness_e == witness;
    {}

    public int __getPrice_restorePermissions()
        //@ requires [?frac0](this.product |-> ?this_product_r) &*& [?frac1](this_product_r.price |-> ?this_product_price_r);
        //@ ensures [frac0](this.product |-> this_product_r) &*& [frac1](this_product_r.price |-> this_product_price_r) &*& this_product_price_r == result;
    {}
}
