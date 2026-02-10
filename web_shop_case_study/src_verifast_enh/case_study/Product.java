package case_study;


//@ predicate Product_OwnFields(Product subject; String title, int price, int ageRestriction) = subject.title |-> title &*& subject.price |-> price &*& subject.ageRestriction |-> ageRestriction;
//@ predicate Product_FieldTypes(String title, int price, int ageRestriction; ) = title != null &*& (Interval(ageRestriction, 0, 18)) &*& (Interval(price, 0, 2147483647)) &*& true;

public final class Product  {

    public java.lang.String title;

    public int price;

    public int ageRestriction;

    
    public Product(String title, int price, int ageRestriction)
        //@ requires title != null &*& (Interval(ageRestriction, 0, 18)) &*& (Interval(price, 0, 2147483647)) &*& true;
        //@ ensures [_]Product_OwnFields(this, ?this_title_e, ?this_price_e, ?this_ageRestriction_e) &*& [_]Product_FieldTypes(this_title_e, this_price_e, this_ageRestriction_e) &*& [_]AllowedFor(this_ageRestriction_e, ageRestriction) &*& title != null &*& true &*& true &*& true &*& this_title_e == title &*& this_price_e == price &*& this_ageRestriction_e == ageRestriction;
    {
        super();

        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
    }

    
    public int getPrice()
        //@ requires [?frac](this.price |-> ?this_price_r);
        //@ ensures [frac](this.price |-> this_price_r) &*& this_price_r == result;
    {
        return price;
    }


// GENERATED METHODS; UNPROVABLE


    public static Product __INIT_restorePermissions(String title, int price, int ageRestriction)
        //@ requires title != null &*& ([_](Interval(ageRestriction, 0, 18))) &*& ([_](Interval(price, 0, 2147483647))) &*& true;
        //@ ensures result != null &*& Product_OwnFields(result, ?result_title_e, ?result_price_e, ?result_ageRestriction_e) &*& Product_FieldTypes(result_title_e, result_price_e, result_ageRestriction_e) &*& result != null &*& AllowedFor(result_ageRestriction_e, ageRestriction) &*& title != null &*& Interval(price, 0, 2147483647) &*& Interval(ageRestriction, 0, 18) &*& true &*& true &*& true &*& result_title_e == title &*& result_price_e == price &*& result_ageRestriction_e == ageRestriction;
    {}

    public int __getPrice_restorePermissions()
        //@ requires [?frac](this.price |-> ?this_price_r);
        //@ ensures [frac](this.price |-> this_price_r) &*& this_price_r == result;
    {}
}
