package case_study;


//@ predicate Customer_OwnFields(Customer subject; String name, int age) = subject.name |-> name &*& subject.age |-> age;
//@ predicate Customer_FieldTypes(String name, int age; ) = name != null &*& (Interval(age, 14, 150)) &*& true;

public final class Customer  {

    public java.lang.String name;

    public int age;

    
    public Customer(String name, int age)
        //@ requires name != null &*& (Interval(age, 14, 150)) &*& true;
        //@ ensures [_]Customer_OwnFields(this, ?this_name_e, ?this_age_e) &*& [_]Customer_FieldTypes(this_name_e, this_age_e) &*& [_]AgedOver(this_age_e, age) &*& ([_](Interval(age, 14, 150))) &*& (name != null) &*& this_name_e == name &*& this_age_e == age;
    {
        super();

        this.name = name;
        this.age = age;
        //@ open Interval(age, 14, 150);
        //@ close Interval(age, 14, 150);
    }


// GENERATED METHODS; UNPROVABLE


    public static Customer __INIT_restorePermissions(String name, int age)
        //@ requires name != null &*& ([_](Interval(age, 14, 150))) &*& true;
        //@ ensures result != null &*& Customer_OwnFields(result, ?result_name_e, ?result_age_e) &*& Customer_FieldTypes(result_name_e, result_age_e) &*& result != null &*& AgedOver(result_age_e, age) &*& (Interval(age, 14, 150)) &*& (name != null) &*& result_name_e == name &*& result_age_e == age;
    {}
}
