package case_study;


//@ predicate Main_OwnFields(Main subject; ) = true;
//@ predicate Main_FieldTypes(; ) = true;

public final class Main  {

    
    private Main()
        //@ requires true;
        //@ ensures [_]Main_OwnFields(this) &*& [_]Main_FieldTypes();
    {
        super();

    }

    
    public static void main(String[] args)
        //@ requires args != null &*& true;
        //@ ensures args != null &*& true;
    {
        case_study.Product product18;
        case_study.Product temp0 = Product.__INIT_restorePermissions("Louisiana Buzzsaw Carnage",10,18);
        //@ assert temp0 != null &*& ([_](Product_OwnFields(temp0, ?temp0_title_a0, ?temp0_price_a0, ?temp0_ageRestriction_a0)) &*& [_](AllowedFor(temp0_ageRestriction_a0, 18)));
        product18 = temp0;
        case_study.Customer customer18;
        case_study.Customer temp1 = Customer.__INIT_restorePermissions("Alice",18);
        //@ assert temp1 != null &*& ([_](Customer_OwnFields(temp1, ?temp1_name_a1, ?temp1_age_a1)) &*& [_](AgedOver(temp1_age_a1, 18)));
        customer18 = temp1;
        case_study.Shop shop;
        case_study.Shop temp2 = Shop.__INIT_restorePermissions();
        shop = temp2;
        shop.__addOrder_restorePermissions(Order.__INIT_restorePermissions(18,customer18,product18));
        case_study.Product product6;
        case_study.Product temp3 = Product.__INIT_restorePermissions("Tim & Jeffrey, All Episodes",10,6);
        //@ assert temp3 != null &*& ([_](Product_OwnFields(temp3, ?temp3_title_a2, ?temp3_price_a2, ?temp3_ageRestriction_a2)) &*& [_](AllowedFor(temp3_ageRestriction_a2, 6)));
        product6 = temp3;
        shop.__addOrder_restorePermissions(Order.__INIT_restorePermissions(14,customer18,product6));
        case_study.Customer customer14;
        case_study.Customer temp4 = Customer.__INIT_restorePermissions("Bob",14);
        //@ assert temp4 != null &*& ([_](Customer_OwnFields(temp4, ?temp4_name_a3, ?temp4_age_a3)) &*& [_](AgedOver(temp4_age_a3, 14)));
        customer14 = temp4;
        shop.__addOrder_restorePermissions(Order.__INIT_restorePermissions(14,customer14,product6));
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
    }


// GENERATED METHODS; UNPROVABLE


    private static Main __INIT_restorePermissions()
        //@ requires true;
        //@ ensures result != null &*& Main_OwnFields(result) &*& Main_FieldTypes() &*& result != null;
    {}

    public static void __main_restorePermissions(String[] args)
        //@ requires args != null &*& true;
        //@ ensures args != null &*& true;
    {}
}
