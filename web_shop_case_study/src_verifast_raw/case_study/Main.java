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

    
    public static void mainVerifast(String[] args)
        //@ requires args != null &*& true;
        //@ ensures (args != null);
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

    
    public static void main(String[] args)
        //@ requires args != null &*& true;
        //@ ensures (args != null);
    {
        case_study.Product product18;
        case_study.Product temp5 = Product.__INIT_restorePermissions("Louisiana Buzzsaw Carnage",10,18);
        //@ assert temp5 != null &*& ([_](Product_OwnFields(temp5, ?temp5_title_a4, ?temp5_price_a4, ?temp5_ageRestriction_a4)) &*& [_](AllowedFor(temp5_ageRestriction_a4, 18)));
        product18 = temp5;
        case_study.Customer customer18;
        case_study.Customer temp6 = Customer.__INIT_restorePermissions("Alice",18);
        //@ assert temp6 != null &*& ([_](Customer_OwnFields(temp6, ?temp6_name_a5, ?temp6_age_a5)) &*& [_](AgedOver(temp6_age_a5, 18)));
        customer18 = temp6;
        case_study.Shop shop;
        case_study.Shop temp7 = Shop.__INIT_restorePermissions();
        shop = temp7;
        __addOrderHelper_restorePermissions(shop, 18, customer18, product18);
        case_study.Product product6;
        case_study.Product temp8 = Product.__INIT_restorePermissions("Tim & Jeffrey, All Episodes",10,6);
        //@ assert temp8 != null &*& ([_](Product_OwnFields(temp8, ?temp8_title_a6, ?temp8_price_a6, ?temp8_ageRestriction_a6)) &*& [_](AllowedFor(temp8_ageRestriction_a6, 6)));
        product6 = temp8;
        __addOrderHelper_restorePermissions(shop, 14, customer18, product6);
        case_study.Customer customer14;
        case_study.Customer temp9 = Customer.__INIT_restorePermissions("Bob",14);
        //@ assert temp9 != null &*& ([_](Customer_OwnFields(temp9, ?temp9_name_a7, ?temp9_age_a7)) &*& [_](AgedOver(temp9_age_a7, 14)));
        customer14 = temp9;
        __addOrderHelper_restorePermissions(shop, 14, customer14, product6);
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
        shop.__processNextOrder_restorePermissions();
    }

    
    public static void addOrderHelper(Shop shop, int witness, Customer customer, Product product)
        //@ requires shop != null &*& customer != null &*& product != null &*& (Customer_OwnFields(customer, ?customer_name_r, ?customer_age_r) &*& Customer_FieldTypes(customer_name_r, customer_age_r) &*& AgedOver(customer_age_r, witness)) &*& (Product_OwnFields(product, ?product_title_r, ?product_price_r, ?product_ageRestriction_r) &*& Product_FieldTypes(product_title_r, product_price_r, product_ageRestriction_r) &*& AllowedFor(product_ageRestriction_r, witness)) &*& (Shop_OwnFields(shop, ?shop_orders_r) &*& Shop_FieldTypes(shop_orders_r)) &*& true;
        //@ ensures ([_](Customer_OwnFields(customer, ?customer_name_e, ?customer_age_e)) &*& [_](Customer_FieldTypes(customer_name_e, customer_age_e)) &*& customer != null &*& [_](AgedOver(customer_age_e, witness))) &*& ([_](Product_OwnFields(product, ?product_title_e, ?product_price_e, ?product_ageRestriction_e)) &*& [_](Product_FieldTypes(product_title_e, product_price_e, product_ageRestriction_e)) &*& product != null &*& [_](AllowedFor(product_ageRestriction_e, witness))) &*& ([_](Shop_OwnFields(shop, ?shop_orders_e)) &*& [_](Shop_FieldTypes(shop_orders_e)) &*& shop != null) &*& true;
    {
        shop.__addOrder_restorePermissions(Order.__INIT_restorePermissions(witness,customer,product));
        ;
        ;
    }


// GENERATED METHODS; UNPROVABLE


    private static Main __INIT_restorePermissions()
        //@ requires true;
        //@ ensures result != null &*& Main_OwnFields(result) &*& Main_FieldTypes() &*& result != null;
    {}

    public static void __mainVerifast_restorePermissions(String[] args)
        //@ requires args != null &*& true;
        //@ ensures (args != null);
    {}

    public static void __main_restorePermissions(String[] args)
        //@ requires args != null &*& true;
        //@ ensures (args != null);
    {}

    public static void __addOrderHelper_restorePermissions(Shop shop, int witness, Customer customer, Product product)
        //@ requires shop != null &*& customer != null &*& product != null &*& ([_](Customer_OwnFields(customer, ?customer_name_r, ?customer_age_r)) &*& [_](Customer_FieldTypes(customer_name_r, customer_age_r)) &*& [_](AgedOver(customer_age_r, witness))) &*& ([_](Product_OwnFields(product, ?product_title_r, ?product_price_r, ?product_ageRestriction_r)) &*& [_](Product_FieldTypes(product_title_r, product_price_r, product_ageRestriction_r)) &*& [_](AllowedFor(product_ageRestriction_r, witness))) &*& ([_](Shop_OwnFields(shop, ?shop_orders_r)) &*& [_](Shop_FieldTypes(shop_orders_r))) &*& true;
        //@ ensures (Customer_OwnFields(customer, ?customer_name_e, ?customer_age_e) &*& Customer_FieldTypes(customer_name_e, customer_age_e) &*& customer != null &*& AgedOver(customer_age_e, witness)) &*& (Product_OwnFields(product, ?product_title_e, ?product_price_e, ?product_ageRestriction_e) &*& Product_FieldTypes(product_title_e, product_price_e, product_ageRestriction_e) &*& product != null &*& AllowedFor(product_ageRestriction_e, witness)) &*& (Shop_OwnFields(shop, ?shop_orders_e) &*& Shop_FieldTypes(shop_orders_e) &*& shop != null) &*& true;
    {}
}
