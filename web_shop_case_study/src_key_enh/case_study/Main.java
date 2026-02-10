package case_study;


public final class Main  {


    
    /*@ private normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures_free (true) && (this != null);
      @ assignable \nothing;
      @*/
    private Main() {
        super();

    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Main __INIT_trampoline() {
        return new case_study.Main();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (args != null);
      @ requires_free args.packed == \typeof(args);
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static void mainVerifast(/*@nullable@*/ java.lang.String[] args) {
        case_study.Product product18;
        case_study.Product temp0 = Product.__INIT_trampoline("Louisiana Buzzsaw Carnage",10,18, true, true, true);
        //@ assume (true) && (temp0 != null);
        //@ assume (18 >= 0) && (temp0 != null && temp0.ageRestriction <= 18);
        product18 = temp0;
        case_study.Customer customer18;
        case_study.Customer temp1 = Customer.__INIT_trampoline("Alice",18, true, true);
        //@ assume (true) && (temp1 != null);
        //@ assume (18 >= 0) && (temp1 != null && temp1.age >= 18);
        customer18 = temp1;
        case_study.Shop shop;
        case_study.Shop temp2 = Shop.__INIT_trampoline();
        shop = temp2;
        shop.__addOrder_trampoline(Order.__INIT_trampoline(18,customer18,product18, true, true, true, true), true, true);
        case_study.Product product6;
        case_study.Product temp3 = Product.__INIT_trampoline("Tim & Jeffrey, All Episodes",10,6, true, true, true);
        //@ assume (true) && (temp3 != null);
        //@ assume (6 >= 0) && (temp3 != null && temp3.ageRestriction <= 6);
        product6 = temp3;
        shop.__addOrder_trampoline(Order.__INIT_trampoline(14,customer18,product6, true, true, true, true), true, true);
        case_study.Customer customer14;
        case_study.Customer temp4 = Customer.__INIT_trampoline("Bob",14, true, true);
        //@ assume (true) && (temp4 != null);
        //@ assume (14 >= 0) && (temp4 != null && temp4.age >= 14);
        customer14 = temp4;
        shop.__addOrder_trampoline(Order.__INIT_trampoline(14,customer14,product6, true, true, true, true), true, true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
    }

    /*@ public normal_behavior
      @ requires args_nullness || ((true) && (args != null));
      @ requires_free !args_nullness || ((true) && (args != null));
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static void __mainVerifast_trampoline(/*@nullable@*/ java.lang.String[] args, boolean args_nullness) {
        mainVerifast(args);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (args != null);
      @ requires_free args.packed == \typeof(args);
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static void main(/*@nullable@*/ java.lang.String[] args) {
        case_study.Product product18;
        case_study.Product temp5 = Product.__INIT_trampoline("Louisiana Buzzsaw Carnage",10,18, true, true, true);
        //@ assume (true) && (temp5 != null);
        //@ assume (18 >= 0) && (temp5 != null && temp5.ageRestriction <= 18);
        product18 = temp5;
        case_study.Customer customer18;
        case_study.Customer temp6 = Customer.__INIT_trampoline("Alice",18, true, true);
        //@ assume (true) && (temp6 != null);
        //@ assume (18 >= 0) && (temp6 != null && temp6.age >= 18);
        customer18 = temp6;
        case_study.Shop shop;
        case_study.Shop temp7 = Shop.__INIT_trampoline();
        shop = temp7;
        __addOrderHelper_trampoline(shop, 18, customer18, product18, true, true, true, true, true);
        case_study.Product product6;
        case_study.Product temp8 = Product.__INIT_trampoline("Tim & Jeffrey, All Episodes",10,6, true, true, true);
        //@ assume (true) && (temp8 != null);
        //@ assume (6 >= 0) && (temp8 != null && temp8.ageRestriction <= 6);
        product6 = temp8;
        __addOrderHelper_trampoline(shop, 14, customer18, product6, true, true, true, true, true);
        case_study.Customer customer14;
        case_study.Customer temp9 = Customer.__INIT_trampoline("Bob",14, true, true);
        //@ assume (true) && (temp9 != null);
        //@ assume (14 >= 0) && (temp9 != null && temp9.age >= 14);
        customer14 = temp9;
        __addOrderHelper_trampoline(shop, 14, customer14, product6, true, true, true, true, true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
        shop.__processNextOrder_trampoline(true);
    }

    /*@ public normal_behavior
      @ requires args_nullness || ((true) && (args != null));
      @ requires_free !args_nullness || ((true) && (args != null));
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static void __main_trampoline(/*@nullable@*/ java.lang.String[] args, boolean args_nullness) {
        main(args);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (shop != null);
      @ requires (true) && (customer != null);
      @ requires (true) && (product != null);
      @ requires (witness >= 0) && (customer != null && customer.age >= witness);
      @ requires (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @ requires_free shop.packed == \typeof(shop);
      @ requires_free customer.packed == \typeof(customer);
      @ requires_free product.packed == \typeof(product);
      @ requires_free shop != customer && shop != product;
      @ ensures_free shop.packed == \typeof(shop);
      @ ensures_free customer.packed == \typeof(customer);
      @ ensures_free product.packed == \typeof(product);
      @ ensures_free (witness >= 0) && (customer != null && customer.age >= witness);
      @ ensures_free (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @*/
    public static void addOrderHelper(/*@nullable@*/ case_study.Shop shop, int witness, /*@nullable@*/ case_study.Customer customer, /*@nullable@*/ case_study.Product product) {
        shop.__addOrder_trampoline(Order.__INIT_trampoline(witness,customer,product, true, true, true, true), true, true);
        ;
        ;
    }

    /*@ public normal_behavior
      @ requires shop_nullness || ((true) && (shop != null));
      @ requires customer_nullness || ((true) && (customer != null));
      @ requires product_nullness || ((true) && (product != null));
      @ requires customer_agedover || ((witness >= 0) && (customer != null && customer.age >= witness));
      @ requires product_allowedfor || ((witness >= 0) && (product != null && product.ageRestriction <= witness));
      @ requires_free !shop_nullness || ((true) && (shop != null));
      @ requires_free !customer_nullness || ((true) && (customer != null));
      @ requires_free !product_nullness || ((true) && (product != null));
      @ requires_free !customer_agedover || ((witness >= 0) && (customer != null && customer.age >= witness));
      @ requires_free !product_allowedfor || ((witness >= 0) && (product != null && product.ageRestriction <= witness));
      @ ensures_free shop.packed == \typeof(shop);
      @ ensures_free customer.packed == \typeof(customer);
      @ ensures_free product.packed == \typeof(product);
      @ ensures_free (witness >= 0) && (customer != null && customer.age >= witness);
      @ ensures_free (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @*/
    public static void __addOrderHelper_trampoline(/*@nullable@*/ case_study.Shop shop, int witness, /*@nullable@*/ case_study.Customer customer, /*@nullable@*/ case_study.Product product, boolean shop_nullness, boolean customer_nullness, boolean product_nullness, boolean customer_agedover, boolean product_allowedfor) {
        addOrderHelper(shop, witness, customer, product);
    }

}
