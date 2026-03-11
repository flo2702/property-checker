package case_study;


public final class Product  {

    //@ public invariant_free packed <: case_study.Product ==> title.packed == \typeof(title);
    //@ public invariant_free \invariant_free_for(title);
    //@ public invariant_free packed <: case_study.Product ==> ((true) && (title != null));
    //@ public invariant_free packed <: case_study.Product ==> ((0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647));
    //@ public invariant_free packed <: case_study.Product ==> ((0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18));

    public /*@nullable@*/ java.lang.String title;

    public int price;

    public int ageRestriction;

    
    /*@ public normal_behavior
      @ requires (true) && (title != null);
      @ requires (0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647);
      @ requires (0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18);
      @ requires_free this.packed == \typeof(this);
      @ requires_free title.packed == \typeof(title);
      @ ensures (ageRestriction >= 0) && (this != null && this.ageRestriction <= ageRestriction);
      @ ensures this.title == title && this.price == price && this.ageRestriction == ageRestriction;
      @ ensures_free title.packed == \typeof(title);
      @ ensures (true) && (this != null);
      @ ensures (ageRestriction >= 0) && (this != null && this.ageRestriction <= ageRestriction);
      @ ensures (0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647);
      @ ensures (0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Product(/*@nullable@*/ java.lang.String title, int price, int ageRestriction) {
        super();

        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
        ;
        ;
        ;
        ;
    }

    /*@ public normal_behavior
      @ requires title_nullness || ((true) && (title != null));
      @ requires price_interval || ((0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647));
      @ requires ageRestriction_interval || ((0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18));
      @ requires_free !title_nullness || ((true) && (title != null));
      @ requires_free !price_interval || ((0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647));
      @ requires_free !ageRestriction_interval || ((0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.title == title && \result.price == price && \result.ageRestriction == ageRestriction;
      @ ensures_free title.packed == \typeof(title);
      @ ensures (true) && (\result != null);
      @ ensures (ageRestriction >= 0) && (\result != null && \result.ageRestriction <= ageRestriction);
      @ ensures (ageRestriction >= 0) && (\result != null && \result.ageRestriction <= ageRestriction);
      @ ensures (0 >= 0 && 0 <= 2147483647) && (price >= 0 && price <= 2147483647);
      @ ensures (0 >= 0 && 0 <= 18) && (ageRestriction >= 0 && ageRestriction <= 18);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Product __INIT_trampoline(/*@nullable@*/ java.lang.String title, int price, int ageRestriction, boolean title_nullness, boolean price_interval, boolean ageRestriction_interval) {
        return new case_study.Product(title, price, ageRestriction);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures \result == this.price;
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public int getPrice() {
        return price;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.price;
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public  int __getPrice_trampoline(boolean this_nullness) {
        return getPrice();
    }

}
