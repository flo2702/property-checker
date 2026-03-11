package case_study;


public final class Order  {

    //@ public invariant_free packed <: case_study.Order ==> customer.packed == \typeof(customer);
    //@ public invariant_free \invariant_free_for(customer);
    //@ public invariant_free packed <: case_study.Order ==> product.packed == \typeof(product);
    //@ public invariant_free \invariant_free_for(product);
    //@ public invariant_free packed <: case_study.Order ==> ((true) && (customer != null));
    //@ public invariant_free packed <: case_study.Order ==> ((true) && (product != null));
    //@ public invariant_free packed <: case_study.Order ==> ((witness >= 0) && (customer != null && customer.age >= witness));
    //@ public invariant_free packed <: case_study.Order ==> ((witness >= 0) && (product != null && product.ageRestriction <= witness));

    public int witness;

    public /*@nullable@*/ case_study.Customer customer;

    public /*@nullable@*/ case_study.Product product;

    
    /*@ public normal_behavior
      @ requires (true) && (customer != null);
      @ requires (true) && (product != null);
      @ requires (witness >= 0) && (customer != null && customer.age >= witness);
      @ requires (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @ requires_free this.packed == \typeof(this);
      @ requires_free customer.packed == \typeof(customer);
      @ requires_free product.packed == \typeof(product);
      @ ensures this.customer == customer && this.product == product && this.witness == witness;
      @ ensures_free customer.packed == \typeof(customer);
      @ ensures_free product.packed == \typeof(product);
      @ ensures (true) && (this != null);
      @ ensures (witness >= 0) && (customer != null && customer.age >= witness);
      @ ensures (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Order(int witness, /*@nullable@*/ case_study.Customer customer, /*@nullable@*/ case_study.Product product) {
        super();

        this.witness = witness;
        this.customer = customer;
        this.product = product;
        ;
        ;
        ;
        ;
    }

    /*@ public normal_behavior
      @ requires customer_nullness || ((true) && (customer != null));
      @ requires product_nullness || ((true) && (product != null));
      @ requires customer_agedover || ((witness >= 0) && (customer != null && customer.age >= witness));
      @ requires product_allowedfor || ((witness >= 0) && (product != null && product.ageRestriction <= witness));
      @ requires_free !customer_nullness || ((true) && (customer != null));
      @ requires_free !product_nullness || ((true) && (product != null));
      @ requires_free !customer_agedover || ((witness >= 0) && (customer != null && customer.age >= witness));
      @ requires_free !product_allowedfor || ((witness >= 0) && (product != null && product.ageRestriction <= witness));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.customer == customer && \result.product == product && \result.witness == witness;
      @ ensures_free customer.packed == \typeof(customer);
      @ ensures_free product.packed == \typeof(product);
      @ ensures (true) && (\result != null);
      @ ensures (witness >= 0) && (customer != null && customer.age >= witness);
      @ ensures (witness >= 0) && (product != null && product.ageRestriction <= witness);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Order __INIT_trampoline(int witness, /*@nullable@*/ case_study.Customer customer, /*@nullable@*/ case_study.Product product, boolean customer_nullness, boolean product_nullness, boolean customer_agedover, boolean product_allowedfor) {
        return new case_study.Order(witness, customer, product);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ ensures \result == this.product.price;
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public int getPrice() {
        return product.__getPrice_trampoline(false);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures \result == this.product.price;
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @ assignable \strictly_nothing;
      @*/
    public  int __getPrice_trampoline(boolean this_nullness) {
        return getPrice();
    }

}
