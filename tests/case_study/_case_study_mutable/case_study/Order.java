package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Order {
    
    public final @Dependable int witness;
    public final @AgedOver(age="witness") Customer customer;
    public final @AllowedFor(age="witness") Product product;

    @VerifastEnsuresClause("this_customer_e == customer &*& this_product_e == product &*& this_witness_e == witness")
    @JMLClause("ensures this.customer == customer && this.product == product && this.witness == witness;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: agedover.initialization.fields.uninitialized :: error: allowedfor.initialization.fields.uninitialized
    // :: error: agedover.contracts.postcondition.not.satisfied :: error: allowedfor.contracts.postcondition.not.satisfied
    public Order(int witness, @AgedOver(age="witness") Customer customer, @AllowedFor(age="witness") Product product) {
        this.witness = witness;
        // :: error: agedover.assignment.type.incompatible
        this.customer = customer;
        // :: error: allowedfor.assignment.type.incompatible
        this.product = product;

        // Why is this necessary?
        Assert._verifast_open_translationOnly("AgedOver(customer_age_r, witness)");
        Assert._verifast_close_translationOnly("AgedOver(customer_age_r, witness)");
        Assert._verifast_open_translationOnly("AllowedFor(product_ageRestriction_r, witness)");
        Assert._verifast_close_translationOnly("AllowedFor(product_ageRestriction_r, witness)");
    }

    @VerifastSuppressTranslatedContract
    @VerifastRequiresClause("[?frac0](this.product |-> ?this_product_r) &*& [?frac1](this_product_r.price |-> ?this_product_price_r)")
    @VerifastEnsuresClause("[frac0](this.product |-> this_product_r) &*& [frac1](this_product_r.price |-> this_product_price_r)")
    @VerifastEnsuresClause("this_product_price_r == result")
    @JMLClause("ensures \\result == this.product.price;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getPrice(@MaybeAliased Order this) {
        return product.getPrice();
    }
}
