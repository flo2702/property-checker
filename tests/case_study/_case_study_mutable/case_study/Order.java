package case_study;

import edu.kit.kastel.property.util.Packing;
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
    }

    @JMLClause("ensures \\result == this.product.price;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getPrice(@MaybeAliased Order this) {
        return product.getPrice();
    }

    @JMLClause("ensures \\result.customer == customer && \\result.product == product && \\result.witness == 18;")
    @JMLClause("ensures \\fresh(\\result);")
    @JMLClause("assignable \\nothing;") @Pure
    public static Order order18(@AgedOver(age="18") Customer customer, @AllowedFor(age="18") Product product) {
        return new Order(18, customer, product);
    }

    @JMLClause("ensures \\result.customer == customer && \\result.product == product && \\result.witness == 14;")
    @JMLClause("ensures \\fresh(\\result);")
    @JMLClause("assignable \\nothing;") @Pure
    public static Order order14(@AgedOver(age="14") Customer customer, @AllowedFor(age="14") Product product) {
        return new Order(14, customer, product);
    }
}
