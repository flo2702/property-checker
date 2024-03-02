package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class Order {
    
    public final int witness;
    public final @AgedOver(age="witness") Customer customer;
    public final @AllowedFor(age="witness") Product product;

    @JMLClause("ensures this.customer == customer && this.product == product && this.witness == witness;")
    @JMLClause("assignable \\nothing;")
    // :: error: agedover.contracts.postcondition.not.satisfied :: error: allowedfor.contracts.postcondition.not.satisfied
    public Order(int witness, @AgedOver(age="witness") Customer customer, @AllowedFor(age="witness") Product product) {
        this.witness = witness;
        this.customer = customer;
        this.product = product;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Order.class);
    }

    @JMLClause("ensures \\result.customer == customer && \\result.product == product && \\result.witness == 18;")
    @JMLClause("assignable \\nothing;")
    // :: error: agedover.contracts.postcondition.not.satisfied :: error: allowedfor.contracts.postcondition.not.satisfied
    public static Order order18(@AgedOver(age="18") Customer customer, @AllowedFor(age="18") Product product) {
        // :: error: agedover.argument.type.incompatible :: error: allowedfor.argument.type.incompatible
        return new Order(18, customer, product);
    }

    @JMLClause("ensures \\result.customer == customer && \\result.product == product && \\result.witness == 14;")
    @JMLClause("assignable \\nothing;")
    // :: error: agedover.contracts.postcondition.not.satisfied :: error: allowedfor.contracts.postcondition.not.satisfied
    public static Order order14(@AgedOver(age="14") Customer customer, @AllowedFor(age="14") Product product) {
        // :: error: agedover.argument.type.incompatible :: error: allowedfor.argument.type.incompatible
        return new Order(14, customer, product);
    }
}
