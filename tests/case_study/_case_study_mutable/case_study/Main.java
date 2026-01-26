package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Main {

    @Pure
    private Main() {
    }
    
    public static void main(String[] args) {
        @NonNull @AllowedFor(age="18") Product product18 = new Product("Louisiana Buzzsaw Carnage", 10, 18);
        @NonNull @AgedOver(age="18") Customer customer18 = new Customer("Alice", 18);
        Shop shop = new Shop();

        addOrderHelper(shop, 18, customer18, product18);

        @NonNull @AllowedFor(age="6") Product product6 = new Product("Tim & Jeffrey, All Episodes", 10, 6);
        addOrderHelper(shop, 14, customer18, product6);

        @NonNull @AgedOver(age="14") Customer customer14 = new Customer("Bob", 14);
        addOrderHelper(shop, 14, customer14, product6);

        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();

        shop.processNextOrder();
    }

    @JMLClauseTranslationOnly("requires \\invariant_for(shop);")
    @JMLClauseTranslationOnly("ensures \\invariant_for(shop);")
    @JMLClauseTranslationOnly("assignable shop.orders, shop.orders.footprint;")
    // These errors are reported by the type checker, but mended by the SMT solver, so there remains nothing to be proven in KeY
    // :: error: agedover.contracts.postcondition.not.satisfied :: error: allowedfor.contracts.postcondition.not.satisfied
    public static void addOrderHelper(@Unique Shop shop, int witness, @AgedOver(age="witness") Customer customer, @AllowedFor(age="witness") Product product) {
        // :: error: agedover.argument.type.incompatible :: error: allowedfor.argument.type.incompatible
        shop.addOrder(new Order(witness, customer, product));
        Assert.immutableFieldUnchanged_TranslationOnly("customer", "customer.age");
        Assert.immutableFieldUnchanged_TranslationOnly("product", "product.ageRestriction");
    }
}
