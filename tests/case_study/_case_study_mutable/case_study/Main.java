package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
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
        @AllowedFor(age="18") Product product18 = Product.product18("Louisiana Buzzsaw Carnage", 10);
        @AgedOver(age="18") Customer customer18 = Customer.customer18("Alice");
        Shop shop = new Shop();

        addOrder18(shop, customer18, product18);

        @AllowedFor(age="6") Product product6 = Product.product6("Tim & Jeffrey, All Episodes", 10);
        addOrder14(shop, customer18, product6);

        @AgedOver(age="14") Customer customer14 = Customer.customer14("Bob");
        addOrder14(shop, customer14, product6);

        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();

        shop.processNextOrder();
    }

    @JMLClauseTranslationOnly("requires \\invariant_for(shop);")
    @JMLClauseTranslationOnly("ensures \\invariant_for(shop);")
    @JMLClauseTranslationOnly("assignable shop.orders.footprint;")
    public static void addOrder18(@Unique Shop shop, @MaybeAliased @AgedOver(age="18") Customer customer, @MaybeAliased @AllowedFor(age="18") Product product) {
        shop.addOrder(Order.order18(customer, product));
        Assert.immutableFieldUnchanged("customer", "customer.age");
        Assert.immutableFieldUnchanged("product", "product.ageRestriction");
    }

    @JMLClauseTranslationOnly("requires \\invariant_for(shop);")
    @JMLClauseTranslationOnly("ensures \\invariant_for(shop);")
    @JMLClauseTranslationOnly("assignable shop.orders.footprint;")
    public static void addOrder14(@Unique Shop shop, @MaybeAliased @AgedOver(age="14") Customer customer, @MaybeAliased @AllowedFor(age="14") Product product) {
        shop.addOrder(Order.order14(customer, product));
        Assert.immutableFieldUnchanged("customer", "customer.age");
        Assert.immutableFieldUnchanged("product", "product.ageRestriction");
    }
}
