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

        shop.addOrder(new Order(18, customer18, product18));

        @NonNull @AllowedFor(age="6") Product product6 = new Product("Tim & Jeffrey, All Episodes", 10, 6);
        shop.addOrder(new Order(14, customer18, product6));

        @NonNull @AgedOver(age="14") Customer customer14 = new Customer("Bob", 14);
        shop.addOrder(new Order(14, customer14, product6));

        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();

        shop.processNextOrder();
    }
}
