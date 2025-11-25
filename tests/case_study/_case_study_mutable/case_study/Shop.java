package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClauseTranslationOnly("public accessible \\inv: this.orders, this.orders.footprint;")
@JMLClauseTranslationOnly("public invariant this.orders != null ==> \\invariant_for(this.orders);")
@JMLClauseTranslationOnly("public invariant this.orders != null ==> \\disjoint(this.*, this.orders.footprint);")
public final class Shop {
    
    private @Unique @PossiblyEmpty @Inv SortedList orders;

    @JMLClauseTranslationOnly("assignable \\nothing;") @Pure
    public Shop() {
        this.orders = new SortedList();
    }

    @JMLClauseTranslationOnly("assignable this.orders.footprint;")
    public void addOrder(@Unique Shop this, Order order) {
        this.orders.insert(order);
    }

    @JMLClauseTranslationOnly("assignable this.orders.footprint, this.orders.first.packed;")
    public boolean processNextOrder(@Unique Shop this) {
        Order result = this.orders.removeIfPresent();
        return result != null;
    }
}
