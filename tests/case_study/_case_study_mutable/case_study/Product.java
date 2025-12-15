package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Product {
    
    public final String title;
    public final @Interval(min="0", max="2147483647") int price;
    public final @Dependable @Interval(min="0", max="18") int ageRestriction;

    @VerifastEnsuresClause("this_title_e == title &*& this_price_e == price &*& this_ageRestriction_e == ageRestriction")
    @JMLClause("ensures this.title == title && this.price == price && this.ageRestriction == ageRestriction;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: allowedfor.inconsistent.constructor.type
    public @AllowedFor(age="ageRestriction") Product(
            String title,
            @Interval(min="0", max="2147483647") int price,
            @Interval(min="0", max="18") int ageRestriction) {
        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
    }

    @VerifastEnsuresClause("[_](this.price |-> result)")
    @JMLClause("ensures \\result == this.price;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getPrice(@MaybeAliased Product this) {
        return price;
    }
}
