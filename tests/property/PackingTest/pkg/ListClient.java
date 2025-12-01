package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class ListClient {

    @Unique @Length(len="1") List a;
    @MaybeAliased @Length(len="1") List b;
    @Unique @Length(len="a.size") List c;

    @NonMonotonic
    // :: error: length.initialization.fields.uninitialized
    public ListClient() {
        this.a = new List(42);
        this.b = new List(42);
        this.c = new List(42);
    }

    @NonMonotonic
    // :: error: length.initialization.fields.uninitialized
    public void correctPacking(@Unique ListClient this) {
        a.insert(42, 1);
        // :: error: length.method.invocation.invalid
        c.insert(42, 1);
    }
}
