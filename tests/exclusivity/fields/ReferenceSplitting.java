import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class ReferenceSplitting {

    // :: error: nullness.initialization.field.uninitialized
    @Unique Foo field;

    // :: error: exclusivity.initialization.fields.uninitialized
    void refTransfer(@Unique ReferenceSplitting this) {
        @ReadOnly @Nullable Foo x;
        @Unique @Nullable Foo a;

        x = new Foo();  // x is updated to @Unique
        a = x;          // x is updated to @ReadOnly
        // :: error: exclusivity.assignment.type.incompatible
        this.field = x; // invalid, x is not @Unique anymore
    }
}
