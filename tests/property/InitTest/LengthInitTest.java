import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public abstract class LengthInitTest {
    
    public @MaybeAliased @Length(len="1") List i2;
    public @MaybeAliased @Length(len="1") List i3;
    public @MaybeAliased @Length(len="2") List i4;

    // :: error: nullness.initialization.fields.uninitialized :: error: length.initialization.fields.uninitialized
    public LengthInitTest(@MaybeAliased @Length(len="1") List arg) {
        this.i2 = arg;
        this.i3 = arg;

        @Length(len="1") List l3 = arg;
    }

    // :: error: length.initialization.fields.uninitialized
    public LengthInitTest(@MaybeAliased @Length(len="1") List arg, int dummy) {
        this.i2 = arg;
        this.i3 = arg;
        // :: error: length.assignment.type.incompatible
        this.i4 = arg;

        // :: error: length.assignment.type.incompatible
        @Length(len="2") List l3 = arg;
    }
}
