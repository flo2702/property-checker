import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class InitializationFinalClass {

    @ReadOnly @UnknownInitialization(Object.class) @Nullable Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    @NonMonotonic
    InitializationFinalClass() {
        this.unique = new Obj();
        // :: error: nullness.initialization.fields.uninitialized
        this.foo();
    }

    @NonMonotonic
    InitializationFinalClass(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();

        this.foo();
    }

    @Pure
    void foo(@Unique InitializationFinalClass this) {}
}
