import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Constructor {

    @ReadOnly @UnknownInitialization(Object.class) @Nullable Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    @NonMonotonic
    // :: error: nullness.initialization.fields.uninitialized
    public Constructor() { }

    @NonMonotonic
    // :: error: nullness.initialization.fields.uninitialized
    public @UnknownInitialization(Constructor.class) Constructor(short dummy) {
    }

    @NonMonotonic
    public @UnknownInitialization(Object.class) Constructor(long dummy) {
    }

    @NonMonotonic
    public Constructor(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();
    }

    @NonMonotonic
    public void foo(Constructor this) {}

    @NonMonotonic
    public static void main() {
        new Constructor().foo();
        // not invalid because Constructor class is final
        new Constructor((short)0).foo();
        // :: error: packing.method.invocation.invalid
        new Constructor((long)0).foo();
        new Constructor(0).foo();
    }
}
