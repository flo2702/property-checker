import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class NullnessDefaultTest {

    // :: error: initialization.static.field.uninitialized
    static @NonNull Object staticNonNullField;
    static @Nullable Object staticNullableField;
    static @MonotonicNonNull Object staticMonotonicNonNullField;
    // :: error: initialization.static.field.uninitialized
    static Object staticDefaultField;

    // :: error: nullness.initialization.field.uninitialized
    @NonNull Object nonNullField;
    @Nullable Object nullableField;
    @MonotonicNonNull Object monotonicNonNullField;
    // :: error: nullness.initialization.field.uninitialized
    Object defaultField;
    
    // :: error: nullness.initialization.field.uninitialized
    @ReadOnly @UnknownInitialization(Object.class) @NonNull Object nonNullField0;
    // :: error: nullness.initialization.field.uninitialized
    @ReadOnly @UnknownInitialization(Object.class) Object defaultField0;

    public void foo() {
        @NonNull Object nonNullLocal = nonNullField;
        nonNullLocal = defaultField;
        // :: error: nullness.assignment.type.incompatible
        nonNullLocal = nullableField;
        
        @Nullable Object nullableLocal = nonNullField;
        nullableLocal = defaultField;
        nullableLocal = nullableField;
        
        Object defaultLocal = nonNullField;
        defaultLocal = defaultField;
        defaultLocal = nullableField;
    }

    public void validParam0(@NonNull Object arg) {}
    public void validParam1(Object arg) {}

    public void invalidParam0(@ReadOnly @UnknownInitialization(Object.class) @NonNull Object arg) {}
    public void invalidParam1(@ReadOnly @UnknownInitialization(Object.class) Object arg) {}
}
