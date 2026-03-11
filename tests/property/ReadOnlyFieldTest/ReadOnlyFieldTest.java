import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class ReadOnlyFieldTest {
    @Interval(min="1", max="2") int field = 1;

    // :: error: type.invalid.readonly.init
    @ReadOnly ReadOnlyFieldTest test;

    @ReadOnly @UnknownInitialization(Object.class) ReadOnlyFieldTest test2;

    // :: error: nullness.initialization.fields.uninitialized :: error: interval.initialization.fields.uninitialized
    public ReadOnlyFieldTest() {
    }

    public void fooThis(@Unique ReadOnlyFieldTest this) {
        @Interval(min="1", max="2") int x = this.test.field;
        // :: error: interval.assignment.type.incompatible
        @Interval(min="1", max="2") int y = this.test2.field;
    }
}
