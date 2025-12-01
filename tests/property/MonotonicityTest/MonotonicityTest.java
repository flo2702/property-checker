import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class MonotonicityTest {

    @NonNull Object field0;
    @NonNull Object field1;

    MonotonicityTest() {
        this.field0 = new Object();
        this.monotonic();
        this.field1 = new Object();
    }

    @NonMonotonic
    // :: error: nullness.initialization.fields.uninitialized
    MonotonicityTest(int dummy) {
        this.field0 = new Object();
        this.nonMonotonic();
        this.field1 = new Object();
    }

    void monotonic(@UnderInitialization(Object.class) @Unique MonotonicityTest this) {
        this.field0 = new Object();
        // :: error: nullness.assignment.type.incompatible
        this.field0 = null;
        // :: error: initialization.nonmonotonic.method.call
        this.nonMonotonic();
    }

    @NonMonotonic
    void nonMonotonic(@UnderInitialization(Object.class) @Unique MonotonicityTest this) {
        this.field0 = null;
    }
}
