import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class DependentPackingTest {

    // :: error: interval.initialization.field.uninitialized
    public @Dependable @Interval(min="0", max="0") int field0;
    // :: error: interval.initialization.field.uninitialized
    public @Dependable @Interval(min="0", max="this.field0") int field1;

    @NonMonotonic
    // :: error: packing.postcondition.not.satisfied
    public void foo0(@Unique DependentPackingTest this) {
        this.field0 = 1;
        this.field0 = 0;
    }
}
