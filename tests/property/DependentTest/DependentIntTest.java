import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class DependentIntTest {
    
    public static final @Dependable int MIN = 1, MAX = 1;

    // :: error: interval.initialization.field.uninitialized
    public @Dependable @Interval(min="MIN", max="MAX") int field;

    public static void foo0(@Interval(min="2", max="2") int arg0, @Interval(min="2", max="5") int arg1) {
        // :: error: interval.assignment.type.incompatible
        @Interval(min="MIN", max="MAX") int x = new DependentIntTest().field;
        
        // :: error: interval.assignment.type.incompatible
        @Interval(min="1", max="1 + 2") int l0 = arg0;
        @Interval(min="1", max="5") int l1 = arg1;
        
        final int MAX = 5;
        // :: error: interval.assignment.type.incompatible
        @Interval(min="1", max="MAX") int l2 = arg1;
        
        // :: error: interval.assignment.type.incompatible
        l0 = l2;
    }
}
