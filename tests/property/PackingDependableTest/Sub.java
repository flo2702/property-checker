import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class Sub extends PackingDependableTest {

    public @Interval(min="this.f",max="this.f") int g;

    // :: error: interval.initialization.fields.uninitialized
    public Sub() {
        super();
        // :: error: interval.assignment.type.incompatible
        this.g = 0;
    }
}
