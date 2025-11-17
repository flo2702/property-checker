import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class PackingDependableTest {

    public @Dependable int f;

    public PackingDependableTest() {
        this.f = 0;
    }

    @NonMonotonic
    // :: error: packing.postcondition.not.satisfied
    public void foo(@Unique PackingDependableTest this) {
        this.f = 1;
    }
}
