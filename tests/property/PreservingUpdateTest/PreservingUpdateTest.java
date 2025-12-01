import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class PreservingUpdateTest {

    @Interval(min="1", max="2") int intField = 1;
    @NonNull Object objField = new Object();

    void preservingAliased(@MaybeAliased PreservingUpdateTest this) {
        this.intField = 2;
        this.objField = new Object();
    }

    @NonMonotonic
    void nonPreservingAliased0(@MaybeAliased PreservingUpdateTest this) {
        // :: error: interval.assignment.type.incompatible
        this.intField = 0;
    }

    @NonMonotonic
    void nonPreservingAliased1(@MaybeAliased PreservingUpdateTest this) {
        // :: error: nullness.assignment.type.incompatible
        this.objField = null;
    }
}
