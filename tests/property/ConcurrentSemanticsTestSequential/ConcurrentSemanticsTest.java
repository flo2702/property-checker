import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

// Duplicate of ConcurrentSemanticsTest with sequential semantics

public final class ConcurrentSemanticsTest {

    public int intField;
    public @Nullable Object objField;

    @EnsuresMaybeAliased(value="this")
    public void leakThis(@Unique @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {}

    // this is aliased; thus another thread may write the field

    public @Interval(min="2", max="2") int aliasedInt(@MaybeAliased @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        @Interval(min="2", max="2") int temp = 2;
        this.intField = temp;
        //// :: error: interval.return.type.incompatible
        return intField;
    }
    public @NonNull Object aliasedObj(@MaybeAliased @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        this.objField = new Object();
        //// :: error: nullness.return.type.incompatible :: error: packing.return.type.incompatible
        return objField;
    }

    // this is unique and becomes aliased; thus another thread may write the field

    @EnsuresMaybeAliased(value="this")
    public @Interval(min="2", max="2") int aliasedLaterInt(@Unique @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        @Interval(min="2", max="2") int temp = 2;
        this.intField = temp;
        this.leakThis();
        // :: error: interval.return.type.incompatible
        return intField;
    }
    @EnsuresMaybeAliased(value="this")
    public @NonNull Object aliasedLaterObj(@Unique @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        this.objField = new Object();
        this.leakThis();
        // :: error: nullness.return.type.incompatible :: error: packing.return.type.incompatible
        return objField;
    }

    // this remains unique; thus the field cannot be written by another thread

    public @Interval(min="2", max="2") int uniqueInt(@Unique @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        @Interval(min="2", max="2") int temp = 2;
        this.intField = temp;
        return intField;
    }
    public @NonNull Object uniqueObj(@Unique @UnknownInitialization(Object.class) ConcurrentSemanticsTest this) {
        this.objField = new Object();

        // TODO This error is a false positive, but fixing requires
        //  either introducing a circular dependency between the packing and uniqueness checkers
        //  or adding a feature to the uniqueness checker to restrict borrowings of "this" similar to the formalization
        //  in the paper.
        //// :: error: packing.return.type.incompatible
        return objField;
    }
}
