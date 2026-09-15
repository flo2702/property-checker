import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class List {
    public @Unique @Nullable @NonNullIf(cond="this.len != 0") ListNode first;
    public @Dependable @Min(min="0") int len;

    // :: error: minlen.inconsistent.constructor.type :: error: min.initialization.fields.uninitialized :: error: nonnullif.initialization.fields.uninitialized
    public @MinLen(len="0") List() {
        // :: error: nonnullif.assignment.type.incompatible
        this.first = null;
        this.len = 0;
    }

    @EnsuresMinLen(value="this", len="n+1")
    // :: error: minlen.contracts.postcondition.not.satisfied :: error: packing.postcondition.not.satisfied
    public void insertFirst(
            @Unique @MinLen(len="n") List this,
            int datum, int n) {
        ListNode node = this.first;
        // :: error: nonnullif.assignment.type.incompatible
        this.first = new ListNode(datum, node);
        // :: error: min.assignment.type.incompatible
        this.len = this.len + 1;
    }

    @EnsuresMinLen(value="this", len="n-1")
    // :: error: minlen.contracts.postcondition.not.satisfied :: error: packing.postcondition.not.satisfied
    public int removeFirst(
            @Unique @MinLen(len="n") List this,
            @Min(min="1") int n) {
        // :: error:nullness.dereference.of.nullable
        int result = this.first.datum;
        // :: error: exclusivity.assignment.type.incompatible
        this.first = this.first.next;
        // :: error: min.assignment.type.incompatible
        this.len = this.len - 1;
        return result;
    }
}
