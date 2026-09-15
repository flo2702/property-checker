import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;

public class ArrayTest {

    // :: error: simple.assignment.type.incompatible
    int @Dependable @B @Unique [] field = new int[32];

    // :: error: simple.initialization.fields.uninitialized
    public void uniqueReceiver1(@Unique ArrayTest this) {
        int @Unique [] local = new int[32];

        this.field[0] = 0;
        local[0] = 0;

        int @MaybeAliased [] alias = this.field;
        // :: error: initialization.write.aliased.array
        this.field[0] = 0;
        alias = local;
        local[0] = 0;

        // :: error: simple.assignment.type.incompatible
        this.field = new int[32];
        this.field[0] = 0;
    }

    // :: error: simple.initialization.fields.uninitialized
    public void uniqueReceiver2(@Unique ArrayTest this) {
        this.field[0] = 0;
    }

    public void aliasedReceiver(@MaybeAliased ArrayTest this) {
        int @Unique [] local = new int[32];
        local[0] = 0;

        // :: error: initialization.write.aliased.array
        this.field[0] = 0;
    }
}
