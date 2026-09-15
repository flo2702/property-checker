import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;

public class ArrayTest {

    int @Dependable @Unique [] field = new int[32];

    public void uniqueReceiver(@Unique ArrayTest this) {
        int @Unique [] local = new int[32];

        this.field[0] = 0;
        local[0] = 0;

        int @MaybeAliased [] alias = this.field;
        // :: error: initialization.write.aliased.array
        this.field[0] = 0;
        alias = local;
        local[0] = 0;

        this.field = new int[32];
        this.field[0] = 0;
    }

    public void aliasedReceiver(@MaybeAliased ArrayTest this) {
        int @Unique [] local = new int[32];
        local[0] = 0;

        // :: error: initialization.write.aliased.array
        this.field[0] = 0;
    }
}
