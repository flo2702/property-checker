import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ArraysTest {

    Object[] defaultField;
    @MaybeAliased Object @MaybeAliased [] aliasedField;

    // :: error: nullness.initialization.fields.uninitialized
    public ArraysTest() {}

    public void foo0() {
        bar(defaultField);
        bar(aliasedField);
    }

    public void foo1() {
        Object[] defaultLocal = defaultField;
        @MaybeAliased Object @MaybeAliased [] aliasedLocal = aliasedField;

        bar(defaultLocal);
        bar(aliasedLocal);
    }

    public void bar(Object[] arg) {}
}
