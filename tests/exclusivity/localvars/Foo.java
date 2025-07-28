import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class Foo {

    int i;

    Foo() {
    }

    public void mth(@ReadOnly @UnknownInitialization(Object.class) Foo this) {}

    public void mthUnique(@Unique Foo this) {}
}
