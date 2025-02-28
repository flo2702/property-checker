import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ConstructorSubclass extends ConstructorSuperclass {

    @Unique Object subField;

    @NonMonotonic
    ConstructorSubclass() {
        super();
        this.isPackedToSuperclass();
        this.subField = new Obj();
    }

    @NonMonotonic
    ConstructorSubclass(int dummy) {
        super(dummy);
        this.isPackedToSuperclass();
        this.subField = new Obj();
    }

    @NonMonotonic
    void isPackedToSuperclass(@UnderInitialization(ConstructorSuperclass.class) @Unique ConstructorSubclass this) {}
}
