import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class SubClass extends AnnotatedConstructorTest {

    public SubClass() {
        Packing.pack(this, SubClass.class);
    }

    // :: error: simple.inconsistent.constructor.type
    public @D SubClass(int i) {
        Packing.pack(this, SubClass.class);
    }
}