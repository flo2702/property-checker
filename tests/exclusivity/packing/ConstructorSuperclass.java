import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ConstructorSuperclass {

    @Unique Object superField;

    ConstructorSuperclass() {
        this.superField = new Obj();
        Packing.pack(this, ConstructorSuperclass.class);
    }

    @UnderInitialization(Object.class) ConstructorSuperclass(int dummy) { }
}
