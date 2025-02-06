import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class Assign {

    // :: error: initialization.field.uninitialized
    @Unique Foo foo;

    void assignWritableThis(@Unique Assign this) {
        this.foo = new Foo();
    }

    void assignParam(@Unique Assign this, @Unique Assign other) {
        // :: error: assignment.parameter
        other = new Assign();
    }
}
