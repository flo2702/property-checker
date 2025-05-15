import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class MutateOtherObjects {

    // :: error: initialization.field.uninitialized
    @Dependable @Unique Foo foo;

    @NonMonotonic
    void mutate(@Unique MutateOtherObjects this, @Unique MutateOtherObjects other) {
        this.foo = new Foo();

        // :: error: initialization.assignment.invalid-lhs :: error: packing.assignment.to.dependable
        this.foo.i = 42;
        // :: error: initialization.assignment.invalid-lhs :: error: packing.assignment.to.dependable
        other.foo = new Foo();
    }
}
