import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ExceptionTest {

    public @Unique Object field;

    public ExceptionTest() {
        field = new Object();
        Packing.pack(this, ExceptionTest.class);
    }

    public void foo() {}

    public static void main() {
        ExceptionTest obj = new ExceptionTest();
        try {
            obj.foo();
        } catch (Exception e) {
            // :: error: exclusivity.type.invalidated :: error: method.call.incompatible
            obj.foo();
        }
    }
}