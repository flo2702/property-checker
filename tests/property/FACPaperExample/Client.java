import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class Client {
    public void addAndRemove0() {
        @MinLen(len="0") List l = new List();
        l.insertFirst(1, 0);
        // error by synt type rules, but proven by SMT
        // :: error: minlen.method.invocation.invalid
        l.removeFirst(1);
        // true error
        // :: error: minlen.method.invocation.invalid
        l.removeFirst(1); // 1
    }
    public void addAndRemove1() {
        List l = new List();
        l.insertFirst(1, 0);
        // error by synt type rules, but proven by SMT
        // :: error: minlen.method.invocation.invalid
        l.insertFirst(2, 1);
        // error by synt type rules, but proven by SMT
        // :: error: minlen.method.invocation.invalid
        l.removeFirst(1);
        // true error
        // :: error: minlen.method.invocation.invalid :: error: min.argument.type.incompatible
        l.removeFirst(0); // 2
    }
}
