import java.util.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;

public class InvTest {

    InvTest(int defaultConstr) {}
    @Inv InvTest(long invConstr) {}
    @InvUnknown InvTest(short helperConstr) {}

    void defaultMethod() {}

    void invMethod(@Inv InvTest this) {}

    @EnsuresInv("this")
    // :: error: inv.contracts.postcondition.not.satisfied
    void helperMethodNoPre(@InvUnknown InvTest this) {}

    @EnsuresInvUnknown("this")
    void helperMethodNoPost(@Inv InvTest this) {}

    void helperMethod(@InvUnknown InvTest this) {}
}
