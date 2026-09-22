import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.checker.qual.*;

public class JMLContractTest {


    @JMLClause("requires arg % 2 == 0;")
    @JMLContract("""
            public exceptional_behavior
            requires arg % 2 != 0;
            signals(RuntimeException) true;
            """)
    public void foo(@C JMLContractTest this, @B int arg) {
        if (arg % 2 != 0) throw new RuntimeException();
    }
}
