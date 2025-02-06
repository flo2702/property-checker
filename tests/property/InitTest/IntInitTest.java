import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class IntInitTest {
    
    int unannotated;
    @Remainder(remainder="0", modulus="2") int even;
    @Remainder(remainder="1", modulus="2") int odd;
    
    public IntInitTest() {
        this.helper();
        
        even = 2;
        odd = 1;
        
        // :: error: packing.method.invocation.invalid
        this.nonHelper();
    }

    public @Remainder(remainder="0", modulus="2") int helper(@Unique @UnknownInitialization IntInitTest this) {
    	// :: error: remainder.return.type.incompatible :: error: packing.return.type.incompatible
        return this.even;
    }

    public @Remainder(remainder="0", modulus="2") int nonHelper(@Unique @Initialized IntInitTest this) {
    	return this.even;
    }
}
