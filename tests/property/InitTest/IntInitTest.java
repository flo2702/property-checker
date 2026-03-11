import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class IntInitTest {
    
    int unannotated;
    @Remainder(remainder="0", modulus="2") int even;
    @Remainder(remainder="1", modulus="2") int odd;

    @NonMonotonic
    public IntInitTest() {
        this.helper();
        
        this.even = 2;
        this.odd = 1;
        
        // :: error: remainder.initialization.fields.uninitialized
        this.nonHelper();
    }

    @NonMonotonic
    public @Remainder(remainder="0", modulus="2") int helper(@Unique @UnderInitialization IntInitTest this) {
    	// :: error: remainder.return.type.incompatible
        return this.even;
    }

    @NonMonotonic
    public @Remainder(remainder="0", modulus="2") int nonHelper(@Unique @Initialized IntInitTest this) {
    	return this.even;
    }
}
