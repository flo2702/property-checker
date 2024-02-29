import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public class LengthWFTest {
    
    @Length(len="1") List wellFormed0;
    @Length(len="1") List wellFormed1;
    
    // :: error: type.invalid
    @Length(len="1") List malFormed0;
    
    // :: error: type.invalid
    @Length(len="1") String malFormed1;

    public LengthWFTest() {
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, LengthWFTest.class);
    }
}
