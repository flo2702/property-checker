import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class BasicPackingB extends BasicPackingA {

    @Unique Object bField;

    BasicPackingB() {
        this.bField = new Obj();
    }

    @Pure
    void isUnpacked(@Unique @UnderInitialization(Object.class) BasicPackingB this) {}

    @Pure
    void isPackedToA(@Unique @UnderInitialization(BasicPackingA.class) BasicPackingB this) {}

    @Pure
    void isPackedToB(@Unique @UnderInitialization(BasicPackingB.class) BasicPackingB this) {}

    @Pure
    void isFullyPacked(@Unique @Initialized BasicPackingB this) {}

    @Pure
    void isPackedToAtLeastObject(@Unique @UnknownInitialization(Object.class) BasicPackingB this) {}

    @Pure
    void isPackedToPackedToAtLeastA(@Unique @UnknownInitialization(BasicPackingA.class) BasicPackingB this) {}

    @NonMonotonic
    void correctPacking(@Unique BasicPackingB this) {
        this.isPackedToA();
        this.isUnpacked();
        this.isPackedToA();
        this.isFullyPacked();
    }

    @NonMonotonic
    void unpackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        // :: error: nullness.assignment.type.incompatible
        this.bField = null;
        // :: error: initialization.unpacking.unknown
        Packing.unpack(this, BasicPackingB.class);
    }

    @NonMonotonic
    void incorrectPackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        // :: error: packing.method.invocation.invalid
        this.isFullyPacked();
    }

    @NonMonotonic
    void unpackNonReceiver(@Unique BasicPackingB this, @Unique BasicPackingB other) {
        // :: error: initialization.packing.nonreceiver
        Packing.unpack(other, BasicPackingB.class);
    }

    @NonMonotonic
    // :: error: packing.postcondition.not.satisfied
    void unpackAliased(@MaybeAliased BasicPackingB this) {
        // :: error: nullness.assignment.type.incompatible
        this.bField = null;
        // :: error: exclusivity.packing.aliased
        Packing.unpack(this, BasicPackingB.class);
    }

    @NonMonotonic
    void unpackObject(@Unique BasicPackingB this) {
        // :: error: initialization.unpacking.object.class
        Packing.unpack(this, Object.class);
    }

    @NonMonotonic
    // :: error: nullness.initialization.fields.uninitialized
    void incorrectModification(@Unique BasicPackingB this) {
        this.bField = null;
    }

    @NonMonotonic
    void correctModification(@Unique BasicPackingB this) {
        this.bField = null;
        this.bField = new Obj();
    }

    @NonMonotonic
    void doublePacking0(@Unique BasicPackingB this) {
        // :: error: initialization.already.unpacked
        Packing.unpack(this, BasicPackingB.class);
        Packing.pack(this, BasicPackingB.class);
        // :: error: initialization.already.packed
        Packing.pack(this, BasicPackingB.class);
    }

    @NonMonotonic
    void doublePacking1(@Unique BasicPackingB this) {
        // :: error: initialization.already.unpacked
        Packing.unpack(this, BasicPackingB.class);
        Packing.pack(this, BasicPackingB.class);
    }
}
