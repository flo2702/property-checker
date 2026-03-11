import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class LeakThis {

    @UnknownInitialization(Object.class) @ReadOnly @Nullable LeakThis readOnly;
    @UnknownInitialization(Object.class) @MaybeAliased LeakThis aliased;
    @UnknownInitialization(Object.class) @Unique LeakThis unique;

    // :: error: nullness.initialization.fields.uninitialized
    @UnknownInitialization(LeakThis.class) LeakThis() {
        this.readOnly = this;
        this.mthReadOnly();
    }

    // :: error: nullness.initialization.fields.uninitialized
    @UnknownInitialization(LeakThis.class) LeakThis(boolean dummy) {
        this.unique = this;
        // :: error: exclusivity.type.invalidated
        this.mthUnique();
    }

    // :: error: nullness.initialization.fields.uninitialized
    @UnknownInitialization(LeakThis.class) @MaybeAliased LeakThis(int dummy) {
        this.aliased = this;
        this.mthAliased();
    }

    void mthReadOnly(@UnknownInitialization(Object.class) @ReadOnly LeakThis this) {
        // :: error: exclusivity.assignment.receiver-not-writable
        this.readOnly = this;
    }

    void mthAliased(@UnknownInitialization(Object.class) @MaybeAliased LeakThis this) {
        this.aliased = this;
    }

    // :: error: exclusivity.postcondition.not.satisfied
    void mthUnique(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        this.unique = this;
    }
    
    void foo0(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) { }
    
    void bar0(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        // :: error: exclusivity.type.invalidated
        a.foo0(a);
    }
    
    void bar1(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.foo0(this);
    }
    
    void bar2(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        this.foo0(a);
    }
    
    void foo1(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) { }
    
    void bar3(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) {
        // :: error: exclusivity.type.invalidated
        a.foo1(b, b);
    }
    
    void bar4(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        // :: error: exclusivity.type.invalidated
        a.foo1(this, this);
    }
    
    void bar5(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) {
        this.foo1(a, b);
    }
}
