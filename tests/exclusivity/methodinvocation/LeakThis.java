import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class LeakThis {

    @ReadOnly LeakThis readOnly;
    @MaybeAliased LeakThis aliased;
    @Unique LeakThis unique;

    // :: error: initialization.fields.uninitialized
    LeakThis() {
        this.readOnly = this;
        this.mthReadOnly();
    }

    LeakThis(boolean dummy) {
        // :: error: exclusivity.type.invalidated
        this.unique = this;
        // :: error: exclusivity.type.invalidated
        this.mthUnique();
    }

    // :: error: initialization.fields.uninitialized
    LeakThis(int dummy) {
        // :: error: exclusivity.type.invalidated
        this.aliased = this;
        // :: error: exclusivity.type.invalidated
        this.mthAliased();
    }

    void mthReadOnly(@ReadOnly LeakThis this) {
        // :: error: assignment.this-not-writable
        this.readOnly = this;
    }

    void mthAliased(@MaybeAliased LeakThis this) {
        this.aliased = this;
    }
    
    void mthUnique(@Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.unique = this;
    }
    
    void foo0(@Unique LeakThis this, @Unique LeakThis a) { }
    
    void bar0() {
        LeakThis a = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo0(a);
    }
    
    void bar1(@Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.foo0(this);
    }
    
    void bar2(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        this.foo0(a);
    }
    
    void foo1(@Unique LeakThis this, @Unique LeakThis a, @Unique LeakThis b) { }
    
    void bar3() {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo1(b, b);
    }
    
    void bar4(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo1(this, this);
    }
    
    void bar5(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        this.foo1(a, b);
    }
}
 