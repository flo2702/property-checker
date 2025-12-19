package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClause("public ghost \\locset footprint;")
@JMLClause("public accessible \\inv: footprint;")
// packed field not included in footprint
@JMLClause("public invariant this.footprint == \\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first == null ? \\empty : this.first.footprint);")
@JMLClause("public invariant this.first != null ==> \\invariant_for(this.first);")
@JMLClause("public invariant this.first != null ==> \\disjoint(this.*, this.first.footprint);")
public final class SortedList {

    public @Dependable @Unique @Nullable @Sorted Node first;

    @VerifastEnsuresClause("this_first_e == null")
    @JMLClause("ensures this.first == null;")
    @JMLClause("ensures \\fresh(this.footprint);")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: sorted.initialization.fields.uninitialized
    public @PossiblyEmpty @Inv SortedList() {
        // :: error: sorted.assignment.type.incompatible
        this.first = null;
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint))");
    }

    @EnsuresNonEmpty(value="this")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: empty.contracts.postcondition.not.satisfied
    // :: error: inv.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @PossiblyEmpty @Inv SortedList this,
            Order newHead) {
        if (this.first == null) {
            this.first = new Node(newHead);
        } else {
            this.first.insert(newHead);
        }
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first.footprint)");
    }

    @VerifastEnsuresClause("[_](this_first_r.head |-> result)")
    @JMLClause("ensures \\old(this.first).head == \\result;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint, this.first.packed;")
    @EnsuresPossiblyEmpty(value="this")
    // :: error: inv.contracts.postcondition.not.satisfied
    public Order remove(@Unique @NonEmpty @Inv SortedList this) {
        Assert._verifast_open("NonEmpty(this_first_r)");
        // :: error: nullness.dereference.of.nullable
        Order result = this.first.getHead();
        this.first = this.first.stealTail();
        Assert._verifast_close("NonEmpty(this_first_r)");
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first == null ? \\empty : this.first.footprint)");
        return result;
    }

    @VerifastEnsuresClause("this_first_r == null ? result == null : [_](this_first_r.head |-> result)")
    @JMLClause("ensures \\old(this.first) != null ==> \\result == \\old(this.first).head;")
    @JMLClause("ensures \\old(this.first) == null ==> \\result == null;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint, this.first.packed;")
    public @Nullable Order removeIfPresent(@Unique @PossiblyEmpty @Inv SortedList this) {
        if (this.first != null) {
            // :: error: empty.method.invocation.invalid
            return this.remove();
        } else {
            return null;
        }
    }

    @VerifastRequiresClause("this.first |-> ?this_first_r &*& this_first_r != null &*& this_first_r.head |-> ?this_first_head_r")
    @VerifastEnsuresClause("[_](this.first |-> this_first_r) &*& this_first_r != null &*& [_](this_first_r.head |-> this_first_head_r) &*& this_first_head_r == result")
    @JMLClause("ensures \\result == this.first.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Order getHead(@Unique @NonEmpty @Inv SortedList this) {
        // :: error: nullness.dereference.of.nullable
        return this.first.getHead();
    }
}
