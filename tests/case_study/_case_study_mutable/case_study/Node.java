package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClause("public ghost \\locset footprint;")
@JMLClause("public accessible \\inv: footprint;")
// packed field not included in footprint
@JMLClause("public invariant this.footprint == \\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail == null ? \\empty : this.tail.footprint);")
@JMLClause("public invariant this.tail != null ==> \\disjoint(this.*, this.tail.footprint);")
@JMLClause("public invariant this.tail == null || \\invariant_for(this.tail);")
public final class Node {

    public @Dependable @MaybeAliased Order head;

    // See the comment about SortedList::first in SortedList class.
    public @Dependable @Unique @Nullable @Sorted Node tail;

    @VerifastRequiresClause("Sorted(head, tail)")
    @VerifastEnsuresClause("this_tail_e == tail &*& this_head_e == head")
    @JMLClause("requires \\invariant_for(tail);")
    @JMLClause("requires head.product.price <= tail.head.product.price;")
    @JMLClause("ensures this.tail == tail && this.head == head;")
    @JMLClause("assignable \\nothing;") @Pure
    @EnsuresReadOnly(value="#2")
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    Node(Order head, @Unique @Sorted Node tail) {
        this.head = head;
        this.tail = tail;
        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");

        // Why is this necessary?
        Assert._verifast_close_translationOnly("[0.5]Node_FieldTypes(this.head, this.tail)");
        Assert._verifast_close_translationOnly("[0.5]Sorted(tail_head_r, tail_tail_r)");
    }

    @VerifastEnsuresClause("this_tail_e == null &*& this_head_e == head")
    @JMLClause("ensures this.head == head && this.tail == null;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    // :: error: sorted.initialization.fields.uninitialized
    Node(Order head) {
        this.head = head;
        // :: error: sorted.assignment.type.incompatible
        this.tail = null;
        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint))");
    }

    @VerifastEnsuresClause("(this_head_e == this_head_r || this_head_e == newHead)")
    @JMLClause("ensures this.head == \\old(this.head) || this.head == newHead;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    public void insert(
            @Unique @Sorted Node this,
            Order newHead) {
        Assert._verifast_open("[0.5]Order_OwnFields(this_head_r, _, _, ?oldHead_product)");
        Assert._verifast_open("[0.5]Product_OwnFields(oldHead_product, _, ?oldPrice, _)");
        Assert._verifast_close("[0.5]OrderPred(this_head_r, oldPrice)");

        Assert._verifast_open("[0.5]Order_OwnFields(newHead, _, _, ?newHead_product)");
        Assert._verifast_open("[0.5]Product_OwnFields(newHead_product, _, ?newPrice, _)");
        Assert._verifast_close("[0.5]OrderPred(newHead, newPrice)");

        if (newHead.getPrice() <= this.head.getPrice()) {
            Assert._verifast_close("[0.5]SortedOrders(newHead, this_head_r)");
            Assert._verifast_close("[0.5]Node_FieldTypes(this_head_r, this_tail_r)");
            this.insertHead(newHead);
        } else {
            Assert._verifast_close("[0.5]SortedOrders(this_head_r, newHead)");
            Assert._verifast_close("[0.5]Node_FieldTypes(this_head_r, this_tail_r)");
            this.insertTail(newHead);
        }
    }

    @VerifastRequiresClause("SortedOrders(newHead, this_head_r)")
    @VerifastEnsuresClause("this_head_e == newHead")
    @JMLClause("requires newHead.product.price <= this.head.product.price;")
    @JMLClause("ensures this.head == newHead;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertHead(
            @Unique @Sorted Node this,
            Order newHead) {
        if (this.tail == null) {
            this.tail = new Node(this.head);
        } else {
            this.tail = new Node(this.head, this.tail);
        }
        this.head = newHead;
        Assert._verifast_close("[0.5]Node_OwnFields(this.tail, this_head_r, _)");
        Assert._verifast_close("[0.5]Sorted(newHead, this.tail)");

        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");
    }

    @VerifastRequiresClause("SortedOrders(this_head_r, newHead)")
    @VerifastEnsuresClause("this_head_e == this_head_r")
    @JMLClause("requires this.head.product.price <= newHead.product.price;")
    @JMLClause("ensures this.head == \\old(this.head);")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertTail(
            @Unique @Sorted Node this,
            Order newHead) {

        if (tail == null) {
            this.tail = new Node(newHead);
        } else {
            this.tail.insert(newHead);
        }
        Assert._verifast_close("[0.5]Node_OwnFields(this.tail, _, _)");
        Assert._verifast_close("[0.5]Sorted(this.head, this.tail)");

        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");

        // These statements use the uniqueness and packing type systems to tell KeY that certain heap locations are immutable.
        // E.g., the first statement translates to `//@ assume this.head == \old(this.head) ==> this.head.product.price == \old(this.head.product.price)`,
        // which is sound because `this.head` is `@MaybeAliased @Packed(Order.class)` and thus immutable.
        Assert.immutableFieldUnchanged("this.head", "this.head.product.price");
        Assert.immutableFieldUnchanged("this.tail.head", "this.tail.head.product.price");
        Assert.immutableFieldEqual("this.tail.head", "newHead", "this.tail.head.product.price", "newHead.product.price");
    }

    @VerifastSuppressTranslatedContract
    @VerifastRequiresClause("[?frac](this.head |-> ?this_head_r)")
    @VerifastEnsuresClause("[frac](this.head |-> this_head_r)")
    @VerifastEnsuresClause("this_head_r == result")
    @JMLClause("ensures \\result == this.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Order getHead(@Unique @Sorted Node this) {
        return this.head;
    }

    @VerifastSuppressTranslatedContract
    @VerifastRequiresClause("[?frac](this.tail |-> ?this_tail_r)")
    @VerifastEnsuresClause("[frac](this.tail |-> this_tail_r)")
    @VerifastEnsuresClause("this_tail_r == result")
    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @ReadOnly @Nullable Node getTail(@Unique @Sorted Node this) {
        return this.tail;
    }

    @VerifastSuppressTranslatedContract
    @VerifastRequiresClause("[?frac](this.tail |-> ?this_tail_r)")
    @VerifastEnsuresClause("[frac](this.tail |-> this_tail_r)")
    @VerifastEnsuresClause("this_tail_r == result")
    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("ensures \\result != null ==> \\invariant_for(\\result);")
    @JMLClause("assignable this.packed;")
    @EnsuresReadOnly("this")
    @EnsuresUnknownInit(value="this", targetValue=Object.class)
    public
    @Unique @Nullable @Sorted Node
    stealTail(@Unique @Sorted Node this) {
        return this.tail;
    }
}
