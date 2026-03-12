package daikon.diff;

import daikon.inv.Implication;
import daikon.inv.Invariant;
import java.util.Comparator;

/**
 * Comparator for pairing invariants. In an invariant in set2 is an implication, its consequent is
 * used instead of the whole invariant. In set1, the whole invariant is always used. Some examples:
 *
 * <pre>
 * this.compare(A, B&rArr;A) == c.compare(A, A)
 * this.compare(C, D) == c.compare(C, D)
 * </pre>
 */
public class ConsequentPairComparator implements Comparator  {

    //@ public invariant_free packed <: daikon.diff.ConsequentPairComparator ==> c.packed == \typeof(c);
    //@ public invariant_free \invariant_free_for(c);
    //@ public invariant_free packed <: daikon.diff.ConsequentPairComparator ==> ((true) && (c != null));

    public /*@nullable@*/ java.util.Comparator c;

    
    /*@ public normal_behavior
      @ requires (true) && (c != null);
      @ requires_free this.packed == daikon.diff.ConsequentPairComparator;
      @ requires_free c.packed == \typeof(c);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ ConsequentPairComparator(/*@nullable@*/ java.util.Comparator c) {
        super();

        this.c = c;
    }

    /*@ public normal_behavior
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.ConsequentPairComparator __INIT_trampoline(/*@nullable@*/ java.util.Comparator c, boolean c_nullness) {
        return new daikon.diff.ConsequentPairComparator(c);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (arg1 != null);
      @ requires (true) && (arg2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free arg1.packed == \typeof(arg1);
      @ requires_free arg2.packed == \typeof(arg2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free arg1.packed == \typeof(arg1);
      @ ensures_free arg2.packed == \typeof(arg2);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ int compare(/*@nullable@*/ daikon.inv.Invariant arg1, /*@nullable@*/ daikon.inv.Invariant arg2) {
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp1 = arg1;
        inv1 = temp1;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp2 = arg2;
        inv2 = temp2;
        if (inv2 instanceof Implication) {
            daikon.inv.Implication imp2;
            daikon.inv.Implication temp3 = (Implication)inv2;
            imp2 = temp3;
            daikon.inv.Invariant temp4 = imp2.consequent();
            inv2 = temp4;
        }
        return c.compare(inv1, inv2);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires arg1_nullness || ((true) && (arg1 != null));
      @ requires arg2_nullness || ((true) && (arg2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !arg1_nullness || ((true) && (arg1 != null));
      @ requires_free !arg2_nullness || ((true) && (arg2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free arg1.packed == \typeof(arg1);
      @ ensures_free arg2.packed == \typeof(arg2);
      @ assignable \nothing;
      @*/
    public  /*@helper@*/ int __compare_trampoline(/*@nullable@*/ daikon.inv.Invariant arg1, /*@nullable@*/ daikon.inv.Invariant arg2, boolean this_nullness, boolean arg1_nullness, boolean arg2_nullness) {
        return compare(arg1, arg2);
    }

}
