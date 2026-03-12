package daikon.diff;

import daikon.inv.Implication;
import daikon.inv.Invariant;
import java.util.Comparator;

/**
 * Comparator for sorting invariants. If an invariant is an implication, its consequent is used
 * instead of the whole invariant. If the consequents of two invariants are equal, the predicates
 * are compared. The predicates and consequents themselves are compared using the Comparator c
 * passed to the constructor. Some examples:
 *
 * <pre>
 * this.compare(A&rArr;B, A&rArr;C) == c.compare(B, C)
 * this.compare(B, A&rArr;C) == c.compare(B, C)
 * this.compare(B, C) == c.compare(B, C)
 * this.compare(A&rArr;C, B&rArr;C) == c.compare(A, B)
 * </pre>
 */
public class ConsequentSortComparator implements Comparator  {

    //@ public invariant_free packed <: daikon.diff.ConsequentSortComparator ==> c.packed == \typeof(c);
    //@ public invariant_free \invariant_free_for(c);
    //@ public invariant_free packed <: daikon.diff.ConsequentSortComparator ==> ((true) && (c != null));

    public /*@nullable@*/ java.util.Comparator c;

    
    /*@ public normal_behavior
      @ requires (true) && (c != null);
      @ requires_free this.packed == daikon.diff.ConsequentSortComparator;
      @ requires_free c.packed == \typeof(c);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ ConsequentSortComparator(/*@nullable@*/ java.util.Comparator c) {
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
    public static /*@nullable@*/ daikon.diff.ConsequentSortComparator __INIT_trampoline(/*@nullable@*/ java.util.Comparator c, boolean c_nullness) {
        return new daikon.diff.ConsequentSortComparator(c);
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
        daikon.inv.Implication imp1;
        daikon.inv.Implication temp1 = null;
        imp1 = temp1;
        daikon.inv.Implication imp2;
        daikon.inv.Implication temp2 = null;
        imp2 = temp2;
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp3 = arg1;
        inv1 = temp3;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp4 = arg2;
        inv2 = temp4;
        if (inv1 instanceof Implication) {
            daikon.inv.Implication temp5 = (Implication)inv1;
            imp1 = temp5;
            daikon.inv.Invariant temp6 = imp1.consequent();
            inv1 = temp6;
        }
        if (inv2 instanceof Implication) {
            daikon.inv.Implication temp7 = (Implication)inv2;
            imp2 = temp7;
            daikon.inv.Invariant temp8 = imp2.consequent();
            inv2 = temp8;
        }
        int result;
        int temp9 = c.compare(inv1, inv2);
        result = temp9;
        if (result == 0 && imp1 != null && imp2 != null) {
            return c.compare(imp1.predicate(), imp2.predicate());
        } else {
            return result;
        }
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
