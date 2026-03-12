package daikon.diff;

import daikon.inv.Invariant;
import java.util.Comparator;

/**
 * Comparator for sorting invariants. Uses the ConsequentSortComparator, initialized with the
 * ClassVarnameFormulaComparator. See the documentation for those two classes to figure out what
 * this class does.
 */
public class ConsequentCVFSortComparator implements Comparator  {

    //@ public invariant_free packed <: daikon.diff.ConsequentCVFSortComparator ==> c.packed == \typeof(c);
    //@ public invariant_free \invariant_free_for(c);
    //@ public invariant_free packed <: daikon.diff.ConsequentCVFSortComparator ==> ((true) && (c != null));

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.ConsequentCVFSortComparator;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ ConsequentCVFSortComparator() {
        super();
        c = ConsequentSortComparator.__INIT_trampoline(new Invariant.ClassVarnameFormulaComparator(), true);


    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.ConsequentCVFSortComparator __INIT_trampoline() {
        return new daikon.diff.ConsequentCVFSortComparator();
    }

    public /*@nullable@*/ java.util.Comparator c;

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv1 != null);
      @ requires (true) && (inv2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ int compare(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return c.compare(inv1, inv2);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv1_nullness || ((true) && (inv1 != null));
      @ requires inv2_nullness || ((true) && (inv2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv1_nullness || ((true) && (inv1 != null));
      @ requires_free !inv2_nullness || ((true) && (inv2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ assignable \nothing;
      @*/
    public  /*@helper@*/ int __compare_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness, boolean inv1_nullness, boolean inv2_nullness) {
        return compare(inv1, inv2);
    }

}
