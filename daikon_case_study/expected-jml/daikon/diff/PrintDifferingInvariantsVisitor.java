package daikon.diff;

import daikon.inv.Invariant;
import java.io.PrintStream;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Prints the differing invariant pairs. 
 */
public class PrintDifferingInvariantsVisitor extends PrintAllVisitor  {
    static {
        java.util.logging.Logger temp0 = Logger.getLogger("daikon.diff.DetailedStatisticsVisitor");
        //@ assume (true) && (temp0 != null);
        debug = temp0;

    }


    //@ public static invariant_free (true) && (daikon.diff.PrintDifferingInvariantsVisitor.debug != null);

    public static /*@nullable@*/ java.util.logging.Logger debug;

    
    /**
     * Create an instance of PrintDifferingInvariantsVisitor. 
     */
        /*@ public normal_behavior
      @ requires (true) && (ps != null);
      @ requires_free this.packed == daikon.diff.PrintDifferingInvariantsVisitor;
      @ requires_free ps.packed == \typeof(ps);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ PrintDifferingInvariantsVisitor(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts) {
        super(ps, verbose, printEmptyPpts);

    }

    /*@ public normal_behavior
      @ requires ps_nullness || ((true) && (ps != null));
      @ requires_free !ps_nullness || ((true) && (ps != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.PrintDifferingInvariantsVisitor __INIT_trampoline(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts, boolean ps_nullness) {
        return new daikon.diff.PrintDifferingInvariantsVisitor(ps, verbose, printEmptyPpts);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (node != null);
      @ requires (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free node.packed == \typeof(node);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.InvNode node) {
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp1 = node.__getInv1_trampoline(true, true);
        inv1 = temp1;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp2 = node.__getInv2_trampoline(true, true);
        inv2 = temp2;
        if (__shouldPrint_trampoline(inv1, inv2, true, false, false)) {
            super.__visit_trampoline(node, true, true, true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires node_nullness || ((true) && (node != null));
      @ requires node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !node_nullness || ((true) && (node != null));
      @ requires_free !node_nullnessnode || ((true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free node.packed == \typeof(node);
      @ ensures_free (true) && (node instanceof Void || node instanceof daikon.diff.Node && ((daikon.diff.Node)node).userObject != null && (((daikon.diff.Node)node).userObject.first != null || ((daikon.diff.Node)node).userObject.second != null));
      @*/
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.InvNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
    }

    
    /**
     * Returns true if the pair of invariants should be printed, depending on their type,
     * relationship, and printability.
     */
        /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ requires_free debug != null && Level.FINE != null;
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ boolean shouldPrint(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int rel;
        int temp3 = DetailedStatisticsVisitor.__determineRelationship_trampoline(inv1, inv2, false, true);
        rel = temp3;
        if (!__shouldPrintBasedOnRel_trampoline(rel, true)) {
            if (debug.isLoggable(Level.FINE)) {
                debug.fine(" Returning false");
            }
            return false;
        }
        if ((inv1 == null || !inv1.isWorthPrinting()) && (inv2 == null || !inv2.isWorthPrinting())) {
            if (debug.isLoggable(Level.FINE)) {
                debug.fine(" Returning false");
            }
            return false;
        }
        if (debug.isLoggable(Level.FINE)) {
            debug.fine(" Returning true");
        }
        return true;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free debug != null && Level.FINE != null;
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @*/
    public  /*@helper@*/ boolean __shouldPrint_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        return shouldPrint(inv1, inv2);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    private /*@helper@*/ boolean shouldPrintBasedOnRel(int rel) {
        if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2 || rel == DetailedStatisticsVisitor.REL_SAME_UNJUST1_UNJUST2 || rel == DetailedStatisticsVisitor.REL_DIFF_UNJUST1_UNJUST2 || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST1 || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST2) {
            if (debug.isLoggable(Level.FINE)) {
                debug.fine(" Returning false");
            }
            return false;
        }
        return true;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @*/
    public  /*@helper@*/ boolean __shouldPrintBasedOnRel_trampoline(int rel, boolean this_nullness) {
        return shouldPrintBasedOnRel(rel);
    }

}
