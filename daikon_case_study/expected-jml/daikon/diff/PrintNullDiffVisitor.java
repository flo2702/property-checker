package daikon.diff;

import daikon.inv.Invariant;
import java.io.PrintStream;

/**
 * <B>PrintNullDiffVIsitor</B> is a NodeVisitor that only reports an invariant as different when its
 * existence in one set is not in another set. This avoids reported differences simply in confidence
 * changes and other extra-sensitive reports.
 */
public class PrintNullDiffVisitor extends PrintDifferingInvariantsVisitor  {


    
    /**
     * Create an instance of PrintNullDiffVisitor. 
     */
        /*@ public normal_behavior
      @ requires (true) && (ps != null);
      @ requires_free this.packed == daikon.diff.PrintNullDiffVisitor;
      @ requires_free ps.packed == \typeof(ps);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ PrintNullDiffVisitor(/*@nullable@*/ java.io.PrintStream ps, boolean verbose) {
        super(ps, verbose, false);

    }

    /*@ public normal_behavior
      @ requires ps_nullness || ((true) && (ps != null));
      @ requires_free !ps_nullness || ((true) && (ps != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.PrintNullDiffVisitor __INIT_trampoline(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean ps_nullness) {
        return new daikon.diff.PrintNullDiffVisitor(ps, verbose);
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
        daikon.inv.Invariant temp0 = node.__getInv1_trampoline(true, true);
        inv1 = temp0;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp1 = node.__getInv2_trampoline(true, true);
        inv2 = temp1;
        if (inv1 != null ^ inv2 == null) {
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

}
