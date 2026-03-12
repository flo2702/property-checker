package daikon.diff;

import daikon.PptSlice;
import daikon.PptConditional;
import daikon.inv.Implication;
import daikon.inv.Invariant;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;

/**
 * <B>ConsequentExtractorVisitor</B> is a visitor that takes in RootNode tree used by the other
 * visitors in Diff and only modifies the first inv tree out of the pair of two inv trees (the
 * second tree is never read or modified).
 *
 * <p>The goal is to take the right hand side of any implication and extract it for later use. The
 * implementation completely replaces the previous inv tree with the a new inv tree. The new inv
 * tree contains only the extracted consequents of the original inv tree.
 */
public class ConsequentExtractorVisitor extends DepthFirstVisitor  {

    //@ public invariant_free packed <: daikon.diff.ConsequentExtractorVisitor ==> repeatFilter.packed == \typeof(repeatFilter);
    //@ public invariant_free \invariant_free_for(repeatFilter);
    //@ public invariant_free packed <: daikon.diff.ConsequentExtractorVisitor ==> accum.packed == \typeof(accum);
    //@ public invariant_free \invariant_free_for(accum);
    //@ public invariant_free packed <: daikon.diff.ConsequentExtractorVisitor ==> ((true) && (repeatFilter != null));
    //@ public invariant_free packed <: daikon.diff.ConsequentExtractorVisitor ==> ((true) && (accum != null));

    public int nonce;

    public /*@nullable@*/ java.util.HashSet repeatFilter;

    public /*@nullable@*/ java.util.List accum;

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.ConsequentExtractorVisitor;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ ConsequentExtractorVisitor() {
        super();
        repeatFilter = new HashSet();

        accum = new ArrayList();


        int temp0 = 0;
        nonce = temp0;
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.ConsequentExtractorVisitor __INIT_trampoline() {
        return new daikon.diff.ConsequentExtractorVisitor();
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
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.PptNode node) {
        if (node.__getPpt1_trampoline(true, true) instanceof PptConditional) {
            return;
        }
        System.out.println(node.__getPpt1_trampoline(true, true).name);
        repeatFilter.clear();
        accum.clear();
        super.__visit_trampoline(node, true, true, true);
        for (Iterator i = node.__children_trampoline(true, true); i.hasNext(); ) {
            daikon.diff.InvNode child;
            daikon.diff.InvNode temp1 = i.next();
            //@ assume (true) && (temp1 instanceof Void || temp1 instanceof daikon.diff.Node && ((daikon.diff.Node)temp1).userObject != null && (((daikon.diff.Node)temp1).userObject.first != null || ((daikon.diff.Node)temp1).userObject.second != null));
            child = temp1;
            if (child.__getInv1_trampoline(true, true) != null) {
                java.util.List invs;
                java.util.List temp2 = child.__getInv1_trampoline(true, true).ppt.invs;
                //@ assume (true) && (temp2 != null);
                invs = temp2;
                invs.clear();
            }
        }
        for (daikon.inv.Invariant inv : accum) {
            daikon.PptSlice ppt;
            daikon.PptSlice temp4 = inv.ppt;
            //@ assume (true) && (temp4 != null);
            ppt = temp4;
            ppt.addInvariant(inv);
        }
        System.out.println("NONCE: " + nonce);
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
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.PptNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
    }

    
    /**
     * The idea is to check if the node is an Implication Invariant. If not, immediately remove the
     * invariant. Otherwise, extract the Consequent, remove the Implication, and then add the
     * consequent to the list.
     */
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
        daikon.inv.Invariant temp5 = node.__getInv1_trampoline(true, true);
        inv1 = temp5;
        if (inv1 != null) {
            if (inv1.justified() && (inv1 instanceof Implication)) {
                nonce++;
                daikon.inv.Implication imp;
                daikon.inv.Implication temp6 = (Implication)inv1;
                imp = temp6;
                if (repeatFilter.add(imp.consequent().format())) {
                    accum.add(imp.consequent());
                }
                if (imp.iff == true) {
                    if (repeatFilter.add(imp.predicate().format())) {
                        accum.add(imp.predicate());
                    }
                }
            }
            inv1.ppt.removeInvariant(inv1);
            System.out.println(inv1.ppt.invs.size() + " " + repeatFilter.size());
        } else {
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
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ boolean shouldPrint(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int rel;
        int temp7 = DetailedStatisticsVisitor.__determineRelationship_trampoline(inv1, inv2, false, true);
        rel = temp7;
        if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2 || rel == DetailedStatisticsVisitor.REL_SAME_UNJUST1_UNJUST2 || rel == DetailedStatisticsVisitor.REL_DIFF_UNJUST1_UNJUST2 || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST1 || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST2) {
            return false;
        }
        if ((inv1 == null || !inv1.isWorthPrinting()) && (inv2 == null || !inv2.isWorthPrinting())) {
            return false;
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

}
