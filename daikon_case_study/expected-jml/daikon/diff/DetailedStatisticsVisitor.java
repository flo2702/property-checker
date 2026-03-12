package daikon.diff;

import daikon.inv.Invariant;
import daikon.PptSlice;
import java.lang.Math;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.plumelib.util.ArraysPlume;
import org.plumelib.util.StringsPlume;

/**
 * Computes statistics about the differences between the sets of invariants. The statistics can be
 * printed as a human-readable table or a tab-separated list suitable for further processing.
 */
public class DetailedStatisticsVisitor extends DepthFirstVisitor  {
    static {
        java.util.logging.Logger temp0 = Logger.getLogger("daikon.diff.DetailedStatisticsVisitor");
        //@ assume (true) && (temp0 != null);
        debug = temp0;

        int temp1 = 5;
        FIELD_WIDTH = temp1;

        int temp2 = 7;
        LABEL_WIDTH = temp2;

        int temp3 = 4;
        NUM_ARITIES = temp3;

        java.lang.String[] temp4 = {"Nul", "Una", "Bin", "Ter"};
        //@ assume (true) && (temp4 != null);
        ARITY_LABELS = temp4;

        int temp5 = 12;
        NUM_RELATIONSHIPS = temp5;

        int temp6 = 0;
        REL_SAME_JUST1_JUST2 = temp6;

        int temp7 = 1;
        REL_SAME_JUST1_UNJUST2 = temp7;

        int temp8 = 2;
        REL_SAME_UNJUST1_JUST2 = temp8;

        int temp9 = 3;
        REL_SAME_UNJUST1_UNJUST2 = temp9;

        int temp10 = 4;
        REL_DIFF_JUST1_JUST2 = temp10;

        int temp11 = 5;
        REL_DIFF_JUST1_UNJUST2 = temp11;

        int temp12 = 6;
        REL_DIFF_UNJUST1_JUST2 = temp12;

        int temp13 = 7;
        REL_DIFF_UNJUST1_UNJUST2 = temp13;

        int temp14 = 8;
        REL_MISS_JUST1 = temp14;

        int temp15 = 9;
        REL_MISS_UNJUST1 = temp15;

        int temp16 = 10;
        REL_MISS_JUST2 = temp16;

        int temp17 = 11;
        REL_MISS_UNJUST2 = temp17;

        java.lang.String[] temp18 = {"SJJ", "SJU", "SUJ", "SUU", "DJJ", "DJU", "DUJ", "DUU", "JM", "UM", "MJ", "MU"};
        //@ assume (true) && (temp18 != null);
        RELATIONSHIP_LABELS = temp18;

    }


    //@ public invariant_free packed <: daikon.diff.DetailedStatisticsVisitor ==> freq.packed == \typeof(freq);
    //@ public invariant_free \invariant_free_for(freq);
    //@ public static invariant_free (true) && (daikon.diff.DetailedStatisticsVisitor.debug != null);
    //@ public static invariant_free (true) && (daikon.diff.DetailedStatisticsVisitor.ARITY_LABELS != null);
    //@ public static invariant_free (true) && (daikon.diff.DetailedStatisticsVisitor.RELATIONSHIP_LABELS != null);
    //@ public invariant_free packed <: daikon.diff.DetailedStatisticsVisitor ==> ((true) && (freq != null));

    public static /*@nullable@*/ java.util.logging.Logger debug;

    public static int FIELD_WIDTH;

    public static int LABEL_WIDTH;

    public static int NUM_ARITIES;

    public static /*@nullable@*/ java.lang.String[] ARITY_LABELS;

    public static int NUM_RELATIONSHIPS;

    public static int REL_SAME_JUST1_JUST2;

    public static int REL_SAME_JUST1_UNJUST2;

    public static int REL_SAME_UNJUST1_JUST2;

    public static int REL_SAME_UNJUST1_UNJUST2;

    public static int REL_DIFF_JUST1_JUST2;

    public static int REL_DIFF_JUST1_UNJUST2;

    public static int REL_DIFF_UNJUST1_JUST2;

    public static int REL_DIFF_UNJUST1_UNJUST2;

    public static int REL_MISS_JUST1;

    public static int REL_MISS_UNJUST1;

    public static int REL_MISS_JUST2;

    public static int REL_MISS_UNJUST2;

    public static /*@nullable@*/ java.lang.String[] RELATIONSHIP_LABELS;

    public /*@nullable@*/ double[][] freq;

    public boolean continuousJustification;

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.DetailedStatisticsVisitor;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ DetailedStatisticsVisitor(boolean continuousJustification) {
        super();
        freq = new double[NUM_ARITIES][NUM_RELATIONSHIPS];


        this.continuousJustification = continuousJustification;
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.DetailedStatisticsVisitor __INIT_trampoline(boolean continuousJustification) {
        return new daikon.diff.DetailedStatisticsVisitor(continuousJustification);
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
        daikon.inv.Invariant temp20 = node.__getInv1_trampoline(true, true);
        inv1 = temp20;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp21 = node.__getInv2_trampoline(true, true);
        inv2 = temp21;
        if (shouldAddFrequency(inv1, inv2)) {
            __addFrequency_trampoline(node.__getInv1_trampoline(true, true), node.__getInv2_trampoline(true, true), true, false, false);
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
     * Adds the difference between the two invariants to the appropriate entry in the frequencies
     * table.
     */
        /*@ private normal_behavior
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
    private /*@helper@*/ void addFrequency(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        if (continuousJustification) {
            __addFrequencyContinuous_trampoline(inv1, inv2, true, false, true);
        } else {
            __addFrequencyBinary_trampoline(inv1, inv2, true, false, true);
        }
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
    public  /*@helper@*/ void __addFrequency_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        addFrequency(inv1, inv2);
    }

    
    /**
     * Treats justification as a binary value. The table entry is incremented by 1 regardless of the
     * difference in justifications.
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ requires_free ARITY_LABELS != null && freq.length == ARITY_LABELS.length;
      @ requires_free RELATIONSHIP_LABELS != null && (\forall int i; 0 <= i && i < freq.length; freq[i] != null && freq[i].length == RELATIONSHIP_LABELS.length);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void addFrequencyBinary(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int arity;
        int temp22 = __determineArity_trampoline(inv1, inv2, false, true);
        arity = temp22;
        int relationship;
        int temp23 = __determineRelationship_trampoline(inv1, inv2, false, true);
        relationship = temp23;
        freq[arity][relationship] += 1.0;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free ARITY_LABELS != null && freq.length == ARITY_LABELS.length;
      @ requires_free RELATIONSHIP_LABELS != null && (\forall int i; 0 <= i && i < freq.length; freq[i] != null && freq[i].length == RELATIONSHIP_LABELS.length);
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @*/
    public  /*@helper@*/ void __addFrequencyBinary_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        addFrequencyBinary(inv1, inv2);
    }

    
    /**
     * Treats justification as a continuous value. If one invariant is justified but the other is
     * unjustified, the table entry is incremented by the difference in justifications.
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ requires_free ARITY_LABELS != null && freq.length == ARITY_LABELS.length;
      @ requires_free RELATIONSHIP_LABELS != null && (\forall int i; 0 <= i && i < freq.length; freq[i] != null && freq[i].length == RELATIONSHIP_LABELS.length);
      @ ensures (true) && (inv2 != null || inv1 != null);
      @ ensures (true) && (inv1 != null || inv2 != null);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void addFrequencyContinuous(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int arity;
        int temp24 = __determineArity_trampoline(inv1, inv2, false, true);
        arity = temp24;
        int relationship;
        int temp25 = __determineRelationship_trampoline(inv1, inv2, false, true);
        relationship = temp25;
        switch (relationship) {
        case REL_SAME_JUST1_UNJUST2:
        
        case REL_SAME_UNJUST1_JUST2:
            freq[arity][relationship] += __calculateConfidenceDifference_trampoline(inv1, inv2, false, false);
            break;
        
        default:
            freq[arity][relationship] += 1.0;
        
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free ARITY_LABELS != null && freq.length == ARITY_LABELS.length;
      @ requires_free RELATIONSHIP_LABELS != null && (\forall int i; 0 <= i && i < freq.length; freq[i] != null && freq[i].length == RELATIONSHIP_LABELS.length);
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @*/
    public  /*@helper@*/ void __addFrequencyContinuous_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        addFrequencyContinuous(inv1, inv2);
    }

    
    /**
     * Returns the difference in the probabilites of the two invariants. Confidence values less than 0
     * (i.e. CONFIDENCE_NEVER) are rounded up to 0.
     */
        /*@ private normal_behavior
      @ requires (true) && (inv1 != null);
      @ requires (true) && (inv2 != null);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @*/
    private static /*@helper@*/ double calculateConfidenceDifference(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        assert inv1 != null && inv2 != null;
        double diff;
        
        double conf1;
        double temp27 = Math.max(inv1.getConfidence(), 0);
        conf1 = temp27;
        double conf2;
        double temp28 = Math.max(inv2.getConfidence(), 0);
        conf2 = temp28;
        double temp29 = Math.abs(conf1 - conf2);
        diff = temp29;
        return diff;
    }

    /*@ public normal_behavior
      @ requires inv1_nullness || ((true) && (inv1 != null));
      @ requires inv2_nullness || ((true) && (inv2 != null));
      @ requires_free !inv1_nullness || ((true) && (inv1 != null));
      @ requires_free !inv2_nullness || ((true) && (inv2 != null));
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @*/
    public static /*@helper@*/ double __calculateConfidenceDifference_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean inv1_nullness, boolean inv2_nullness) {
        return calculateConfidenceDifference(inv1, inv2);
    }

    
    /**
     * Returns the arity of the invariant pair. 
     */
        /*@ public normal_behavior
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free debug != null && Level.FINE != null;
      @ requires_free ARITY_LABELS != null && ARITY_LABELS.length == 4;
      @ ensures ARITY_LABELS != null && 0 <= \result && \result < ARITY_LABELS.length;
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ assignable \nothing;
      @*/
    public static /*@helper@*/ int determineArity(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        daikon.inv.Invariant inv;
        daikon.inv.Invariant temp30 = (inv1 != null) ? inv1 : inv2;
        //@ assert (true) && (temp30 != null);
        inv = temp30;
        logInvariantVisit(inv1, inv2);
        daikon.PptSlice ppt;
        daikon.PptSlice temp31 = inv.ppt;
        //@ assume (true) && (temp31 != null);
        ppt = temp31;
        int arity;
        int temp32 = ppt.arity();
        arity = temp32;
        if (debug.isLoggable(Level.FINE)) {
            debug.fine("  arity: " + arity);
        }
        return arity;
    }

    /*@ public normal_behavior
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free debug != null && Level.FINE != null;
      @ requires_free ARITY_LABELS != null && ARITY_LABELS.length == 4;
      @ ensures ARITY_LABELS != null && 0 <= \result && \result < ARITY_LABELS.length;
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ assignable \nothing;
      @*/
    public static /*@helper@*/ int __determineArity_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        return determineArity(inv1, inv2);
    }

    
    /*@ private normal_behavior
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ assignable \nothing;
      @*/
    private static /*@helper@*/ void logInvariantVisit(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        if (debug.isLoggable(Level.FINE)) {
            debug.fine("visit: " + ((inv1 != null) ? inv1.ppt.parent.name() : "NULL") + " " + ((inv1 != null) ? inv1.repr() : "NULL") + " - " + ((inv2 != null) ? inv2.repr() : "NULL"));
        }
    }

    /*@ public normal_behavior
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ assignable \nothing;
      @*/
    public static /*@helper@*/ void __logInvariantVisit_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        logInvariantVisit(inv1, inv2);
    }

    
    /**
     * Returns the relationship between the two invariants. There are twelve possible relationships,
     * described at the beginning of this file.
     */
        /*@ public normal_behavior
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free REL_SAME_JUST1_JUST2 == 0 && REL_SAME_JUST1_UNJUST2 == 1 && REL_SAME_UNJUST1_JUST2 == 2 && REL_SAME_UNJUST1_UNJUST2 == 3;
      @ requires_free REL_DIFF_JUST1_JUST2 == 4 && REL_DIFF_JUST1_UNJUST2 == 5 && REL_DIFF_UNJUST1_JUST2 == 6 && REL_DIFF_UNJUST1_UNJUST2 == 7;
      @ requires_free REL_MISS_JUST1 == 8 && REL_MISS_UNJUST1 == 9 && REL_MISS_JUST2 == 10 && REL_MISS_UNJUST2 == 11;
      @ requires_free RELATIONSHIP_LABELS != null && RELATIONSHIP_LABELS.length == 12;
      @ ensures (true) && (inv2 != null || inv1 != null);
      @ ensures (true) && (inv1 != null || inv2 != null);
      @ ensures \result == REL_SAME_JUST1_JUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_JUST1_UNJUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_UNJUST1_JUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_UNJUST1_UNJUST2 ==> inv1 != null && inv2 != null;
      @ ensures RELATIONSHIP_LABELS != null && 0 <= \result && \result < RELATIONSHIP_LABELS.length;
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ assignable \nothing;
      @*/
    public static /*@helper@*/ int determineRelationship(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int relationship;
        
        if (inv1 == null) {
            int temp34 = inv2.justified() ? REL_MISS_JUST2 : REL_MISS_UNJUST2;
            relationship = temp34;
        } else if (inv2 == null) {
            int temp35 = inv1.justified() ? REL_MISS_JUST1 : REL_MISS_UNJUST1;
            relationship = temp35;
        } else {
            boolean justified1;
            boolean temp36 = inv1.justified();
            justified1 = temp36;
            boolean justified2;
            boolean temp37 = inv2.justified();
            justified2 = temp37;
            if (inv1.isSameInvariant(inv2)) {
                if (justified1 && justified2) {
                    int temp38 = REL_SAME_JUST1_JUST2;
                    relationship = temp38;
                } else if (justified1 && !justified2) {
                    int temp39 = REL_SAME_JUST1_UNJUST2;
                    relationship = temp39;
                } else if (!justified1 && justified2) {
                    int temp40 = REL_SAME_UNJUST1_JUST2;
                    relationship = temp40;
                } else {
                    int temp41 = REL_SAME_UNJUST1_UNJUST2;
                    relationship = temp41;
                }
            } else {
                if (justified1 && justified2) {
                    int temp42 = REL_DIFF_JUST1_JUST2;
                    relationship = temp42;
                } else if (justified1 && !justified2) {
                    int temp43 = REL_DIFF_JUST1_UNJUST2;
                    relationship = temp43;
                } else if (!justified1 && justified2) {
                    int temp44 = REL_DIFF_UNJUST1_JUST2;
                    relationship = temp44;
                } else {
                    int temp45 = REL_DIFF_UNJUST1_UNJUST2;
                    relationship = temp45;
                }
            }
        }
        return relationship;
    }

    /*@ public normal_behavior
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free REL_SAME_JUST1_JUST2 == 0 && REL_SAME_JUST1_UNJUST2 == 1 && REL_SAME_UNJUST1_JUST2 == 2 && REL_SAME_UNJUST1_UNJUST2 == 3;
      @ requires_free REL_DIFF_JUST1_JUST2 == 4 && REL_DIFF_JUST1_UNJUST2 == 5 && REL_DIFF_UNJUST1_JUST2 == 6 && REL_DIFF_UNJUST1_UNJUST2 == 7;
      @ requires_free REL_MISS_JUST1 == 8 && REL_MISS_UNJUST1 == 9 && REL_MISS_JUST2 == 10 && REL_MISS_UNJUST2 == 11;
      @ requires_free RELATIONSHIP_LABELS != null && RELATIONSHIP_LABELS.length == 12;
      @ ensures \result == REL_SAME_JUST1_JUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_JUST1_UNJUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_UNJUST1_JUST2 ==> inv1 != null && inv2 != null;
      @ ensures \result == REL_SAME_UNJUST1_UNJUST2 ==> inv1 != null && inv2 != null;
      @ ensures RELATIONSHIP_LABELS != null && 0 <= \result && \result < RELATIONSHIP_LABELS.length;
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @ assignable \nothing;
      @*/
    public static /*@helper@*/ int __determineRelationship_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        return determineRelationship(inv1, inv2);
    }

    
    /**
     * Returns a tab-separated listing of its data, suitable for post-processing. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ String repr() {
        java.io.StringWriter sw;
        java.io.StringWriter temp46 = new StringWriter();
        sw = temp46;
        java.io.PrintWriter pw;
        java.io.PrintWriter temp47 = new PrintWriter(sw);
        pw = temp47;
        for (int arity = 0; arity < NUM_ARITIES; arity++) {
            for (int rel = 0; rel < NUM_RELATIONSHIPS; rel++) {
                pw.println(String.valueOf(arity) + "\t" + String.valueOf(rel) + "\t" + String.valueOf(freq[arity][rel]));
            }
        }
        return sw.toString();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __repr_trampoline(boolean this_nullness) {
        return repr();
    }

    
    /**
     * Returns a human-readable table of its data. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ String format() {
        java.io.StringWriter sw;
        java.io.StringWriter temp48 = new StringWriter();
        sw = temp48;
        java.io.PrintWriter pw;
        java.io.PrintWriter temp49 = new PrintWriter(sw);
        pw = temp49;
        pw.println("STATISTICS");
        pw.print("       ");
        for (int rel = 0; rel < NUM_RELATIONSHIPS; rel++) {
            pw.print(StringsPlume.rpad(RELATIONSHIP_LABELS[rel], FIELD_WIDTH));
        }
        pw.println(StringsPlume.rpad("TOTAL", FIELD_WIDTH));
        for (int arity = 0; arity < NUM_ARITIES; arity++) {
            pw.print(StringsPlume.rpad(ARITY_LABELS[arity], LABEL_WIDTH));
            for (int rel = 0; rel < NUM_RELATIONSHIPS; rel++) {
                int f;
                int temp50 = (int)freq[arity][rel];
                f = temp50;
                pw.print(StringsPlume.rpad(f, FIELD_WIDTH));
            }
            int s;
            int temp51 = (int)ArraysPlume.sum(freq[arity]);
            s = temp51;
            pw.print(StringsPlume.rpad(s, FIELD_WIDTH));
            pw.println();
        }
        pw.print(StringsPlume.rpad("TOTAL", LABEL_WIDTH));
        for (int rel = 0; rel < NUM_RELATIONSHIPS; rel++) {
            int sum;
            int temp52 = 0;
            sum = temp52;
            for (int arity = 0; arity < NUM_ARITIES; arity++) {
                sum += (int)freq[arity][rel];
            }
            pw.print(StringsPlume.rpad(sum, FIELD_WIDTH));
        }
        pw.print(StringsPlume.rpad((int)ArraysPlume.sum(freq), FIELD_WIDTH));
        pw.println();
        pw.println();
        return sw.toString();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __format_trampoline(boolean this_nullness) {
        return format();
    }

    
    /**
     * Returns the frequency of pairs of invariants we have seen with this arity and relationship. May
     * be a non-integer, since we may be treating justification as a continuous value.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ double freq(int arity, int relationship) {
        return freq[arity][relationship];
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ double __freq_trampoline(int arity, int relationship, boolean this_nullness) {
        return freq(arity, relationship);
    }

    
    /**
     * Returns true if the pair of invariants should be added to the frequency table, based on their
     * printability.
     */
        /*@ private normal_behavior
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @*/
    private static /*@helper@*/ boolean shouldAddFrequency(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return (inv1 != null && inv1.isWorthPrinting()) || (inv2 != null && inv2.isWorthPrinting());
    }

    /*@ public normal_behavior
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @*/
    public static /*@helper@*/ boolean __shouldAddFrequency_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return shouldAddFrequency(inv1, inv2);
    }

}
