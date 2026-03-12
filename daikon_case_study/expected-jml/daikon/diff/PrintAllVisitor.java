package daikon.diff;

import daikon.Global;
import daikon.Ppt;
import daikon.inv.Invariant;
import java.io.PrintStream;
import java.text.DecimalFormat;

/**
 * Prints all the invariant pairs, including pairs containing identical invariants. 
 */
public class PrintAllVisitor extends DepthFirstVisitor  {
    static {
        java.lang.String temp0 = Global.lineSep;
        //@ assume (true) && (temp0 != null);
        lineSep = temp0;

        boolean temp1 = false;
        HUMAN_OUTPUT = temp1;

        java.text.DecimalFormat temp2 = new DecimalFormat("0.####");
        //@ assume (true) && (temp2 != null);
        CONFIDENCE_FORMAT = temp2;

    }


    //@ public invariant_free packed <: daikon.diff.PrintAllVisitor ==> ps.packed == \typeof(ps);
    //@ public invariant_free \invariant_free_for(ps);
    //@ public invariant_free packed <: daikon.diff.PrintAllVisitor ==> bufOutput.packed == \typeof(bufOutput);
    //@ public invariant_free \invariant_free_for(bufOutput);
    //@ public static invariant_free (true) && (daikon.diff.PrintAllVisitor.lineSep != null);
    //@ public static invariant_free (true) && (daikon.diff.PrintAllVisitor.CONFIDENCE_FORMAT != null);
    //@ public invariant_free packed <: daikon.diff.PrintAllVisitor ==> ((true) && (ps != null));
    //@ public invariant_free packed <: daikon.diff.PrintAllVisitor ==> ((true) && (bufOutput != null));

    public static /*@nullable@*/ java.lang.String lineSep;

    public static boolean HUMAN_OUTPUT;

    public static /*@nullable@*/ java.text.DecimalFormat CONFIDENCE_FORMAT;

    public /*@nullable@*/ java.io.PrintStream ps;

    public boolean verbose;

    public boolean printEmptyPpts;

    public /*@nullable@*/ java.lang.StringBuilder bufOutput;

    
    /*@ public normal_behavior
      @ requires (true) && (ps != null);
      @ requires_free this.packed == daikon.diff.PrintAllVisitor;
      @ requires_free ps.packed == \typeof(ps);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ PrintAllVisitor(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts) {
        super();
        bufOutput = new StringBuilder();


        this.ps = ps;
        this.verbose = verbose;
        this.printEmptyPpts = printEmptyPpts;
    }

    /*@ public normal_behavior
      @ requires ps_nullness || ((true) && (ps != null));
      @ requires_free !ps_nullness || ((true) && (ps != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.PrintAllVisitor __INIT_trampoline(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts, boolean ps_nullness) {
        return new daikon.diff.PrintAllVisitor(ps, verbose, printEmptyPpts);
    }

    
    /**
     * Prints the pair of program points, and all the invariants contained within them. 
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
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.PptNode node) {
        bufOutput.setLength(0);
        super.__visit_trampoline(node, true, true, true);
        if (bufOutput.length() > 0 || printEmptyPpts) {
            daikon.Ppt ppt1;
            daikon.Ppt temp6 = node.__getPpt1_trampoline(true, true);
            ppt1 = temp6;
            daikon.Ppt ppt2;
            daikon.Ppt temp7 = node.__getPpt2_trampoline(true, true);
            ppt2 = temp7;
            ps.print("<");
            if (ppt1 == null) {
                ps.print((String)null);
            } else {
                ps.print(ppt1.name());
            }
            if (ppt1 == null || ppt2 == null || !ppt1.name().equals(ppt2.name())) {
                ps.print(", ");
                if (ppt2 == null) {
                    ps.print((String)null);
                } else {
                    ps.print(ppt2.name());
                }
            }
            ps.println(">");
            ps.print(bufOutput.toString());
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
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.PptNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
    }

    
    /**
     * Prints a pair of invariants. Includes the type of the invariants and their relationship. 
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
        if (HUMAN_OUTPUT) {
            __printHumanOutput_trampoline(node, true, true, true);
            return;
        }
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp8 = node.__getInv1_trampoline(true, true);
        inv1 = temp8;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp9 = node.__getInv2_trampoline(true, true);
        inv2 = temp9;
        __bufPrint_trampoline("  <", true);
        if (inv1 == null) {
            __bufPrint_trampoline(null, true);
        } else {
            __printInvariant_trampoline(inv1, true, true);
        }
        __bufPrint_trampoline(", ", true);
        if (inv2 == null) {
            __bufPrint_trampoline((String)null, true);
        } else {
            __printInvariant_trampoline(inv2, true, true);
        }
        __bufPrint_trampoline(">", true);
        int arity;
        int temp10 = DetailedStatisticsVisitor.__determineArity_trampoline(inv1, inv2, false, false);
        arity = temp10;
        java.lang.String arityLabel;
        java.lang.String temp11 = DetailedStatisticsVisitor.ARITY_LABELS[arity];
        arityLabel = temp11;
        int rel;
        int temp12 = DetailedStatisticsVisitor.__determineRelationship_trampoline(inv1, inv2, false, true);
        rel = temp12;
        java.lang.String relLabel;
        java.lang.String temp13 = DetailedStatisticsVisitor.RELATIONSHIP_LABELS[rel];
        relLabel = temp13;
        __bufPrint_trampoline(" (" + arityLabel + "," + relLabel + ")", true);
        __bufPrintln_trampoline(true);
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
     * This method is an alternate printing procedure for an InvNode so that the output is more human
     * readable. The format resembles cvs diff with '+' and '-' signs for the differing invariants.
     * There is no information on justification or invariant type.
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
    public /*@helper@*/ void printHumanOutput(/*@nullable@*/ daikon.diff.InvNode node) {
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp14 = node.__getInv1_trampoline(true, true);
        inv1 = temp14;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp15 = node.__getInv2_trampoline(true, true);
        inv2 = temp15;
        if (inv1 != null && inv2 != null && inv1.format().equals(inv2.format())) {
            return;
        }
        if (inv1 == null) {
        } else {
            __bufPrintln_trampoline(("- " + inv1.format()).trim(), true);
        }
        if (inv2 == null) {
        } else {
            __bufPrintln_trampoline(("+ " + inv2.format()).trim(), true);
        }
        __bufPrintln_trampoline(true);
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
    public  /*@helper@*/ void __printHumanOutput_trampoline(/*@nullable@*/ daikon.diff.InvNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        printHumanOutput(node);
    }

    
    /**
     * Prints an invariant, including its printability and possibly its confidence. Example: "argv !=
     * null {0.9999+}".
     */
        /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv.packed == \typeof(inv);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ void printInvariant(/*@nullable@*/ daikon.inv.Invariant inv) {
        if (verbose) {
            __bufPrint_trampoline(inv.repr_prob(), true);
            __bufPrint_trampoline(" {", true);
            __printPrintability_trampoline(inv, true, true);
            __bufPrint_trampoline("}", true);
        } else {
            __bufPrint_trampoline(inv.format(), true);
            __bufPrint_trampoline(" {", true);
            __printConfidence_trampoline(inv, true, true);
            __printPrintability_trampoline(inv, true, true);
            __bufPrint_trampoline("}", true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    public  /*@helper@*/ void __printInvariant_trampoline(/*@nullable@*/ daikon.inv.Invariant inv, boolean this_nullness, boolean inv_nullness) {
        printInvariant(inv);
    }

    
    /**
     * Prints the confidence of the invariant. Confidences between .9999 and 1 are rounded to .9999.
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv.packed == \typeof(inv);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void printConfidence(/*@nullable@*/ daikon.inv.Invariant inv) {
        double conf;
        double temp16 = inv.getConfidence();
        conf = temp16;
        if (0.9999 < conf && conf < 1) {
            double temp17 = 0.9999;
            conf = temp17;
        }
        __bufPrint_trampoline(CONFIDENCE_FORMAT.format(conf), true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    public  /*@helper@*/ void __printConfidence_trampoline(/*@nullable@*/ daikon.inv.Invariant inv, boolean this_nullness, boolean inv_nullness) {
        printConfidence(inv);
    }

    
    /**
     * Prints '+' if the invariant is worth printing, '-' otherwise. 
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv.packed == \typeof(inv);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void printPrintability(/*@nullable@*/ daikon.inv.Invariant inv) {
        if (inv.isWorthPrinting()) {
            __bufPrint_trampoline("+", true);
        } else {
            __bufPrint_trampoline("-", true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    public  /*@helper@*/ void __printPrintability_trampoline(/*@nullable@*/ daikon.inv.Invariant inv, boolean this_nullness, boolean inv_nullness) {
        printPrintability(inv);
    }

    
    /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free s.packed == \typeof(s);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ void bufPrint(/*@nullable@*/ java.lang.String s) {
        bufOutput.append(s);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @*/
    public  /*@helper@*/ void __bufPrint_trampoline(/*@nullable@*/ java.lang.String s, boolean this_nullness) {
        bufPrint(s);
    }

    
    /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free s.packed == \typeof(s);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ void bufPrintln(/*@nullable@*/ java.lang.String s) {
        __bufPrint_trampoline(s, true);
        __bufPrintln_trampoline(true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @*/
    public  /*@helper@*/ void __bufPrintln_trampoline(/*@nullable@*/ java.lang.String s, boolean this_nullness) {
        bufPrintln(s);
    }

    
    /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ void bufPrintln() {
        bufOutput.append(Global.lineSep);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ void __bufPrintln_trampoline(boolean this_nullness) {
        bufPrintln();
    }

}
