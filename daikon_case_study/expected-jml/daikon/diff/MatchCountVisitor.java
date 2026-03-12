package daikon.diff;

import daikon.PptConditional;
import daikon.PptSlice;
import daikon.PptTopLevel;
import daikon.inv.Invariant;
import daikon.inv.OutputFormat;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.StringTokenizer;

/**
 * MatchCountVisitor is a visitor that almost does the opposite of PrintDifferingInvariantsVisitor.
 * MatchCount prints invariant pairs if they are the same, and only if they are a part of a
 * conditional ppt. The visitor also accumulates some state during its traversal for statistics, and
 * can report the match precision.
 *
 * @author Lee Lin
 */
public class MatchCountVisitor extends PrintAllVisitor  {

    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> cnt.packed == \typeof(cnt);
    //@ public invariant_free \invariant_free_for(cnt);
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> targSet.packed == \typeof(targSet);
    //@ public invariant_free \invariant_free_for(targSet);
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> recall.packed == \typeof(recall);
    //@ public invariant_free \invariant_free_for(recall);
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> goodMap.packed == \typeof(goodMap);
    //@ public invariant_free \invariant_free_for(goodMap);
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> ((true) && (cnt != null));
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> ((true) && (targSet != null));
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> ((true) && (recall != null));
    //@ public invariant_free packed <: daikon.diff.MatchCountVisitor ==> ((true) && (goodMap != null));

    public /*@nullable@*/ java.util.HashSet cnt;

    public /*@nullable@*/ java.util.HashSet targSet;

    public /*@nullable@*/ java.util.HashSet recall;

    public /*@nullable@*/ java.util.HashMap goodMap;

    
    /*@ public normal_behavior
      @ requires (true) && (ps != null);
      @ requires_free this.packed == daikon.diff.MatchCountVisitor;
      @ requires_free ps.packed == \typeof(ps);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ MatchCountVisitor(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts) {
        super(ps, verbose, printEmptyPpts);
        cnt = new HashSet();

        targSet = new HashSet();

        recall = new HashSet();

        goodMap = new HashMap();


    }

    /*@ public normal_behavior
      @ requires ps_nullness || ((true) && (ps != null));
      @ requires_free !ps_nullness || ((true) && (ps != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free ps.packed == \typeof(ps);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.MatchCountVisitor __INIT_trampoline(/*@nullable@*/ java.io.PrintStream ps, boolean verbose, boolean printEmptyPpts, boolean ps_nullness) {
        return new daikon.diff.MatchCountVisitor(ps, verbose, printEmptyPpts);
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
        daikon.PptTopLevel ppt;
        daikon.PptTopLevel temp0 = node.__getPpt1_trampoline(true, true);
        ppt = temp0;
        if (!(ppt instanceof PptConditional)) {
            return;
        } else {
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
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.PptNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
        visit(node);
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
        java.lang.String key1;
        java.lang.String temp3 = __visitInv1_trampoline(inv1, true);
        key1 = temp3;
        java.lang.String key2;
        java.lang.String temp4 = __visitInv2_trampoline(inv2, true);
        key2 = temp4;
        if (__shouldPrint_trampoline(inv1, inv2, false, false)) {
            java.util.HashSet recallLocal;
            java.util.HashSet temp5 = recall;
            //@ assume (true) && (temp5 != null);
            recallLocal = temp5;
            recallLocal.add(key1);
            daikon.PptSlice ppt1;
            daikon.PptSlice temp6 = inv1.ppt;
            //@ assume (true) && (temp6 != null);
            ppt1 = temp6;
            java.lang.String thisPptName1;
            java.lang.String temp7 = ppt1.name();
            //@ assume (true) && (temp7 != null);
            thisPptName1 = temp7;
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

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@nullable@*/ /*@helper@*/ String visitInv1(/*@nullable@*/ daikon.inv.Invariant inv1) {
        java.lang.String key1;
        java.lang.String temp8 = "";
        key1 = temp8;
        if (inv1 != null && inv1.justified() && !__filterOut_trampoline(inv1, true)) {
            java.lang.String temp9 = __buildKey_trampoline(inv1, ";condition", true, true, true);
            key1 = temp9;
            if (__shouldPrint_trampoline(inv1, inv1, false, false)) {
                java.util.HashSet cntLocal;
                java.util.HashSet temp10 = cnt;
                //@ assume (true) && (temp10 != null);
                cntLocal = temp10;
                cntLocal.add(key1);
            }
        }
        return key1;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __visitInv1_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, boolean this_nullness) {
        return visitInv1(inv1);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@nullable@*/ /*@helper@*/ String visitInv2(/*@nullable@*/ daikon.inv.Invariant inv2) {
        java.lang.String key2;
        java.lang.String temp11 = "";
        key2 = temp11;
        if (inv2 != null && inv2.justified() && !__filterOut_trampoline(inv2, true)) {
            java.lang.String temp12 = __buildKey_trampoline(inv2, "(", true, true, true);
            key2 = temp12;
            java.util.HashSet targSetLocal;
            java.util.HashSet temp13 = targSet;
            //@ assume (true) && (temp13 != null);
            targSetLocal = temp13;
            targSetLocal.add(key2);
        }
        return key2;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __visitInv2_trampoline(/*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness) {
        return visitInv2(inv2);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (inv != null);
      @ requires (true) && (endMarker != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv.packed == \typeof(inv);
      @ requires_free endMarker.packed == \typeof(endMarker);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free endMarker.packed == \typeof(endMarker);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@nullable@*/ /*@helper@*/ String buildKey(/*@nullable@*/ daikon.inv.Invariant inv, /*@nullable@*/ java.lang.String endMarker) {
        java.lang.String thisPptName;
        java.lang.String temp14 = inv.ppt.name();
        thisPptName = temp14;
        java.lang.String thisPptName_substring;
        java.lang.String temp15 = thisPptName.substring(0, thisPptName.lastIndexOf(endMarker));
        thisPptName_substring = temp15;
        return thisPptName_substring + "$" + inv.format_using(OutputFormat.JAVA);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires endMarker_nullness || ((true) && (endMarker != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ requires_free !endMarker_nullness || ((true) && (endMarker != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free endMarker.packed == \typeof(endMarker);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __buildKey_trampoline(/*@nullable@*/ daikon.inv.Invariant inv, /*@nullable@*/ java.lang.String endMarker, boolean this_nullness, boolean inv_nullness, boolean endMarker_nullness) {
        return buildKey(inv, endMarker);
    }

    
    /**
     * Grabs the splitting condition from a pptname. 
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (s != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free s.packed == \typeof(s);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@nullable@*/ /*@helper@*/ String extractPredicate(/*@nullable@*/ java.lang.String s) {
        int cut;
        int temp16 = s.indexOf(";condition=");
        cut = temp16;
        return s.substring(cut + 12, s.lastIndexOf('\"'));
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires s_nullness || ((true) && (s != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !s_nullness || ((true) && (s != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free s.packed == \typeof(s);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __extractPredicate_trampoline(/*@nullable@*/ java.lang.String s, boolean this_nullness, boolean s_nullness) {
        return extractPredicate(s);
    }

    
    /**
     * Returns true if the pair of invariants should be printed. 
     */
        /*@ protected normal_behavior
      @ requires (true) && (inv2 != null || inv1 != null);
      @ requires (true) && (inv1 != null || inv2 != null);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ ensures (true) && (inv2 != null || inv1 != null);
      @ ensures (true) && (inv1 != null || inv2 != null);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv1 != null;
      @ ensures_free \result ==> inv2 != null;
      @*/
    protected static /*@helper@*/ boolean shouldPrint(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        int rel;
        int temp17 = DetailedStatisticsVisitor.__determineRelationship_trampoline(inv1, inv2, false, true);
        rel = temp17;
        if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2) {
            if (__filterOut_trampoline(inv1, false) || __filterOut_trampoline(inv2, false)) {
                return false;
            }
            return true;
        }
        return false;
    }

    /*@ public normal_behavior
      @ requires inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ requires_free !inv1_nullnessnode || ((true) && (inv2 != null || inv1 != null));
      @ requires_free !inv2_nullnessnode || ((true) && (inv1 != null || inv2 != null));
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \result ==> inv1 != null;
      @ ensures_free \result ==> inv2 != null;
      @ ensures_free (true) && (inv2 != null || inv1 != null);
      @ ensures_free (true) && (inv1 != null || inv2 != null);
      @*/
    public static /*@helper@*/ boolean __shouldPrint_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean inv1_nullnessnode, boolean inv2_nullnessnode) {
        return shouldPrint(inv1, inv2);
    }

    
    /**
     * Returns true iff any token of {@code inv.format_java()} contains a number other than -1, 0, 1
     * or is null.
     */
        /*@ private normal_behavior
      @ requires (true) && (inv != null);
      @ requires_free inv.packed == \typeof(inv);
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    private static /*@helper@*/ boolean filterOut(/*@nullable@*/ daikon.inv.Invariant inv) {
        java.lang.String str;
        java.lang.String temp18 = inv.format_using(OutputFormat.JAVA);
        str = temp18;
        java.util.StringTokenizer st;
        java.util.StringTokenizer temp19 = new StringTokenizer(str, " ()");
        st = temp19;
        while (st.hasMoreTokens()) {
            java.lang.String oneToken;
            java.lang.String temp20 = st.nextToken();
            oneToken = temp20;
            try {
                char firstChar;
                char temp21 = oneToken.charAt(0);
                firstChar = temp21;
                if (Character.isDigit(firstChar) || firstChar == '-') {
                    if (__acceptableNumber_trampoline(oneToken, true)) {
                    } else {
                        return true;
                    }
                }
            } catch (java.lang.NumberFormatException e) {
                System.out.println("Should never get here... NumberFormatException in filterOut: " + oneToken);
            }
        }
        return false;
    }

    /*@ public normal_behavior
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    public static /*@helper@*/ boolean __filterOut_trampoline(/*@nullable@*/ daikon.inv.Invariant inv, boolean inv_nullness) {
        return filterOut(inv);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ double calcRecall() {
        System.out.println("Recall: " + recall.size() + " / " + targSet.size());
        if (targSet.size() == 0) {
            return -1;
        }
        return (double)recall.size() / targSet.size();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ double __calcRecall_trampoline(boolean this_nullness) {
        return calcRecall();
    }

    
    /**
     * Returns true iff numLiteral represents a numeric literal string of integer or float that we
     * believe will be useful for a splitting condition. Usually that includes -1, 0, 1, and any other
     * numeric literal found in the source code.
     */
        /*@ private normal_behavior
      @ requires (true) && (numLiteral != null);
      @ requires_free numLiteral.packed == \typeof(numLiteral);
      @ ensures_free numLiteral.packed == \typeof(numLiteral);
      @*/
    private static /*@helper@*/ boolean acceptableNumber(/*@nullable@*/ java.lang.String numLiteral) {
        if (numLiteral.indexOf(".") > -1) {
            return true;
        } else {
            int num;
            int temp23 = Integer.parseInt(numLiteral);
            num = temp23;
            return (num == -1 || num == 0 || num == 1);
        }
    }

    /*@ public normal_behavior
      @ requires numLiteral_nullness || ((true) && (numLiteral != null));
      @ requires_free !numLiteral_nullness || ((true) && (numLiteral != null));
      @ ensures_free numLiteral.packed == \typeof(numLiteral);
      @*/
    public static /*@helper@*/ boolean __acceptableNumber_trampoline(/*@nullable@*/ java.lang.String numLiteral, boolean numLiteral_nullness) {
        return acceptableNumber(numLiteral);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ double calcPrecision() {
        System.out.println("Prec: " + recall.size() + " / " + cnt.size());
        if (cnt.size() == 0) {
            return -1;
        }
        return (double)recall.size() / cnt.size();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ double __calcPrecision_trampoline(boolean this_nullness) {
        return calcPrecision();
    }

    
    /**
     * Prints the results of the correct set in a human-readable format. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void printFinal() {
        for (java.lang.String ppt : goodMap.keySet()) {
            System.out.println();
            System.out.println("*****************" + ppt);
            for (java.lang.String s : goodMap.get(ppt)) {
                System.out.println(s);
            }
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ void __printFinal_trampoline(boolean this_nullness) {
        printFinal();
    }

}
