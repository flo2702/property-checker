package daikon.diff;

import daikon.PptMap;
import daikon.inv.Invariant;
import daikon.inv.OutputFormat;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.StringTokenizer;
import org.plumelib.util.CollectionsPlume;

/**
 * <B>MultiDiffVisitor</B> is a state-storing NodeVisitor that works across multiple files
 * regardless of the current two-file infrastructure. This allows the selection of very unique
 * invariants that occur once over an entire set of trace files.
 */
public class MultiDiffVisitor extends PrintNullDiffVisitor  {
    static {
        boolean temp0 = false;
        spinfoMode = temp0;

        java.io.PrintStream temp1 = System.out;
        //@ assume (true) && (temp1 != null);
        out = temp1;

    }


    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> currMap.packed == \typeof(currMap);
    //@ public invariant_free \invariant_free_for(currMap);
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> programPointsList.packed == \typeof(programPointsList);
    //@ public invariant_free \invariant_free_for(programPointsList);
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> freqList.packed == \typeof(freqList);
    //@ public invariant_free \invariant_free_for(freqList);
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> justifiedList.packed == \typeof(justifiedList);
    //@ public invariant_free \invariant_free_for(justifiedList);
    //@ public static invariant_free (true) && (daikon.diff.MultiDiffVisitor.out != null);
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> ((true) && (currMap != null));
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> ((true) && (programPointsList != null));
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> ((true) && (freqList != null));
    //@ public invariant_free packed <: daikon.diff.MultiDiffVisitor ==> ((true) && (justifiedList != null));

    public /*@nullable@*/ daikon.PptMap currMap;

    public /*@nullable@*/ java.util.HashSet programPointsList;

    public /*@nullable@*/ java.util.HashMap freqList;

    public /*@nullable@*/ java.util.HashSet justifiedList;

    public int total;

    public static boolean spinfoMode;

    public static /*@nullable@*/ java.io.PrintStream out;

    
    /*@ public normal_behavior
      @ requires (true) && (firstMap != null);
      @ requires_free this.packed == daikon.diff.MultiDiffVisitor;
      @ requires_free firstMap.packed == \typeof(firstMap);
      @ ensures_free firstMap.packed == \typeof(firstMap);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ MultiDiffVisitor(/*@nullable@*/ daikon.PptMap firstMap) {
        super(System.out, false);
        total = 0;


        daikon.PptMap temp2 = firstMap;
        currMap = temp2;
        java.util.HashSet temp3 = new HashSet();
        programPointsList = temp3;
        java.util.HashMap temp4 = new HashMap();
        freqList = temp4;
        java.util.HashSet temp5 = new HashSet();
        justifiedList = temp5;
    }

    /*@ public normal_behavior
      @ requires firstMap_nullness || ((true) && (firstMap != null));
      @ requires_free !firstMap_nullness || ((true) && (firstMap != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free firstMap.packed == \typeof(firstMap);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.MultiDiffVisitor __INIT_trampoline(/*@nullable@*/ daikon.PptMap firstMap, boolean firstMap_nullness) {
        return new daikon.diff.MultiDiffVisitor(firstMap);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (out_os != null);
      @ requires_free out_os.packed == \typeof(out_os);
      @ ensures_free out_os.packed == \typeof(out_os);
      @*/
    public static /*@helper@*/ void setForSpinfoOut(/*@nullable@*/ java.io.OutputStream out_os) {
        MultiDiffVisitor.out = new PrintStream(out_os, true);
        boolean temp7 = true;
        spinfoMode = temp7;
    }

    /*@ public normal_behavior
      @ requires out_os_nullness || ((true) && (out_os != null));
      @ requires_free !out_os_nullness || ((true) && (out_os != null));
      @ ensures_free out_os.packed == \typeof(out_os);
      @*/
    public static /*@helper@*/ void __setForSpinfoOut_trampoline(/*@nullable@*/ java.io.OutputStream out_os, boolean out_os_nullness) {
        setForSpinfoOut(out_os);
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
    public /*@helper@*/ void visit(/*@nullable@*/ daikon.diff.RootNode node) {
        total++;
        super.__visit_trampoline(node, true, true, true);
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
    public  /*@helper@*/ void __visit_trampoline(/*@nullable@*/ daikon.diff.RootNode node, boolean this_nullness, boolean node_nullness, boolean node_nullnessnode) {
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
        daikon.inv.Invariant temp8 = node.__getInv1_trampoline(true, true);
        inv1 = temp8;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp9 = node.__getInv2_trampoline(true, true);
        inv2 = temp9;
        if (inv1 != null && __shouldPrint_trampoline(inv1, inv2, true)) {
            java.lang.String tmpStr;
            java.lang.String temp10 = inv1.ppt.name();
            tmpStr = temp10;
            java.lang.String thisPptName;
            java.lang.String temp11 = tmpStr.substring(0, tmpStr.lastIndexOf('('));
            thisPptName = temp11;
            programPointsList.add(thisPptName);
            java.lang.String key;
            java.lang.String temp12 = thisPptName + "$" + inv1.format_using(OutputFormat.JAVA);
            key = temp12;
            java.lang.Integer val;
            java.lang.Integer temp13 = freqList.get(key);
            val = temp13;
            if (val == null) {
                freqList.put(key, 1);
            } else {
                freqList.put(key, val.intValue() + 1);
            }
            justifiedList.add(key);
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
     * Prints everything in the goodList. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void printAll() {
        if (spinfoMode) {
            __printAllSpinfo_trampoline(true);
            return;
        }
        int kill;
        int temp14 = 0;
        kill = temp14;
        int unjustifiedKill;
        int temp15 = 0;
        unjustifiedKill = temp15;
        java.util.ArrayList bigList;
        java.util.ArrayList temp16 = new ArrayList();
        bigList = temp16;
        System.out.println("Histogram**************");
        for (java.lang.String str : freqList.keySet()) {
            int freq;
            int temp18 = ((Integer)freqList.get(str)).intValue();
            freq = temp18;
            if (freq < total && justifiedList.contains(str)) {
                bigList.add(str + " Count =  " + freq);
            } else if (freq == total) {
                kill++;
            } else {
                unjustifiedKill++;
            }
        }
        System.out.println("Invariants appearing in all: " + kill);
        System.out.println("Invariants never justified: " + unjustifiedKill);
        java.util.HashMap lastMap;
        java.util.HashMap temp19 = new HashMap();
        lastMap = temp19;
        for (java.lang.String key : programPointsList) {
            lastMap.put(key, new ArrayList());
        }
        for (java.lang.String str : bigList) {
            java.util.StringTokenizer st;
            java.util.StringTokenizer temp22 = new StringTokenizer(str, "$");
            st = temp22;
            java.lang.String key;
            java.lang.String temp23 = st.nextToken();
            key = temp23;
            java.lang.String data;
            java.lang.String temp24 = st.nextToken();
            data = temp24;
            try {
                java.util.ArrayList formatAndFrequencyList;
                java.util.ArrayList temp25 = lastMap.get(key);
                //@ assume (true) && (temp25 != null);
                formatAndFrequencyList = temp25;
                formatAndFrequencyList.add(data);
            } catch (java.lang.Exception e) {
                System.out.println(key + " error in MultiDiffVisitor");
            }
        }
        for (java.util.Map.Entry entry : lastMap.entrySet()) {
            java.lang.String key;
            java.lang.String temp28 = (String)entry.getKey();
            key = temp28;
            java.util.ArrayList al;
            java.util.ArrayList temp29 = (ArrayList)entry.getValue();
            al = temp29;
            if (al.size() == 0) {
                continue;
            }
            System.out.println();
            System.out.println(key + "*****************");
            System.out.println();
            for (java.lang.Object toPrint : al) {
                System.out.println(toPrint);
            }
        }
        System.out.println();
        System.out.println();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ void __printAll_trampoline(boolean this_nullness) {
        printAll();
    }

    
    /**
     * Prints everything in the goodList, outputs as spinfo. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void printAllSpinfo() {
        java.util.ArrayList bigList;
        java.util.ArrayList temp31 = new ArrayList();
        bigList = temp31;
        for (java.lang.String str : freqList.keySet()) {
            int freq;
            int temp33 = ((Integer)freqList.get(str)).intValue();
            freq = temp33;
            if (freq < total && justifiedList.contains(str)) {
                bigList.add(str);
            }
        }
        java.util.HashMap lastMap;
        java.util.HashMap temp34 = new HashMap();
        lastMap = temp34;
        for (java.lang.String key : programPointsList) {
            lastMap.put(key, new ArrayList());
        }
        for (java.lang.String str : bigList) {
            java.util.StringTokenizer st;
            java.util.StringTokenizer temp37 = new StringTokenizer(str, "$");
            st = temp37;
            java.lang.String key;
            java.lang.String temp38 = st.nextToken();
            key = temp38;
            java.lang.String data;
            java.lang.String temp39 = st.nextToken();
            data = temp39;
            try {
                java.util.ArrayList formatAndFrequencyList;
                java.util.ArrayList temp40 = lastMap.get(key);
                //@ assume (true) && (temp40 != null);
                formatAndFrequencyList = temp40;
                formatAndFrequencyList.add(data);
            } catch (java.lang.Exception e) {
                out.println(key + " error in MultiDiffVisitor");
            }
        }
        java.lang.String lastPpt;
        java.lang.String temp42 = "";
        lastPpt = temp42;
        for (java.lang.String key : CollectionsPlume.sortedKeySet(lastMap)) {
            java.util.ArrayList al;
            java.util.ArrayList temp44 = lastMap.get(key);
            al = temp44;
            if (al.size() == 0) {
                continue;
            }
            java.util.StringTokenizer pToke;
            java.util.StringTokenizer temp45 = new StringTokenizer(key, "(");
            pToke = temp45;
            java.lang.String thisPpt;
            java.lang.String temp46 = pToke.nextToken();
            thisPpt = temp46;
            if (!lastPpt.equals(thisPpt)) {
                out.println();
                out.println("PPT_NAME " + thisPpt);
                java.lang.String temp47 = thisPpt;
                lastPpt = temp47;
            }
            for (java.lang.Object toPrint : al) {
                out.println(toPrint);
            }
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @*/
    public  /*@helper@*/ void __printAllSpinfo_trampoline(boolean this_nullness) {
        printAllSpinfo();
    }

    
    /*@ protected normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free inv1.packed == \typeof(inv1);
      @ requires_free inv2.packed == \typeof(inv2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @ ensures_free \invariant_free_for(this);
      @*/
    protected /*@helper@*/ boolean shouldPrint(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2) {
        return true;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free inv1.packed == \typeof(inv1);
      @ ensures_free inv2.packed == \typeof(inv2);
      @*/
    public  /*@helper@*/ boolean __shouldPrint_trampoline(/*@nullable@*/ daikon.inv.Invariant inv1, /*@nullable@*/ daikon.inv.Invariant inv2, boolean this_nullness) {
        return shouldPrint(inv1, inv2);
    }

}
