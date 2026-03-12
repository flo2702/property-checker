package daikon.diff;

import daikon.Daikon;
import daikon.FileIO;
import daikon.LogHelper;
import daikon.Ppt;
import daikon.PptConditional;
import daikon.PptMap;
import daikon.PptTopLevel;
import daikon.inv.Invariant;
import gnu.getopt.Getopt;
import gnu.getopt.LongOpt;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OptionalDataException;
import java.io.StreamCorruptedException;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.plumelib.util.CollectionsPlume;
import org.plumelib.util.FilesPlume;
import org.plumelib.util.MPair;
import org.plumelib.util.OrderedPairIterator;
import org.plumelib.util.StringsPlume;

/**
 * Diff is the main class for the invariant diff program. The invariant diff program outputs the
 * differences between two sets of invariants.
 *
 * <p>The following is a high-level description of the program. Each input file contains a
 * serialized PptMap or InvMap. PptMap and InvMap are similar structures, in that they both map
 * program points to invariants. However, PptMaps are much more complicated than InvMaps. PptMaps
 * are output by Daikon, and InvMaps are output by this program.
 *
 * <p>First, if either input is a PptMap, it is converted to an InvMap. Next, the two InvMaps are
 * combined to form a tree. The tree is exactly three levels deep. The first level contains the
 * root, which holds no data. Each node in the second level is a pair of Ppts, and each node in the
 * third level is a pair of Invariants. The tree is constructed by pairing the corresponding Ppts
 * and Invariants in the two PptMaps. Finally, the tree is traversed via the Visitor pattern to
 * produce output. The Visitor pattern makes it easy to extend the program, simply by writing a new
 * Visitor.
 */
public final class Diff  {
    static {
        java.util.logging.Logger temp0 = Logger.getLogger("daikon.diff.Diff");
        //@ assume (true) && (temp0 != null);
        debug = temp0;

        java.lang.String temp1 = StringsPlume.joinLines("Usage:", "    java daikon.diff.Diff [flags...] file1 [file2]", "  file1 and file2 are serialized invariants produced by Daikon.", "  If file2 is not specified, file1 is compared with the empty set.", "  For a list of flags, see the Daikon manual, which appears in the ", "  Daikon distribution and also at http://plse.cs.washington.edu/daikon/.");
        //@ assume (true) && (temp1 != null);
        usage = temp1;

        java.lang.String temp2 = "help";
        //@ assume (true) && (temp2 != null);
        HELP_SWITCH = temp2;

        java.lang.String temp3 = "invSortComparator1";
        //@ assume (true) && (temp3 != null);
        INV_SORT_COMPARATOR1_SWITCH = temp3;

        java.lang.String temp4 = "invSortComparator2";
        //@ assume (true) && (temp4 != null);
        INV_SORT_COMPARATOR2_SWITCH = temp4;

        java.lang.String temp5 = "invPairComparator";
        //@ assume (true) && (temp5 != null);
        INV_PAIR_COMPARATOR_SWITCH = temp5;

        java.lang.String temp6 = "ignore_unjustified";
        //@ assume (true) && (temp6 != null);
        IGNORE_UNJUSTIFIED_SWITCH = temp6;

        java.lang.String temp7 = "ignore_exitNN";
        //@ assume (true) && (temp7 != null);
        IGNORE_NUMBERED_EXITS_SWITCH = temp7;

        java.util.Comparator temp8 = new Ppt.NameComparator();
        //@ assume (true) && (temp8 != null);
        PPT_COMPARATOR = temp8;

    }


    //@ public invariant_free packed <: daikon.diff.Diff ==> invSortComparator1.packed == \typeof(invSortComparator1);
    //@ public invariant_free \invariant_free_for(invSortComparator1);
    //@ public invariant_free packed <: daikon.diff.Diff ==> invSortComparator2.packed == \typeof(invSortComparator2);
    //@ public invariant_free \invariant_free_for(invSortComparator2);
    //@ public invariant_free packed <: daikon.diff.Diff ==> invPairComparator.packed == \typeof(invPairComparator);
    //@ public invariant_free \invariant_free_for(invPairComparator);
    //@ public static invariant_free (true) && (daikon.diff.Diff.debug != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.usage != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.HELP_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.INV_SORT_COMPARATOR1_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.INV_SORT_COMPARATOR2_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.INV_PAIR_COMPARATOR_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.IGNORE_UNJUSTIFIED_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.IGNORE_NUMBERED_EXITS_SWITCH != null);
    //@ public static invariant_free (true) && (daikon.diff.Diff.PPT_COMPARATOR != null);
    //@ public invariant_free packed <: daikon.diff.Diff ==> ((true) && (invSortComparator1 != null));
    //@ public invariant_free packed <: daikon.diff.Diff ==> ((true) && (invSortComparator2 != null));
    //@ public invariant_free packed <: daikon.diff.Diff ==> ((true) && (invPairComparator != null));

    public static /*@nullable@*/ java.util.logging.Logger debug;

    public static /*@nullable@*/ java.lang.String usage;

    public static /*@nullable@*/ java.lang.String HELP_SWITCH;

    public static /*@nullable@*/ java.lang.String INV_SORT_COMPARATOR1_SWITCH;

    public static /*@nullable@*/ java.lang.String INV_SORT_COMPARATOR2_SWITCH;

    public static /*@nullable@*/ java.lang.String INV_PAIR_COMPARATOR_SWITCH;

    public static /*@nullable@*/ java.lang.String IGNORE_UNJUSTIFIED_SWITCH;

    public static /*@nullable@*/ java.lang.String IGNORE_NUMBERED_EXITS_SWITCH;

    public static /*@nullable@*/ java.util.Comparator PPT_COMPARATOR;

    public /*@nullable@*/ java.util.Comparator invSortComparator1;

    public /*@nullable@*/ java.util.Comparator invSortComparator2;

    public /*@nullable@*/ java.util.Comparator invPairComparator;

    public boolean examineAllPpts;

    public boolean ignoreNumberedExits;

    
    /*@ public normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ Diff() {
        this(false, false);

    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.Diff __INIT_trampoline() {
        return new daikon.diff.Diff();
    }

    
    /*@ public normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ Diff(boolean examineAllPpts) {
        this(examineAllPpts, false);

    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.Diff __INIT_trampoline(boolean examineAllPpts) {
        return new daikon.diff.Diff(examineAllPpts);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (c != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free c.packed == \typeof(c);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ Diff(boolean examineAllPpts, /*@nullable@*/ java.util.Comparator c) {
        this(examineAllPpts, false);

        __setAllInvComparators_trampoline(c, true, true);
    }

    /*@ public normal_behavior
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.Diff __INIT_trampoline(boolean examineAllPpts, /*@nullable@*/ java.util.Comparator c, boolean c_nullness) {
        return new daikon.diff.Diff(examineAllPpts, c);
    }

    
    /*@ public normal_behavior
      @ requires_free this.packed == \typeof(this);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ Diff(boolean examineAllPpts, boolean ignoreNumberedExits) {
        super();

        this.examineAllPpts = examineAllPpts;
        this.ignoreNumberedExits = ignoreNumberedExits;
        java.util.Comparator c;
        java.util.Comparator temp11 = new Invariant.ClassVarnameComparator();
        c = temp11;
        __setAllInvComparators_trampoline(c, true, true);
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.Diff __INIT_trampoline(boolean examineAllPpts, boolean ignoreNumberedExits) {
        return new daikon.diff.Diff(examineAllPpts, ignoreNumberedExits);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (d != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free sc1.packed == \typeof(sc1);
      @ requires_free sc2.packed == \typeof(sc2);
      @ requires_free pc.packed == \typeof(pc);
      @ requires_free d.packed == \typeof(d);
      @ ensures_free sc1.packed == \typeof(sc1);
      @ ensures_free sc2.packed == \typeof(sc2);
      @ ensures_free pc.packed == \typeof(pc);
      @ ensures_free d.packed == \typeof(d);
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ Diff(boolean examineAllPpts, boolean ignoreNumberedExits, /*@nullable@*/ java.lang.String sc1, /*@nullable@*/ java.lang.String sc2, /*@nullable@*/ java.lang.String pc, /*@nullable@*/ java.util.Comparator d) throws ClassNotFoundException, IllegalAccessException, InstantiationException, InvocationTargetException, NoSuchMethodException {
        super();

        this.examineAllPpts = examineAllPpts;
        this.ignoreNumberedExits = ignoreNumberedExits;
        this.invSortComparator1 = __selectComparator_trampoline(sc1, d, true);
        this.invSortComparator2 = __selectComparator_trampoline(sc2, d, true);
        this.invPairComparator = __selectComparator_trampoline(pc, d, true);
    }

    /*@ public normal_behavior
      @ requires d_nullness || ((true) && (d != null));
      @ requires_free !d_nullness || ((true) && (d != null));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free sc1.packed == \typeof(sc1);
      @ ensures_free sc2.packed == \typeof(sc2);
      @ ensures_free pc.packed == \typeof(pc);
      @ ensures_free d.packed == \typeof(d);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.Diff __INIT_trampoline(boolean examineAllPpts, boolean ignoreNumberedExits, /*@nullable@*/ java.lang.String sc1, /*@nullable@*/ java.lang.String sc2, /*@nullable@*/ java.lang.String pc, /*@nullable@*/ java.util.Comparator d, boolean d_nullness) {
        return new daikon.diff.Diff(examineAllPpts, ignoreNumberedExits, sc1, sc2, pc, d);
    }

    
    /**
     * Read two PptMap or InvMap objects from their respective files. Convert the PptMaps to InvMaps
     * as necessary, and diff the InvMaps.
     */
        /*@ public normal_behavior
      @ requires (true) && (args != null);
      @ requires_free args.packed == \typeof(args);
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void main(/*@nullable@*/ java.lang.String[] args) throws FileNotFoundException, StreamCorruptedException, OptionalDataException, IOException, ClassNotFoundException, IllegalAccessException, InstantiationException, InvocationTargetException, NoSuchMethodException {
        try {
            __mainHelper_trampoline(args, true);
        } catch (daikon.Daikon.DaikonTerminationException e) {
            daikon.Daikon.handleDaikonTerminationException(e);
        }
    }

    /*@ public normal_behavior
      @ requires args_nullness || ((true) && (args != null));
      @ requires_free !args_nullness || ((true) && (args != null));
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void __main_trampoline(/*@nullable@*/ java.lang.String[] args, boolean args_nullness) {
        main(args);
    }

    
    /**
     * This does the work of {@link #main(String[])}, but it never calls System.exit, so it is
     * appropriate to be called progrmmatically.
     */
        /*@ public normal_behavior
      @ requires (true) && (args != null);
      @ requires_free args.packed == \typeof(args);
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void mainHelper(/*@nullable@*/ java.lang.String[] args) throws FileNotFoundException, StreamCorruptedException, OptionalDataException, IOException, ClassNotFoundException, InstantiationException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
    }

    /*@ public normal_behavior
      @ requires args_nullness || ((true) && (args != null));
      @ requires_free !args_nullness || ((true) && (args != null));
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void __mainHelper_trampoline(/*@nullable@*/ java.lang.String[] args, boolean args_nullness) {
        mainHelper(args);
    }

    
    /**
     * Reads an InvMap from a file that contains a serialized InvMap or PptMap.
     *
     * @param file a file
     * @return an InvMap read from the file
     * @throws IOException if there is trouble reading the file
     * @throws ClassNotFoundException if an object in the serialized file has an unloadable class
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (file != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free file.packed == \typeof(file);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free file.packed == \typeof(file);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@nullable@*/ /*@helper@*/ InvMap readInvMap(/*@nullable@*/ java.io.File file) throws IOException, ClassNotFoundException {
        java.lang.Object o;
        java.lang.Object temp18 = FilesPlume.readObject(file);
        o = temp18;
        if (o instanceof InvMap) {
            return (InvMap)o;
        } else {
            daikon.PptMap pptMap;
            daikon.PptMap temp19 = FileIO.read_serialized_pptmap(file, false);
            pptMap = temp19;
            return __convertToInvMap_trampoline(pptMap, true, true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires file_nullness || ((true) && (file != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !file_nullness || ((true) && (file != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free file.packed == \typeof(file);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.InvMap __readInvMap_trampoline(/*@nullable@*/ java.io.File file, boolean this_nullness, boolean file_nullness) {
        return readInvMap(file);
    }

    
    /**
     * Extracts the PptTopLevel and Invariants out of a pptMap, and places them into an InvMap. Maps
     * PptTopLevel to a List of Invariants. The InvMap is a cleaner representation than the PptMap,
     * and it allows us to more easily manipulate the contents. The InvMap contains exactly the
     * elements contained in the PptMap. Conditional program points are also added as keys. Filtering
     * is done when creating the pair tree. The ppts in the InvMap must be sorted, but the invariants
     * need not be sorted.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (pptMap != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free pptMap.packed == \typeof(pptMap);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap.packed == \typeof(pptMap);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ InvMap convertToInvMap(/*@nullable@*/ daikon.PptMap pptMap) {
        daikon.diff.InvMap map;
        daikon.diff.InvMap temp20 = InvMap.__INIT_trampoline();
        map = temp20;
        java.util.NavigableSet ppts;
        java.util.NavigableSet temp21 = new TreeSet(PPT_COMPARATOR);
        ppts = temp21;
        ppts.addAll(pptMap.asCollection());
        for (daikon.PptTopLevel ppt : ppts) {
            if (ignoreNumberedExits && ppt.ppt_name.isNumberedExitPoint()) {
                continue;
            }
            java.util.List invs;
            java.util.List temp23 = CollectionsPlume.sortList(ppt.getInvariants(), PptTopLevel.icfp);
            invs = temp23;
            map.__put_trampoline(ppt, invs, true, true, true);
            if (examineAllPpts) {
                for (daikon.PptConditional pptCond : ppt.cond_iterable()) {
                    java.util.List invsCond;
                    java.util.List temp25 = CollectionsPlume.sortList(pptCond.getInvariants(), PptTopLevel.icfp);
                    invsCond = temp25;
                    map.__put_trampoline(pptCond, invsCond, true, true, true);
                }
            }
        }
        return map;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires pptMap_nullness || ((true) && (pptMap != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !pptMap_nullness || ((true) && (pptMap != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap.packed == \typeof(pptMap);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.InvMap __convertToInvMap_trampoline(/*@nullable@*/ daikon.PptMap pptMap, boolean this_nullness, boolean pptMap_nullness) {
        return convertToInvMap(pptMap);
    }

    
    /**
     * Returns a pair tree of corresponding program points, and corresponding invariants at each
     * program point. This tree can be walked to determine differences between the sets of invariants.
     * Calls diffInvMap and asks to include all justified invariants.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (map1 != null);
      @ requires (true) && (map2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free map1.packed == \typeof(map1);
      @ requires_free map2.packed == \typeof(map2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ RootNode diffInvMap(/*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2) {
        return __diffInvMap_trampoline(map1, map2, true, true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires map1_nullness || ((true) && (map1 != null));
      @ requires map2_nullness || ((true) && (map2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !map1_nullness || ((true) && (map1 != null));
      @ requires_free !map2_nullness || ((true) && (map2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.RootNode __diffInvMap_trampoline(/*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean this_nullness, boolean map1_nullness, boolean map2_nullness) {
        return diffInvMap(map1, map2);
    }

    
    /**
     * Returns a pair tree of corresponding program points, and corresponding invariants at each
     * program point. This tree can be walked to determine differences between the sets of invariants.
     * The tree consists of the invariants in map1 and map2. If includeUnjustified is true, the
     * unjustified invariants are included.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (map1 != null);
      @ requires (true) && (map2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free map1.packed == \typeof(map1);
      @ requires_free map2.packed == \typeof(map2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ RootNode diffInvMap(/*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified) {
        daikon.diff.RootNode root;
        daikon.diff.RootNode temp26 = RootNode.__INIT_trampoline();
        root = temp26;
        java.util.Comparator comp;
        java.util.Comparator temp27 = PPT_COMPARATOR;
        //@ assume (true) && (temp27 != null);
        comp = temp27;
        org.plumelib.util.OrderedPairIterator opi;
        org.plumelib.util.OrderedPairIterator temp28 = new OrderedPairIterator(map1.__pptSortedIterator_trampoline(comp, true, true), map2.__pptSortedIterator_trampoline(comp, true, true), comp);
        opi = temp28;
        while (opi.hasNext()) {
            org.plumelib.util.MPair ppts;
            org.plumelib.util.MPair temp29 = opi.next();
            ppts = temp29;
            //@ assume ppts.first instanceof PptTopLevel;
            //@ assume ppts.second instanceof PptTopLevel;
            daikon.PptTopLevel ppt1;
            daikon.PptTopLevel temp30 = (PptTopLevel)ppts.first;
            ppt1 = temp30;
            daikon.PptTopLevel ppt2;
            daikon.PptTopLevel temp31 = (PptTopLevel)ppts.second;
            //@ assert (true) && (ppt2 != null || temp31 != null);
            ppt2 = temp31;
            //@ ghost int idx = opi.idx;
            //@ ghost int len = opi.len;
            __addChildToRootNode_trampoline(root, ppt1, ppt2, map1, map2, includeUnjustified, true, true, true, true, false, true);
            //@ set opi.idx = idx;
            //@ set opi.len = len;
        }
        return root;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires map1_nullness || ((true) && (map1 != null));
      @ requires map2_nullness || ((true) && (map2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !map1_nullness || ((true) && (map1 != null));
      @ requires_free !map2_nullness || ((true) && (map2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.RootNode __diffInvMap_trampoline(/*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified, boolean this_nullness, boolean map1_nullness, boolean map2_nullness) {
        return diffInvMap(map1, map2, includeUnjustified);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (root != null);
      @ requires (true) && (map1 != null);
      @ requires (true) && (map2 != null);
      @ requires (true) && (ppt2 != null || ppt1 != null);
      @ requires (true) && (ppt1 != null || ppt2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free root.packed == \typeof(root);
      @ requires_free ppt1.packed == \typeof(ppt1);
      @ requires_free ppt2.packed == \typeof(ppt2);
      @ requires_free map1.packed == \typeof(map1);
      @ requires_free map2.packed == \typeof(map2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free root.packed == \typeof(root);
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void addChildToRootNode(/*@nullable@*/ daikon.diff.RootNode root, /*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2, /*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified) {
        if (__shouldAdd_trampoline(ppt1, true) || __shouldAdd_trampoline(ppt2, true)) {
            daikon.diff.PptNode node;
            daikon.diff.PptNode temp32 = __diffPptTopLevel_trampoline(ppt1, ppt2, map1, map2, includeUnjustified, true, true, true, false, true);
            //@ assume (true) && (temp32 instanceof Void || temp32 instanceof daikon.diff.Node && ((daikon.diff.Node)temp32).userObject != null && (((daikon.diff.Node)temp32).userObject.first != null || ((daikon.diff.Node)temp32).userObject.second != null));
            node = temp32;
            root.__add_trampoline(node, true, true, true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires root_nullness || ((true) && (root != null));
      @ requires map1_nullness || ((true) && (map1 != null));
      @ requires map2_nullness || ((true) && (map2 != null));
      @ requires ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !root_nullness || ((true) && (root != null));
      @ requires_free !map1_nullness || ((true) && (map1 != null));
      @ requires_free !map2_nullness || ((true) && (map2 != null));
      @ requires_free !ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires_free !ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free root.packed == \typeof(root);
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @*/
    public  /*@helper@*/ void __addChildToRootNode_trampoline(/*@nullable@*/ daikon.diff.RootNode root, /*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2, /*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified, boolean this_nullness, boolean root_nullness, boolean map1_nullness, boolean map2_nullness, boolean ppt1_nullnessnode, boolean ppt2_nullnessnode) {
        addChildToRootNode(root, ppt1, ppt2, map1, map2, includeUnjustified);
    }

    
    /**
     * Diffs two PptMaps by converting them to InvMaps. Provided for compatibiliy with legacy code.
     * Calls diffPptMap and asks to include all invariants.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (pptMap1 != null);
      @ requires (true) && (pptMap2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free pptMap1.packed == \typeof(pptMap1);
      @ requires_free pptMap2.packed == \typeof(pptMap2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap1.packed == \typeof(pptMap1);
      @ ensures_free pptMap2.packed == \typeof(pptMap2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ RootNode diffPptMap(/*@nullable@*/ daikon.PptMap pptMap1, /*@nullable@*/ daikon.PptMap pptMap2) {
        return __diffPptMap_trampoline(pptMap1, pptMap2, true, true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires pptMap1_nullness || ((true) && (pptMap1 != null));
      @ requires pptMap2_nullness || ((true) && (pptMap2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !pptMap1_nullness || ((true) && (pptMap1 != null));
      @ requires_free !pptMap2_nullness || ((true) && (pptMap2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap1.packed == \typeof(pptMap1);
      @ ensures_free pptMap2.packed == \typeof(pptMap2);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.RootNode __diffPptMap_trampoline(/*@nullable@*/ daikon.PptMap pptMap1, /*@nullable@*/ daikon.PptMap pptMap2, boolean this_nullness, boolean pptMap1_nullness, boolean pptMap2_nullness) {
        return diffPptMap(pptMap1, pptMap2);
    }

    
    /**
     * Diffs two PptMaps by converting them to InvMaps. Provided for compatibiliy with legacy code. If
     * includeUnjustified is true, the unjustified invariants are included.
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (pptMap1 != null);
      @ requires (true) && (pptMap2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free pptMap1.packed == \typeof(pptMap1);
      @ requires_free pptMap2.packed == \typeof(pptMap2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap1.packed == \typeof(pptMap1);
      @ ensures_free pptMap2.packed == \typeof(pptMap2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ RootNode diffPptMap(/*@nullable@*/ daikon.PptMap pptMap1, /*@nullable@*/ daikon.PptMap pptMap2, boolean includeUnjustified) {
        daikon.diff.InvMap map1;
        daikon.diff.InvMap temp33 = __convertToInvMap_trampoline(pptMap1, true, true);
        map1 = temp33;
        daikon.diff.InvMap map2;
        daikon.diff.InvMap temp34 = __convertToInvMap_trampoline(pptMap2, true, true);
        map2 = temp34;
        return __diffInvMap_trampoline(map1, map2, includeUnjustified, true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires pptMap1_nullness || ((true) && (pptMap1 != null));
      @ requires pptMap2_nullness || ((true) && (pptMap2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !pptMap1_nullness || ((true) && (pptMap1 != null));
      @ requires_free !pptMap2_nullness || ((true) && (pptMap2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptMap1.packed == \typeof(pptMap1);
      @ ensures_free pptMap2.packed == \typeof(pptMap2);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.RootNode __diffPptMap_trampoline(/*@nullable@*/ daikon.PptMap pptMap1, /*@nullable@*/ daikon.PptMap pptMap2, boolean includeUnjustified, boolean this_nullness, boolean pptMap1_nullness, boolean pptMap2_nullness) {
        return diffPptMap(pptMap1, pptMap2, includeUnjustified);
    }

    
    /**
     * Returns true if the program point should be added to the tree, false otherwise. 
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt.packed == \typeof(ppt);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    private /*@helper@*/ boolean shouldAdd(/*@nullable@*/ daikon.PptTopLevel ppt) {
        if (examineAllPpts) {
            return true;
        } else {
            if (ppt == null) {
                return false;
            } else if (ppt.ppt_name.isEnterPoint()) {
                return true;
            } else if (ppt.ppt_name.isCombinedExitPoint()) {
                return true;
            } else {
                return false;
            }
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ assignable \nothing;
      @*/
    public  /*@helper@*/ boolean __shouldAdd_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt, boolean this_nullness) {
        return shouldAdd(ppt);
    }

    
    /**
     * Takes a pair of corresponding top-level program points and maps, and returns a tree of the
     * corresponding invariants. Either of the program points may be null. If includeUnjustied is
     * true, the unjustified invariants are included.
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (map1 != null);
      @ requires (true) && (map2 != null);
      @ requires (true) && (ppt2 != null || ppt1 != null);
      @ requires (true) && (ppt1 != null || ppt2 != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt1.packed == \typeof(ppt1);
      @ requires_free ppt2.packed == \typeof(ppt2);
      @ requires_free map1.packed == \typeof(map1);
      @ requires_free map2.packed == \typeof(map2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    private /*@nullable@*/ /*@helper@*/ PptNode diffPptTopLevel(/*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2, /*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified) {
        daikon.diff.PptNode pptNode;
        daikon.diff.PptNode temp35 = PptNode.__INIT_trampoline(ppt1,ppt2, true, true);
        //@ assume (true) && (temp35 instanceof Void || temp35 instanceof daikon.diff.Node && ((daikon.diff.Node)temp35).userObject != null && (((daikon.diff.Node)temp35).userObject.first != null || ((daikon.diff.Node)temp35).userObject.second != null));
        pptNode = temp35;
        java.util.List invs1;
        
        if (ppt1 != null) {
            java.util.List temp37 = map1.__get_trampoline(ppt1, true, true);
            invs1 = temp37;
            java.util.Comparator comp;
            java.util.Comparator temp38 = invSortComparator1;
            //@ assume (true) && (temp38 != null);
            comp = temp38;
            Collections.sort(invs1, comp);
        } else {
            java.util.List temp39 = new ArrayList();
            invs1 = temp39;
        }
        java.util.List invs2;
        
        if (ppt2 != null) {
            java.util.List temp41 = map2.__get_trampoline(ppt2, true, true);
            invs2 = temp41;
            java.util.Comparator comp;
            java.util.Comparator temp42 = invSortComparator2;
            //@ assume (true) && (temp42 != null);
            comp = temp42;
            Collections.sort(invs2, comp);
        } else {
            java.util.List temp43 = new ArrayList();
            invs2 = temp43;
        }
        __addChildrenToPptTopLevelNode_trampoline(pptNode, invs1, invs2, includeUnjustified, true, true, true, true, true);
        return pptNode;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires map1_nullness || ((true) && (map1 != null));
      @ requires map2_nullness || ((true) && (map2 != null));
      @ requires ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !map1_nullness || ((true) && (map1 != null));
      @ requires_free !map2_nullness || ((true) && (map2 != null));
      @ requires_free !ppt1_nullnessnode || ((true) && (ppt2 != null || ppt1 != null));
      @ requires_free !ppt2_nullnessnode || ((true) && (ppt1 != null || ppt2 != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt1.packed == \typeof(ppt1);
      @ ensures_free ppt2.packed == \typeof(ppt2);
      @ ensures_free map1.packed == \typeof(map1);
      @ ensures_free map2.packed == \typeof(map2);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (true) && (\result instanceof Void || \result instanceof daikon.diff.Node && ((daikon.diff.Node)\result).userObject != null && (((daikon.diff.Node)\result).userObject.first != null || ((daikon.diff.Node)\result).userObject.second != null));
      @ ensures_free (true) && (ppt2 != null || ppt1 != null);
      @ ensures_free (true) && (ppt1 != null || ppt2 != null);
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ daikon.diff.PptNode __diffPptTopLevel_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt1, /*@nullable@*/ daikon.PptTopLevel ppt2, /*@nullable@*/ daikon.diff.InvMap map1, /*@nullable@*/ daikon.diff.InvMap map2, boolean includeUnjustified, boolean this_nullness, boolean map1_nullness, boolean map2_nullness, boolean ppt1_nullnessnode, boolean ppt2_nullnessnode) {
        return diffPptTopLevel(ppt1, ppt2, map1, map2, includeUnjustified);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (pptNode != null);
      @ requires (true) && (invs1 != null);
      @ requires (true) && (invs2 != null);
      @ requires (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free pptNode.packed == \typeof(pptNode);
      @ requires_free invs1.packed == \typeof(invs1);
      @ requires_free invs2.packed == \typeof(invs2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptNode.packed == \typeof(pptNode);
      @ ensures_free invs1.packed == \typeof(invs1);
      @ ensures_free invs2.packed == \typeof(invs2);
      @ ensures_free (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void addChildrenToPptTopLevelNode(/*@nullable@*/ daikon.diff.PptNode pptNode, /*@nullable@*/ java.util.List invs1, /*@nullable@*/ java.util.List invs2, boolean includeUnjustified) {
        java.util.Iterator opi;
        java.util.Iterator temp44 = new OrderedPairIterator(invs1.iterator(), invs2.iterator(), invPairComparator);
        opi = temp44;
        while (opi.hasNext()) {
            org.plumelib.util.MPair invariants;
            org.plumelib.util.MPair temp45 = opi.next();
            invariants = temp45;
            daikon.inv.Invariant inv1;
            daikon.inv.Invariant temp46 = invariants.first;
            inv1 = temp46;
            daikon.inv.Invariant inv2;
            daikon.inv.Invariant temp47 = invariants.second;
            inv2 = temp47;
            __addChildToPptTopLevelNode_trampoline(pptNode, inv1, inv2, includeUnjustified, true, true, true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires pptNode_nullness || ((true) && (pptNode != null));
      @ requires invs1_nullness || ((true) && (invs1 != null));
      @ requires invs2_nullness || ((true) && (invs2 != null));
      @ requires pptNode_nullnessnode || ((true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !pptNode_nullness || ((true) && (pptNode != null));
      @ requires_free !invs1_nullness || ((true) && (invs1 != null));
      @ requires_free !invs2_nullness || ((true) && (invs2 != null));
      @ requires_free !pptNode_nullnessnode || ((true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptNode.packed == \typeof(pptNode);
      @ ensures_free invs1.packed == \typeof(invs1);
      @ ensures_free invs2.packed == \typeof(invs2);
      @ ensures_free (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @*/
    public  /*@helper@*/ void __addChildrenToPptTopLevelNode_trampoline(/*@nullable@*/ daikon.diff.PptNode pptNode, /*@nullable@*/ java.util.List invs1, /*@nullable@*/ java.util.List invs2, boolean includeUnjustified, boolean this_nullness, boolean pptNode_nullness, boolean invs1_nullness, boolean invs2_nullness, boolean pptNode_nullnessnode) {
        addChildrenToPptTopLevelNode(pptNode, invs1, invs2, includeUnjustified);
    }

    
    /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (pptNode != null);
      @ requires (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @ requires_free this.packed == \typeof(this);
      @ requires_free pptNode.packed == \typeof(pptNode);
      @ requires_free arg1.packed == \typeof(arg1);
      @ requires_free arg2.packed == \typeof(arg2);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptNode.packed == \typeof(pptNode);
      @ ensures_free arg1.packed == \typeof(arg1);
      @ ensures_free arg2.packed == \typeof(arg2);
      @ ensures_free (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void addChildToPptTopLevelNode(/*@nullable@*/ daikon.diff.PptNode pptNode, /*@nullable@*/ daikon.inv.Invariant arg1, /*@nullable@*/ daikon.inv.Invariant arg2, boolean includeUnjustified) {
        daikon.inv.Invariant inv1;
        daikon.inv.Invariant temp48 = arg1;
        inv1 = temp48;
        daikon.inv.Invariant inv2;
        daikon.inv.Invariant temp49 = arg2;
        inv2 = temp49;
        if (!includeUnjustified) {
            if ((inv1 != null) && !inv1.justified()) {
                daikon.inv.Invariant temp50 = null;
                inv1 = temp50;
            }
            if ((inv2 != null) && !inv2.justified()) {
                daikon.inv.Invariant temp51 = null;
                inv2 = temp51;
            }
        }
        if ((inv1 != null) || (inv2 != null)) {
            daikon.diff.InvNode invNode;
            daikon.diff.InvNode temp52 = InvNode.__INIT_trampoline(inv1,inv2, false, false);
            invNode = temp52;
            pptNode.__add_trampoline(invNode, true, true, true, true);
        }
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires pptNode_nullness || ((true) && (pptNode != null));
      @ requires pptNode_nullnessnode || ((true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null)));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !pptNode_nullness || ((true) && (pptNode != null));
      @ requires_free !pptNode_nullnessnode || ((true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null)));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free pptNode.packed == \typeof(pptNode);
      @ ensures_free arg1.packed == \typeof(arg1);
      @ ensures_free arg2.packed == \typeof(arg2);
      @ ensures_free (true) && (pptNode instanceof Void || pptNode instanceof daikon.diff.Node && ((daikon.diff.Node)pptNode).userObject != null && (((daikon.diff.Node)pptNode).userObject.first != null || ((daikon.diff.Node)pptNode).userObject.second != null));
      @*/
    public  /*@helper@*/ void __addChildToPptTopLevelNode_trampoline(/*@nullable@*/ daikon.diff.PptNode pptNode, /*@nullable@*/ daikon.inv.Invariant arg1, /*@nullable@*/ daikon.inv.Invariant arg2, boolean includeUnjustified, boolean this_nullness, boolean pptNode_nullness, boolean pptNode_nullnessnode) {
        addChildToPptTopLevelNode(pptNode, arg1, arg2, includeUnjustified);
    }

    
    /**
     * Use the comparator for sorting both sets and creating the pair tree. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (c != null);
      @ requires_free this.packed <: java.lang.Object;
      @ requires_free c.packed == \typeof(c);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invPairComparator != null;
      @ ensures_free this.invSortComparator1 != null;
      @ ensures_free this.invSortComparator2 != null;
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void setAllInvComparators(/*@nullable@*/ java.util.Comparator c) {
        __setInvSortComparator1_trampoline(c, true, true);
        __setInvSortComparator2_trampoline(c, true, true);
        __setInvPairComparator_trampoline(c, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invPairComparator != null;
      @ ensures_free this.invSortComparator1 != null;
      @ ensures_free this.invSortComparator2 != null;
      @*/
    public  /*@helper@*/ void __setAllInvComparators_trampoline(/*@nullable@*/ java.util.Comparator c, boolean this_nullness, boolean c_nullness) {
        setAllInvComparators(c);
    }

    
    /**
     * If the classname is non-null, returns the comparator named by the classname. Else, returns the
     * default.
     */
        /*@ private normal_behavior
      @ requires (true) && (defaultComparator != null);
      @ requires_free classname.packed == \typeof(classname);
      @ requires_free defaultComparator.packed == \typeof(defaultComparator);
      @ ensures_free classname.packed == \typeof(classname);
      @ ensures_free defaultComparator.packed == \typeof(defaultComparator);
      @ ensures_free (true) && (\result != null);
      @*/
    private static /*@nullable@*/ /*@helper@*/ Comparator selectComparator(/*@nullable@*/ java.lang.String classname, /*@nullable@*/ java.util.Comparator defaultComparator) throws ClassNotFoundException, IllegalAccessException, InstantiationException, InvocationTargetException, NoSuchMethodException {
        if (classname != null) {
            java.lang.Class cls;
            java.lang.Class temp53 = Class.forName(classname);
            cls = temp53;
            java.util.Comparator cmp;
            java.util.Comparator temp54 = (Comparator)cls.getDeclaredConstructor().newInstance();
            cmp = temp54;
            return cmp;
        } else {
            return defaultComparator;
        }
    }

    /*@ public normal_behavior
      @ requires defaultComparator_nullness || ((true) && (defaultComparator != null));
      @ requires_free !defaultComparator_nullness || ((true) && (defaultComparator != null));
      @ ensures_free classname.packed == \typeof(classname);
      @ ensures_free defaultComparator.packed == \typeof(defaultComparator);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ /*@helper@*/ java.util.Comparator __selectComparator_trampoline(/*@nullable@*/ java.lang.String classname, /*@nullable@*/ java.util.Comparator defaultComparator, boolean defaultComparator_nullness) {
        return selectComparator(classname, defaultComparator);
    }

    
    /**
     * Use the comparator for sorting the first set. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (c != null);
      @ requires_free this.packed <: java.lang.Object;
      @ requires_free c.packed == \typeof(c);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invSortComparator1 != null;
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void setInvSortComparator1(/*@nullable@*/ java.util.Comparator c) {
        java.util.Comparator temp55 = c;
        invSortComparator1 = temp55;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invSortComparator1 != null;
      @*/
    public  /*@helper@*/ void __setInvSortComparator1_trampoline(/*@nullable@*/ java.util.Comparator c, boolean this_nullness, boolean c_nullness) {
        setInvSortComparator1(c);
    }

    
    /**
     * Use the comparator for sorting the second set. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (c != null);
      @ requires_free this.packed <: java.lang.Object;
      @ requires_free c.packed == \typeof(c);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invSortComparator2 != null;
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void setInvSortComparator2(/*@nullable@*/ java.util.Comparator c) {
        java.util.Comparator temp56 = c;
        invSortComparator2 = temp56;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invSortComparator2 != null;
      @*/
    public  /*@helper@*/ void __setInvSortComparator2_trampoline(/*@nullable@*/ java.util.Comparator c, boolean this_nullness, boolean c_nullness) {
        setInvSortComparator2(c);
    }

    
    /**
     * Use the comparator for creating the pair tree. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (c != null);
      @ requires_free this.packed <: java.lang.Object;
      @ requires_free c.packed == \typeof(c);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invPairComparator != null;
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void setInvPairComparator(/*@nullable@*/ java.util.Comparator c) {
        java.util.Comparator temp57 = c;
        invPairComparator = temp57;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed <: java.lang.Object;
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free this.invPairComparator != null;
      @*/
    public  /*@helper@*/ void __setInvPairComparator_trampoline(/*@nullable@*/ java.util.Comparator c, boolean this_nullness, boolean c_nullness) {
        setInvPairComparator(c);
    }

}
