package daikon.diff;

import daikon.FileIO;
import daikon.Global;
import daikon.PptTopLevel;
import daikon.inv.Invariant;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import org.plumelib.util.CollectionsPlume;

/**
 * Maps ppts to lists of invariants. Has an iterator to return the ppts in the order they were
 * inserted.
 *
 * <p>The ppts are used only as keys in this data structure. Do not attempt to look up invariants
 * stored in the ppts; instead, obtain invariants via the get() method.
 */
public class InvMap implements Serializable  {
    static {
        long temp0 = 20090612L;
        serialVersionUID = temp0;

    }


    //@ public invariant_free packed <: daikon.diff.InvMap ==> pptToInvs.packed == \typeof(pptToInvs);
    //@ public invariant_free \invariant_free_for(pptToInvs);
    //@ public invariant_free packed <: daikon.diff.InvMap ==> ppts.packed == \typeof(ppts);
    //@ public invariant_free \invariant_free_for(ppts);
    //@ public invariant_free packed <: daikon.diff.InvMap ==> ((true) && (pptToInvs != null));
    //@ public invariant_free packed <: daikon.diff.InvMap ==> ((true) && (ppts != null));

    public static long serialVersionUID;

    public /*@nullable@*/ java.util.Map pptToInvs;

    public /*@nullable@*/ java.util.List ppts;

    
    /*@ public normal_behavior
      @ requires_free this.packed == daikon.diff.InvMap;
      @ ensures_free (true) && (this != null);
      @*/
    public /*@helper@*/ InvMap() {
        super();
        pptToInvs = new HashMap();

        ppts = new ArrayList();


    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.InvMap __INIT_trampoline() {
        return new daikon.diff.InvMap();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (ppt != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt.packed == \typeof(ppt);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void addPpt(/*@nullable@*/ daikon.PptTopLevel ppt) {
        __put_trampoline(ppt, new ArrayList(), true, true, true);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires ppt_nullness || ((true) && (ppt != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !ppt_nullness || ((true) && (ppt != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @*/
    public  /*@helper@*/ void __addPpt_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt, boolean this_nullness, boolean ppt_nullness) {
        addPpt(ppt);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (ppt != null);
      @ requires (true) && (invs != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt.packed == \typeof(ppt);
      @ requires_free invs.packed == \typeof(invs);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free invs.packed == \typeof(invs);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void put(/*@nullable@*/ daikon.PptTopLevel ppt, /*@nullable@*/ java.util.List invs) {
        if (ppts.contains(ppt)) {
            throw new Error("Tried to add duplicate PptTopLevel " + ppt.name());
        }
        ppts.add(ppt);
        pptToInvs.put(ppt, invs);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires ppt_nullness || ((true) && (ppt != null));
      @ requires invs_nullness || ((true) && (invs != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !ppt_nullness || ((true) && (ppt != null));
      @ requires_free !invs_nullness || ((true) && (invs != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free invs.packed == \typeof(invs);
      @*/
    public  /*@helper@*/ void __put_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt, /*@nullable@*/ java.util.List invs, boolean this_nullness, boolean ppt_nullness, boolean invs_nullness) {
        put(ppt, invs);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (ppt != null);
      @ requires (true) && (inv != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt.packed == \typeof(ppt);
      @ requires_free inv.packed == \typeof(inv);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free inv.packed == \typeof(inv);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@helper@*/ void add(/*@nullable@*/ daikon.PptTopLevel ppt, /*@nullable@*/ daikon.inv.Invariant inv) {
        if (!ppts.contains(ppt)) {
            throw new Error("ppt has not yet been added: " + ppt.name());
        }
        __get_trampoline(ppt, true, true).add(inv);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires ppt_nullness || ((true) && (ppt != null));
      @ requires inv_nullness || ((true) && (inv != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !ppt_nullness || ((true) && (ppt != null));
      @ requires_free !inv_nullness || ((true) && (inv != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free inv.packed == \typeof(inv);
      @*/
    public  /*@helper@*/ void __add_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt, /*@nullable@*/ daikon.inv.Invariant inv, boolean this_nullness, boolean ppt_nullness, boolean inv_nullness) {
        add(ppt, inv);
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (ppt != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ppt.packed == \typeof(ppt);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ List get(/*@nullable@*/ daikon.PptTopLevel ppt) {
        if (!pptToInvs.containsKey(ppt)) {
            throw new Error("ppt has not yet been added: " + ppt.name());
        }
        return pptToInvs.get(ppt);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires ppt_nullness || ((true) && (ppt != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !ppt_nullness || ((true) && (ppt != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ppt.packed == \typeof(ppt);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.util.List __get_trampoline(/*@nullable@*/ daikon.PptTopLevel ppt, boolean this_nullness, boolean ppt_nullness) {
        return get(ppt);
    }

    
    /**
     * Returns an iterator over the ppts, in the order they were added to the map. Each element is a
     * PptTopLevel. These ppts are only used as keys: do not look in these Ppts to find the invariants
     * associated with them in the InvMap! Use invariantIterator instead.
     *
     * @see #invariantIterator()
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ Iterator pptIterator() {
        return ppts.iterator();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.util.Iterator __pptIterator_trampoline(boolean this_nullness) {
        return pptIterator();
    }

    
    /**
     * Returns an iterable over the ppts, in the order they were added to the map. Each element is a
     * PptTopLevel. These ppts are only used as keys: do not look in these Ppts to find the invariants
     * associated with them in the InvMap! Use invariantIterator instead.
     *
     * @see #invariantIterator()
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ Iterable pptIterable() {
        return CollectionsPlume.iteratorToIterable(__pptIterator_trampoline(true));
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.Iterable __pptIterable_trampoline(boolean this_nullness) {
        return pptIterable();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (c != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free c.packed == \typeof(c);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ Iterator pptSortedIterator(/*@nullable@*/ java.util.Comparator c) {
        java.util.List ppts_copy;
        java.util.List temp1 = new ArrayList(ppts);
        ppts_copy = temp1;
        Collections.sort(ppts_copy, c);
        return ppts_copy.iterator();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires c_nullness || ((true) && (c != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !c_nullness || ((true) && (c != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free c.packed == \typeof(c);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.util.Iterator __pptSortedIterator_trampoline(/*@nullable@*/ java.util.Comparator c, boolean this_nullness, boolean c_nullness) {
        return pptSortedIterator(c);
    }

    
    /**
     * Returns an iterator over the invariants in this. 
     */
        /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @*/
    public /*@nullable@*/ /*@helper@*/ Iterator invariantIterator() {
        java.util.ArrayList answer;
        java.util.ArrayList temp2 = new ArrayList();
        answer = temp2;
        for (daikon.PptTopLevel ppt : ppts) {
            answer.addAll(__get_trampoline(ppt, true, true));
        }
        return answer.iterator();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.util.Iterator __invariantIterator_trampoline(boolean this_nullness) {
        return invariantIterator();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@nullable@*/ /*@helper@*/ String toString() {
        java.lang.String result;
        java.lang.String temp4 = "";
        result = temp4;
        for (daikon.PptTopLevel ppt : __pptIterable_trampoline(true)) {
            result += ppt.name() + Global.lineSep;
            java.util.List invs;
            java.util.List temp6 = __get_trampoline(ppt, true, true);
            invs = temp6;
            for (daikon.inv.Invariant inv : invs) {
                result += "  " + inv.format() + Global.lineSep;
            }
        }
        return result;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public  /*@nullable@*/ /*@helper@*/ java.lang.String __toString_trampoline(boolean this_nullness) {
        return toString();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (this != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free \invariant_free_for(this);
      @ assignable \nothing;
      @*/
    public /*@helper@*/ int size() {
        int size1;
        int temp8 = ppts.size();
        size1 = temp8;
        int size2;
        int temp9 = pptToInvs.size();
        size2 = temp9;
        assert size1 == size2;
        return size1;
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ assignable \nothing;
      @*/
    public  /*@helper@*/ int __size_trampoline(boolean this_nullness) {
        return size();
    }

    
    /**
     * Include FileIO.new_decl_format in the stream 
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (oos != null);
      @ requires daikon.FileIO.new_decl_format != null;
      @ requires_free this.packed == \typeof(this);
      @ requires_free oos.packed == \typeof(oos);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free oos.packed == \typeof(oos);
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void writeObject(/*@nullable@*/ java.io.ObjectOutputStream oos) throws IOException {
        oos.defaultWriteObject();
        oos.writeObject(FileIO.new_decl_format);
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires oos_nullness || ((true) && (oos != null));
      @ requires daikon.FileIO.new_decl_format != null;
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !oos_nullness || ((true) && (oos != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free oos.packed == \typeof(oos);
      @*/
    public  /*@helper@*/ void __writeObject_trampoline(/*@nullable@*/ java.io.ObjectOutputStream oos, boolean this_nullness, boolean oos_nullness) {
        writeObject(oos);
    }

    
    /**
     * Serialize pptmap and FileIO.new_decl_format 
     */
        /*@ private normal_behavior
      @ requires (true) && (this != null);
      @ requires (true) && (ois != null);
      @ requires_free this.packed == \typeof(this);
      @ requires_free ois.packed == \typeof(ois);
      @ requires_free \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ois.packed == \typeof(ois);
      @ ensures_free daikon.FileIO.new_decl_format != null;
      @ ensures_free \invariant_free_for(this);
      @*/
    private /*@helper@*/ void readObject(/*@nullable@*/ java.io.ObjectInputStream ois) throws ClassNotFoundException, IOException {
        ois.defaultReadObject();
        FileIO.new_decl_format = (Boolean)ois.readObject();
    }

    /*@ public normal_behavior
      @ requires this_nullness || ((true) && (this != null));
      @ requires ois_nullness || ((true) && (ois != null));
      @ requires_free !this_nullness || ((true) && (this != null));
      @ requires_free !ois_nullness || ((true) && (ois != null));
      @ ensures \invariant_free_for(this);
      @ ensures_free this.packed == \typeof(this);
      @ ensures_free ois.packed == \typeof(ois);
      @ ensures_free daikon.FileIO.new_decl_format != null;
      @*/
    public  /*@helper@*/ void __readObject_trampoline(/*@nullable@*/ java.io.ObjectInputStream ois, boolean this_nullness, boolean ois_nullness) {
        readObject(ois);
    }

}
