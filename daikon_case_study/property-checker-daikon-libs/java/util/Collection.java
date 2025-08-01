/* This file has been generated by Stubmaker (de.uka.ilkd.stubmaker)
 * Date: Fri Mar 28 13:47:08 CET 2008
 */
package java.util;

public interface Collection extends java.lang.Iterable
{
    
   //@ public instance ghost \seq seq;

   /*@ public normal_behavior
     @ ensures \result == seq.length;
     @ assignable \nothing;
     @ */
   public int size();
   
   /*@ public normal_behavior
     @ ensures \result == (size() == 0);
     @ assignable \nothing;
     @*/
   public boolean isEmpty();
   
   /*@ public normal_behavior
     @ ensures seq == \seq_concat(\old(seq), \seq_singleton(arg0));
     @ assignable seq;
     @*/
   public /*@helper@*/ boolean add(java.lang.Object arg0);
   public /*@helper@*/ java.util.Iterator iterator();
   
   public boolean remove(java.lang.Object arg0);
   
   /*@ public normal_behavior
     @ ensures seq == \seq_concat(\old(seq), arg0.seq);
     @ assignable seq;
     @*/
   public boolean addAll(java.util.Collection arg0);
   public boolean removeAll(java.util.Collection arg0);
   public boolean retainAll(java.util.Collection arg0);
   public void clear();
   public void __clear_trampoline(boolean b);
   
   /*@ public normal_behavior
     @ ensures \result == (\exists \bigint i; 0 <= i && i < seq.length; seq[i] == arg0);
     @ assignable \nothing;
     @*/
   public boolean contains(Object arg0);
   public boolean containsAll(java.util.Collection arg0);
   


   
   public java.lang.Object[] toArray();
   public java.lang.Object[] toArray(java.lang.Object[] arg0);
}
