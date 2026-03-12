package daikon.diff;


public class IPair  {

    //@ public invariant_free packed <: daikon.diff.IPair ==> first.packed == \typeof(first);
    //@ public invariant_free \invariant_free_for(first);
    //@ public invariant_free packed <: daikon.diff.IPair ==> second.packed == \typeof(second);
    //@ public invariant_free \invariant_free_for(second);

    public /*@nullable@*/ Object first;

    public /*@nullable@*/ Object second;

    
    /*@ private normal_behavior
      @ requires_free this.packed == daikon.diff.IPair;
      @ requires_free first.packed == \typeof(first);
      @ requires_free second.packed == \typeof(second);
      @ ensures this.first == first && this.second == second;
      @ ensures_free first.packed == \typeof(first);
      @ ensures_free second.packed == \typeof(second);
      @ ensures_free (true) && (this != null);
      @ assignable \nothing;
      @*/
    private /*@helper@*/ IPair(/*@nullable@*/ Object first, /*@nullable@*/ Object second) {
        super();

        this.first = first;
        this.second = second;
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.first == first && \result.second == second;
      @ ensures_free first.packed == \typeof(first);
      @ ensures_free second.packed == \typeof(second);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ daikon.diff.IPair __INIT_trampoline(/*@nullable@*/ Object first, /*@nullable@*/ Object second) {
        return new daikon.diff.IPair(first, second);
    }

    
    /*@ public normal_behavior
      @ requires_free first.packed == \typeof(first);
      @ requires_free second.packed == \typeof(second);
      @ ensures \result != null && \fresh(\result) && \fresh(\result.*) && \invariant_free_for(\result);
      @ ensures \result.first == first && \result.second == second;
      @ ensures_free first.packed == \typeof(first);
      @ ensures_free second.packed == \typeof(second);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ /*@helper@*/ IPair of(/*@nullable@*/ Object first, /*@nullable@*/ Object second) {
        return IPair.__INIT_trampoline(first,second);
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \fresh(\result.*) && \invariant_free_for(\result);
      @ ensures \result.first == first && \result.second == second;
      @ ensures_free first.packed == \typeof(first);
      @ ensures_free second.packed == \typeof(second);
      @ ensures_free (true) && (\result != null);
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ /*@helper@*/ daikon.diff.IPair __of_trampoline(/*@nullable@*/ Object first, /*@nullable@*/ Object second) {
        return of(first, second);
    }

}
