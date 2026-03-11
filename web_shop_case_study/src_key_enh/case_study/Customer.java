package case_study;


public final class Customer  {

    //@ public invariant_free packed <: case_study.Customer ==> name.packed == \typeof(name);
    //@ public invariant_free \invariant_free_for(name);
    //@ public invariant_free packed <: case_study.Customer ==> ((true) && (name != null));
    //@ public invariant_free packed <: case_study.Customer ==> ((14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150));

    public /*@nullable@*/ java.lang.String name;

    public int age;

    
    /*@ public normal_behavior
      @ requires (true) && (name != null);
      @ requires (14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150);
      @ requires_free this.packed == \typeof(this);
      @ requires_free name.packed == \typeof(name);
      @ ensures (age >= 0) && (this != null && this.age >= age);
      @ ensures this.name == name && this.age == age;
      @ ensures_free name.packed == \typeof(name);
      @ ensures_free (true) && (this != null);
      @ ensures_free (age >= 0) && (this != null && this.age >= age);
      @ ensures_free (14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public Customer(/*@nullable@*/ java.lang.String name, int age) {
        super();

        this.name = name;
        this.age = age;
        ;
        ;
    }

    /*@ public normal_behavior
      @ requires name_nullness || ((true) && (name != null));
      @ requires age_interval || ((14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150));
      @ requires_free !name_nullness || ((true) && (name != null));
      @ requires_free !age_interval || ((14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150));
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures \result.name == name && \result.age == age;
      @ ensures_free name.packed == \typeof(name);
      @ ensures_free (true) && (\result != null);
      @ ensures_free (age >= 0) && (\result != null && \result.age >= age);
      @ ensures_free (age >= 0) && (\result != null && \result.age >= age);
      @ ensures_free (14 >= 0 && 14 <= 150) && (age >= 14 && age <= 150);
      @ assignable \nothing;
      @ assignable \nothing;
      @*/
    public static /*@nullable@*/ case_study.Customer __INIT_trampoline(/*@nullable@*/ java.lang.String name, int age, boolean name_nullness, boolean age_interval) {
        return new case_study.Customer(name, age);
    }

}
