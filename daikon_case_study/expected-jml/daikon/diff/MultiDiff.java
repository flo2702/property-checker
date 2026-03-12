package daikon.diff;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;

/**
 * <B>MultiDiff</B> is an executable application that performs the same functionality as Diff with a
 * few key change. First, it always outputs the histogram even when two files are called. Second, it
 * allows the option of creating *.spinfo based on the invariants found.
 */
public class MultiDiff  {


    
    /*@ private normal_behavior
      @ requires_free this.packed == daikon.diff.MultiDiff;
      @ ensures_free (true) && (this != null);
      @*/
    private /*@helper@*/ MultiDiff() {
        super();

        throw new Error("do not instantiate");
    }

    /*@ public normal_behavior
      @ ensures \result != null && \fresh(\result) && \invariant_free_for(\result) && \invariant_for(\result);
      @ ensures_free (true) && (\result != null);
      @*/
    public static /*@nullable@*/ daikon.diff.MultiDiff __INIT_trampoline() {
        return new daikon.diff.MultiDiff();
    }

    
    /*@ public normal_behavior
      @ requires (true) && (args != null);
      @ requires_free args.packed == \typeof(args);
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void main(/*@nullable@*/ java.lang.String[] args) throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException, NoSuchMethodException, InvocationTargetException {
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
    public static /*@helper@*/ void mainHelper(/*@nullable@*/ java.lang.String[] args) throws IOException, ClassNotFoundException, InstantiationException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        java.io.FileOutputStream fos;
        java.io.FileOutputStream temp1 = new FileOutputStream("rand_sel.spinfo");
        fos = temp1;
        try {
            java.io.PrintStream out;
            java.io.PrintStream temp2 = new PrintStream(fos);
            out = temp2;
            MultiDiffVisitor.__setForSpinfoOut_trampoline(out, true);
            Diff.__main_trampoline(args, true);
        } finally {
            fos.close();
        }
    }

    /*@ public normal_behavior
      @ requires args_nullness || ((true) && (args != null));
      @ requires_free !args_nullness || ((true) && (args != null));
      @ ensures_free args.packed == \typeof(args);
      @*/
    public static /*@helper@*/ void __mainHelper_trampoline(/*@nullable@*/ java.lang.String[] args, boolean args_nullness) {
        mainHelper(args);
    }

}
