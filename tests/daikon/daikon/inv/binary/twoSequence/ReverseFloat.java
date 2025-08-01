// ***** This file is automatically generated from Reverse.java.jpp

package daikon.inv.binary.twoSequence;

import daikon.*;
import daikon.inv.*;
import java.util.logging.Logger;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.plumelib.util.Intern;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents two sequences of double where one is in the reverse order of the other. Prints as
 * {@code x[] is the reverse of y[]}.
 */
public class ReverseFloat extends TwoSequenceFloat {
  static final long serialVersionUID = 20030822L;

  public static final Logger debug =
    Logger.getLogger("daikon.inv.binary.twoSequence.ReverseFloat");

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff Reverse invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  protected ReverseFloat(PptSlice ppt) {
    super(ppt);
  }

  protected @Prototype ReverseFloat() {
    super();
  }

  private static @Prototype ReverseFloat proto = new @Prototype ReverseFloat();

  /** Returns the prototype invariant for ReverseFloat. */
  public static @Prototype ReverseFloat get_proto() {
    return proto;
  }

  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  /** Reverse only makes sense on ordered arrays. */
  @Override
  public boolean instantiate_ok(VarInfo[] vis) {

    if (!valid_types(vis)) {
      return false;
    }

    // Check to see that both arrays are ordered
    if (!vis[0].aux.hasOrder() || !vis[1].aux.hasOrder()) {
      return false;
    }

    return true;
  }

  @Override
  public ReverseFloat instantiate_dyn(@Prototype ReverseFloat this, PptSlice slice) {
    return new ReverseFloat(slice);
  }

  @Override
  protected Invariant resurrect_done_swapped() {
    // "reverse of" is symmetric
    return this;
  }

  @Override
  public String repr(@GuardSatisfied ReverseFloat this) {
    return "ReverseFloat" + varNames() + ": falsified=" + falsified;
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied ReverseFloat this, OutputFormat format) {
    if (format.isJavaFamily()) {
      return format_java_family(format);
    }

    if (format == OutputFormat.DAIKON) {
      return format_daikon();
    }
    if (format == OutputFormat.CSHARPCONTRACT) {
      return format_csharp();
    }
    if (format == OutputFormat.SIMPLIFY) {
      return format_simplify();
    }

    return format_unimplemented(format);
  }

  public String format_daikon(@GuardSatisfied ReverseFloat this) {
    return var1().name() + " is the reverse of " + var2().name();
  }

  public String format_java_family(@GuardSatisfied ReverseFloat this, OutputFormat format) {
          return "daikon.Quant.isReverse(" + var1().name_using(format)
            + ", " + var2().name_using(format) + ")";
  }

  public String format_csharp(@GuardSatisfied ReverseFloat this) {
    String[] split1 = var1().csharp_array_split();
    String[] split2 = var2().csharp_array_split();
    return "Contract.ForAll(0, " + split1[0] + ".Count(), i => " + split1[0] + "[i]"  + split1[1] + ".Equals(" + split2[0] + "[" +split1[0] + ".Count()-1-i]" + split2[1] +"))";
  }

  public String format_simplify(@GuardSatisfied ReverseFloat this) {
    if (Invariant.dkconfig_simplify_define_predicates) {
      return format_simplify_defined();
    } else {
      return format_simplify_explicit();
    }
  }

  private String format_simplify_defined(@GuardSatisfied ReverseFloat this) {
    VarInfo onevar = var1();
    VarInfo othervar = var2();
    String[] one_name = onevar.simplifyNameAndBounds();
    String[] other_name = othervar.simplifyNameAndBounds();

    if (one_name == null || other_name == null) {
      return "format_simplify() can't handle one of these sequences: " + format();
    }

    return "(|is-reverse-of| "
      + one_name[0] + " " + one_name[1] + " " + one_name[2] + " "
      + other_name[0] + " " + other_name[1] + " " + other_name[2] + ")";
  }

  private String format_simplify_explicit(@GuardSatisfied ReverseFloat this) {
    VarInfo onevar = var1();
    VarInfo othervar = var2();
    String[] one_name = onevar.simplifyNameAndBounds();
    String[] other_name = othervar.simplifyNameAndBounds();

    if (one_name == null || other_name == null) {
      return "format_simplify() can't handle one of these sequences: " + format();
    }

    String index = VarInfo.get_simplify_free_index(onevar, othervar);

    // (FORALL (a i j b ip jp)
    //  (IFF (|is-reverse-of| a i j b ip jp)
    //   (AND (EQ (- j i) (- jp ip))
    //        (<= 0 i)
    //        (< j (arrayLength a))
    //        (<= 0 ip)
    //        (< jp (arrayLength b))
    //     (FORALL (x)
    //        (IMPLIES
    //            (AND (<= 0 x) (< x (- j i)))
    //            (EQ (select (select elems a) (+ i x))
    //                (select (select elems b) (- jp x))))))))

    return "(AND (EQ (- " + one_name[2] + " " + one_name[1] + ") (- "
      + other_name[2] + " " + other_name[1] + ")) (<= 0 " + one_name[1]
      + ") (< " + one_name[2] + " (arrayLength " + one_name[0]
      + ")) (<= 0 " + other_name[1] + ") (< " + other_name[2]
      + " (arrayLength " + other_name[0] + ")) (FORALL (" + index
      + ") (IMPLIES (AND (<= 0 " + index + ") (< " + index + " (- "
      + one_name[2] + " " + one_name[1] + "))) (EQ (select (select elems "
      + one_name[0] + ") (+ " + one_name[1] + " " + index
      + ")) (select (select elems " + other_name[0] + ") (- " + other_name[2]
      + " " + index + "))))))";
  }

  @Override
  public InvariantStatus check_modified(double @Interned [] a1, double @Interned [] a2, int count) {
    if (a1.length != a2.length) {
      return InvariantStatus.FALSIFIED;
    }
    int len = a1.length;
    for (int i = 0, j = len - 1; i < len; i++, j--) {
      if (!Global.fuzzy.eq(a1[i], a2[j])) {
        return InvariantStatus.FALSIFIED;
      }
    }
    return InvariantStatus.NO_CHANGE;
  }

  @Override
  public InvariantStatus add_modified(double @Interned [] a1, double @Interned [] a2, int count) {
    return check_modified(a1, a2, count);
  }

  @Override
  protected double computeConfidence() {
    return Invariant.CONFIDENCE_JUSTIFIED;
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant other) {
    assert other instanceof ReverseFloat;
    return true;
  }
}
