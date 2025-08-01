// ***** This file is automatically generated from Numeric.java.jpp

package daikon.inv.binary.twoString;

import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.checker.signature.qual.ClassGetName;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import static daikon.inv.Invariant.asInvClass;

import daikon.*;
import daikon.Quantify.QuantFlags;
import daikon.derive.binary.*;
import daikon.inv.*;
import daikon.inv.binary.twoScalar.*;
import daikon.inv.binary.twoString.*;
import daikon.inv.unary.scalar.*;
import daikon.inv.unary.sequence.*;
import daikon.suppress.*;
import java.util.*;
import org.plumelib.util.UtilPlume;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Baseclass for binary numeric invariants.
 *
 * Each specific invariant is implemented in a subclass (typically, in this file). The subclass must
 * provide the methods instantiate(), check(), and format(). Symmetric functions should define
 * is_symmetric() to return true.
 */
public abstract class StdString extends TwoString {

  static final long serialVersionUID = 20060609L;

  protected StdString(PptSlice ppt, boolean swap) {
    super(ppt);
    this.swap = swap;
  }

  protected StdString(boolean swap) {
    super();
    this.swap = swap;
  }

  @Override
  public boolean instantiate_ok(VarInfo[] vis) {

    ProglangType type1 = vis[0].file_rep_type;
    ProglangType type2 = vis[1].file_rep_type;
    if (!type1.isString() || !type2.isString()) {
      return false;
    }

    return true;
  }

  @Pure
  @Override
  public boolean isExact() {
    return true;
  }

  @Override
  public String repr(@GuardSatisfied StdString this) {
    return getClass().getSimpleName() + ": " + format()
      + (swap ? " [swapped]" : " [unswapped]");
  }

  /**
   * Returns a string in the specified format that describes the invariant.
   *
   * The generic format string is obtained from the subclass specific get_format_str(). Instances of
   * %varN% are replaced by the variable name in the specified format.
   */
  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied StdString this, OutputFormat format) {

    if (ppt == null) {
      return String.format("proto ppt [class %s] format %s", getClass(),
                           get_format_str(format));
    }
    String fmt_str = get_format_str(format);

    String v1 = var1().name_using(format);
    String v2 = var2().name_using(format);

    // Note that we do not use String.replaceAll here, because that's
    // inseparable from the regex library, and we don't want to have to
    // escape v1 with something like
    // v1.replaceAll("([\\$\\\\])", "\\\\$1")
    fmt_str = fmt_str.replace("%var1%", v1);
    fmt_str = fmt_str.replace("%var2%", v2);

    // if (false && (format == OutputFormat.DAIKON)) {
    //   fmt_str = "[" + getClass() + "]" + fmt_str + " ("
    //          + var1().get_value_info() + ", " + var2().get_value_info() +  ")";
    // }
    return fmt_str;
  }

  /** Calls the function specific equal check and returns the correct status. */

  @Override
  public InvariantStatus check_modified(String x, String y, int count) {

    try {
      if (eq_check(x, y)) {
        return InvariantStatus.NO_CHANGE;
      } else {
        return InvariantStatus.FALSIFIED;
      }
    } catch (Exception e) {
      return InvariantStatus.FALSIFIED;
    }
  }

  /**
   * Checks to see if 'x[a] op y[b]' where 'x[] op y[]' and 'a == b'. Doesn't catch the case where
   * a = b+1.
   */
  public @Nullable DiscardInfo is_subscript(VarInfo[] vis) {

    VarInfo v1 = var1(vis);
    VarInfo v2 = var2(vis);

    // Make sure each var is a sequence subscript
    if (!v1.isDerived() || !(v1.derived instanceof SequenceStringSubscript)) {
      return null;
    }
    if (!v2.isDerived() || !(v2.derived instanceof SequenceStringSubscript)) {
      return null;
    }

    @NonNull SequenceStringSubscript der1 = (SequenceStringSubscript) v1.derived;
    @NonNull SequenceStringSubscript der2 = (SequenceStringSubscript) v2.derived;

    // Make sure the shifts match
    if (der1.index_shift != der2.index_shift) {
      return null;
    }

    // Look for this invariant over a sequence
    String cstr = getClass().getName();
    cstr = cstr.replaceFirst("Numeric", "PairwiseNumeric");
    cstr = cstr.replaceFirst("twoScalar", "twoSequence");
    cstr = cstr.replaceFirst("twoFloat", "twoSequence");
    Class<? extends Invariant> pairwise_class;
    try {
      @SuppressWarnings("signature") // string manipulation; application invariants
      @ClassGetName String cstr_cgn = cstr;
      pairwise_class = asInvClass(Class.forName(cstr_cgn));
    } catch (Exception e) {
      throw new Error("can't create class for " + cstr, e);
    }
    Invariant inv = find(pairwise_class, der1.seqvar(), der2.seqvar());
    if (inv == null) {
      return null;
    }

    // Look to see if the subscripts are equal
    Invariant subinv = find(StringEqual.class, der1.sclvar(), der2.sclvar());
    if (subinv == null) {
      return null;
    }

    return new DiscardInfo(this, DiscardCode.obvious, "Implied by "
                           + inv.format() + " and " + subinv.format());
  }

  @Pure
  @Override
  public @Nullable DiscardInfo isObviousDynamically(VarInfo[] vis) {

    DiscardInfo super_result = super.isObviousDynamically(vis);
    if (super_result != null) {
      return super_result;
    }

      // any relation across subscripts is made obvious by the same
      // relation across the original sequence if the subscripts are equal
      DiscardInfo result = is_subscript(vis);
      if (result != null) {
        return result;
      }

    // Check for invariant specific obvious checks.  The obvious_checks
    // method returns an array of arrays of antecedents.  If all of the
    // antecedents in an array are true, then the invariant is obvoius.
    InvDef[][] obvious_arr = obvious_checks(vis);
    obvious_loop:
    for (int i = 0; i < obvious_arr.length; i++) {
      InvDef[] antecedents = obvious_arr[i];
      StringBuilder why = null;
      for (int j = 0; j < antecedents.length; j++) {
        Invariant inv = antecedents[j].find();
        if (inv == null) {
          continue obvious_loop;
        }
        if (why == null) {
          why = new StringBuilder(inv.format());
        } else {
          why.append(" and ");
          why.append(inv.format());
        }
      }
      return new DiscardInfo(this, DiscardCode.obvious, "Implied by " + why);
    }

    return null;
  }

  /**
   * Return a format string for the specified output format. Each instance of %varN% will be
   * replaced by the correct name for varN.
   */
  public abstract String get_format_str(@GuardSatisfied StdString this, OutputFormat format);

  /** Returns true if x and y don't invalidate the invariant. */
  public abstract boolean eq_check(String x, String y);

  /**
   * Returns an array of arrays of antecedents. If all of the antecedents in any array are true,
   * then the invariant is obvious.
   */
  public InvDef[][] obvious_checks(VarInfo[] vis) {
    return new InvDef[][] {};
  }

  public static List<@Prototype Invariant> get_proto_all() {

    List<@Prototype Invariant> result = new ArrayList<>();

        result.add(SubString.get_proto(false));
        result.add(SubString.get_proto(true));

    // System.out.printf("%s get proto: %s%n", StdString.class, result);
    return result;
  }

  // suppressor definitions, used by many of the classes below
  protected static NISuppressor

    var1_eq_var2    = new NISuppressor(0, 1, StringEqual.class),
    var2_eq_var1    = new NISuppressor(0, 1, StringEqual.class);

  //
  // Int and Float Numeric Invariants
  //

//
// Standard String invariants
//

  /**
   * Represents the substring invariant between two String scalars.
   * Prints as {@code x is a substring of y}.
   */
  public static class SubString extends StdString {
    // We are Serializable, so we specify a version to allow changes to
    // method signatures without breaking serialization.  If you add or
    // remove fields, you should change this number to the current date.
    static final long serialVersionUID = 20081113L;

    protected SubString(PptSlice ppt, boolean swap) {
      super(ppt, swap);
    }

    protected SubString(boolean swap) {
      super(swap);
    }

    private static @Prototype SubString proto = new @Prototype SubString(false);
    private static @Prototype SubString proto_swap = new @Prototype SubString(true);

    /** Returns the prototype invariant. */
    public static @Prototype SubString get_proto(boolean swap) {
      if (swap) {
        return proto_swap;
      } else {
        return proto;
      }
    }

    // Variables starting with dkconfig_ should only be set via the
    // daikon.config.Configuration interface.
    /** Boolean. True iff SubString invariants should be considered. */
    public static boolean dkconfig_enabled = false;

    @Override
    public boolean enabled() {
      return dkconfig_enabled;
    }

    @Override
    protected SubString instantiate_dyn(@Prototype SubString this, PptSlice slice) {
      return new SubString(slice, swap);
    }

    @Override
    public String get_format_str(@GuardSatisfied SubString this, OutputFormat format) {
      if (format == OutputFormat.DAIKON) {
        return "%var1% is a substring of %var2%";
      } else if (format.isJavaFamily()) {
        return "%var2%.contains(%var1%)";
      } else if (format == OutputFormat.CSHARPCONTRACT) {

          return "%var2%.Contains(%var1%)";
      } else {
        return format_unimplemented(format);
      }
    }

    @Override
    public boolean eq_check(String x, String y) {
      return y.contains(x);
    }

    /** Justified as long as there are samples. */
    @Override
    protected double computeConfidence() {
      if (ppt.num_samples() == 0) {
        return Invariant.CONFIDENCE_UNJUSTIFIED;
      }

      return Invariant.CONFIDENCE_JUSTIFIED;
    }

    /** Returns a list of non-instantiating suppressions for this invariant. */
    @Pure
    @Override
    public NISuppressionSet get_ni_suppressions() {
      if (swap) {
        return suppressions_swap;
      } else {
        return suppressions;
      }
    }

    /** definition of this invariant (the suppressee) (unswapped) */
    private static NISuppressee suppressee = new NISuppressee(SubString.class, false);

    private static NISuppressionSet suppressions =
      new NISuppressionSet(
          new NISuppression[] {
              // v1 == v2 ==> v1 subsequence v2
              new NISuppression(var1_eq_var2, suppressee),
          });
    private static NISuppressionSet suppressions_swap = suppressions.swap();
  }

}
