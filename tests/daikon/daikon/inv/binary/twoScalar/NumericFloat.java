// ***** This file is automatically generated from Numeric.java.jpp

package daikon.inv.binary.twoScalar;

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
public abstract class NumericFloat extends TwoFloat {

  static final long serialVersionUID = 20060609L;

  protected NumericFloat(PptSlice ppt, boolean swap) {
    super(ppt);
    this.swap = swap;
  }

  protected NumericFloat(boolean swap) {
    super();
    this.swap = swap;
  }

  @Override
  public boolean instantiate_ok(VarInfo[] vis) {

    ProglangType type1 = vis[0].file_rep_type;
    ProglangType type2 = vis[1].file_rep_type;
    if (!type1.isFloat() || !type2.isFloat()) {
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
  public String repr(@GuardSatisfied NumericFloat this) {
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
  public String format_using(@GuardSatisfied NumericFloat this, OutputFormat format) {

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
  public InvariantStatus check_modified(double x, double y, int count) {

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
    if (!v1.isDerived() || !(v1.derived instanceof SequenceFloatSubscript)) {
      return null;
    }
    if (!v2.isDerived() || !(v2.derived instanceof SequenceFloatSubscript)) {
      return null;
    }

    @NonNull SequenceFloatSubscript der1 = (SequenceFloatSubscript) v1.derived;
    @NonNull SequenceFloatSubscript der2 = (SequenceFloatSubscript) v2.derived;

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
    Invariant subinv = find(FloatEqual.class, der1.sclvar(), der2.sclvar());
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
  public abstract String get_format_str(@GuardSatisfied NumericFloat this, OutputFormat format);

  /** Returns true if x and y don't invalidate the invariant. */
  public abstract boolean eq_check(double x, double y);

  /**
   * Returns an array of arrays of antecedents. If all of the antecedents in any array are true,
   * then the invariant is obvious.
   */
  public InvDef[][] obvious_checks(VarInfo[] vis) {
    return new InvDef[][] {};
  }

  public static List<@Prototype Invariant> get_proto_all() {

    List<@Prototype Invariant> result = new ArrayList<>();

      result.add(Divides.get_proto(false));
      result.add(Divides.get_proto(true));
      result.add(Square.get_proto(false));
      result.add(Square.get_proto(true));

      result.add(ZeroTrack.get_proto(false));
      result.add(ZeroTrack.get_proto(true));

    // System.out.printf("%s get proto: %s%n", NumericFloat.class, result);
    return result;
  }

  // suppressor definitions, used by many of the classes below
  protected static NISuppressor

      var1_eq_0       = new NISuppressor(0, RangeFloat.EqualZero.class),
      var2_eq_0       = new NISuppressor(1, RangeFloat.EqualZero.class),
      var1_ge_0       = new NISuppressor(0, RangeFloat.GreaterEqualZero.class),
      var2_ge_0       = new NISuppressor(1, RangeFloat.GreaterEqualZero.class),
      var1_eq_1       = new NISuppressor(0, RangeFloat.EqualOne.class),
      var2_eq_1       = new NISuppressor(1, RangeFloat.EqualOne.class),
      var1_eq_minus_1 = new NISuppressor(0, RangeFloat.EqualMinusOne.class),
      var2_eq_minus_1 = new NISuppressor(1, RangeFloat.EqualMinusOne.class),
      var1_ne_0       = new NISuppressor(0, NonZeroFloat.class),
      var2_ne_0       = new NISuppressor(1, NonZeroFloat.class),
      var1_le_var2    = new NISuppressor(0, 1, FloatLessEqual.class),

    var1_eq_var2    = new NISuppressor(0, 1, FloatEqual.class),
    var2_eq_var1    = new NISuppressor(0, 1, FloatEqual.class);

  //
  // Int and Float Numeric Invariants
  //

  /**
   * Represents the divides without remainder invariant between two double scalars.
   * Prints as {@code x % y == 0}.
   */
  public static class Divides extends NumericFloat {
    // We are Serializable, so we specify a version to allow changes to
    // method signatures without breaking serialization.  If you add or
    // remove fields, you should change this number to the current date.
    static final long serialVersionUID = 20040113L;

    protected Divides(PptSlice ppt, boolean swap) {
      super(ppt, swap);
    }

    protected Divides(boolean swap) {
      super(swap);
    }

    private static @Prototype Divides proto = new @Prototype Divides(false);
    private static @Prototype Divides proto_swap = new @Prototype Divides(true);

    /** Returns the prototype invariant. */
    public static @Prototype NumericFloat get_proto(boolean swap) {
      if (swap) {
        return proto_swap;
      } else {
        return proto;
      }
    }

    // Variables starting with dkconfig_ should only be set via the
    // daikon.config.Configuration interface.
    /** Boolean. True iff divides invariants should be considered. */
    public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

    @Override
    public boolean enabled() {
      return dkconfig_enabled;
    }

    @Override
    protected Divides instantiate_dyn(@Prototype Divides this, PptSlice slice) {
      return new Divides(slice, swap);
    }

    @Override
    public String get_format_str(@GuardSatisfied Divides this, OutputFormat format) {
      if (format == OutputFormat.SIMPLIFY) {
        return "(EQ 0 (MOD %var1% %var2%))";
      } else if (format.isJavaFamily()) {
        return "daikon.Quant.fuzzy.eq(%var1% % %var2%, 0)";
      } else {
        return "%var1% % %var2% == 0";
      }
    }

    @Override
    public boolean eq_check(double x, double y) {
      return Global.fuzzy.eq(0, (x % y));
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
    private static NISuppressee suppressee = new NISuppressee(Divides.class, false);

    private static NISuppressionSet suppressions =
      new NISuppressionSet(
          new NISuppression[] {

            // These suppressions are only valid on scalars because the length
            // of var1 and var2 must also be the same and there is no suppressor
            // for that.

            // var2 == 1 ==> var1 % var2 == 0
            new NISuppression(var2_eq_1, suppressee),

            // var2 == -1 ==> var1 % var2 == 0
            new NISuppression(var2_eq_minus_1, suppressee),

            // (var1 == 0) ^ (var2 != 0) ==> var1 % var2 == 0
            new NISuppression(var1_eq_0, var2_ne_0, suppressee),

            // (var1 == var2) ^ (var2 != 0) ==> var1 % var2 == 0
            new NISuppression(var1_eq_var2, var2_ne_0, suppressee),

            // (var2 == var1) ^ (var1 != 0) ==> var2 % var1 == 0
            new NISuppression(var2_eq_var1, var1_ne_0, suppressee),

          });
    private static NISuppressionSet suppressions_swap = suppressions.swap();

    /**
     * Returns non-null if this invariant is obvious from an existing, non-falsified linear binary
     * invariant in the same slice as this invariant. This invariant of the form "x % y == 0" is
     * falsified if a linear binary invariant is found of the form "a*y - 1*x + 0 == 0"
     *
     * @return non-null value iff this invariant is obvious from other invariants in the same slice
     */
    @Pure
    @Override
    public @Nullable DiscardInfo isObviousDynamically(VarInfo[] vis) {
      // First call super type's method, and if it returns non-null, then
      // this invariant is already known to be obvious, so just return
      // whatever reason the super type returned.
      DiscardInfo di = super.isObviousDynamically(vis);
      if (di != null) {
        return di;
      }

      VarInfo var1 = vis[0];
      VarInfo var2 = vis[1];

      // ensure that var1.varinfo_index <= var2.varinfo_index
      if (var1.varinfo_index > var2.varinfo_index) {
        var1 = vis[1];
        var2 = vis[0];
      }

      // Find slice corresponding to these two variables.
      // Ideally, this should always just be ppt if all
      // falsified invariants have been removed.
      PptSlice2 ppt2 = ppt.parent.findSlice(var1,var2);

      // If no slice is found , no invariants exist to make this one obvious.
      if (ppt2 == null) {
        return null;
      }

      // For each invariant, check to see if it's a linear binary
      // invariant of the form "a*y - 1*x + 0 == 0" and if so,
      // you know this invariant of the form "x % y == 0" is obvious.
      for(Invariant inv : ppt2.invs) {

        if (inv instanceof LinearBinaryFloat) {
          LinearBinaryFloat linv = (LinearBinaryFloat) inv;

          // General form for linear binary: a*x + b*y + c == 0,
          // but a and b can be switched with respect to vis, and either
          // one may be negative, so instead check:
          //  - c == 0
          //  - a*b < 0   (a and b have different signs)
          //  - |a| == 1 or |b| == 1, so one will divide the other
          //     While this means that both x % y == 0 and y % x == 0,
          //     only one of these invariants will still be true at this
          //     time, and only that one will be falsified by this test.
          if (!linv.is_false()
              && Global.fuzzy.eq(linv.core.c, 0)
              && linv.core.b * linv.core.a < 0
              && (Global.fuzzy.eq(linv.core.a * linv.core.a, 1)
                  || Global.fuzzy.eq(linv.core.b * linv.core.b, 1))) {
            return new DiscardInfo(this, DiscardCode.obvious,
                                   "Linear binary invariant implies divides");
          }
        }
      }

      return null;
    }

  }

  /**
   * Represents the square invariant between two double scalars.
   * Prints as {@code x = y**2}.
   */
  public static class Square extends NumericFloat {
    // We are Serializable, so we specify a version to allow changes to
    // method signatures without breaking serialization.  If you add or
    // remove fields, you should change this number to the current date.
    static final long serialVersionUID = 20040113L;

    protected Square(PptSlice ppt, boolean swap) {
      super(ppt, swap);
    }

    protected Square(boolean swap) {
      super(swap);
    }

    private static @Prototype Square proto = new @Prototype Square(false);
    private static @Prototype Square proto_swap = new @Prototype Square(true);

    /** Returns the prototype invariant. */
    public static @Prototype Square get_proto(boolean swap) {
      if (swap) {
        return proto_swap;
      } else {
        return proto;
      }
    }

    // Variables starting with dkconfig_ should only be set via the
    // daikon.config.Configuration interface.
    /** Boolean. True iff square invariants should be considered. */
    public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

    @Override
    public boolean enabled() {
      return dkconfig_enabled;
    }
    @Override
    protected Square instantiate_dyn(@Prototype Square this, PptSlice slice) {
      return new Square(slice, swap);
    }

    @Override
    public String get_format_str(@GuardSatisfied Square this, OutputFormat format) {
      if (format == OutputFormat.SIMPLIFY) {
        return "(EQ %var1% (* %var2% %var2))";
      } else if (format == OutputFormat.CSHARPCONTRACT) {
        return "%var1% == %var2%*%var2%";
      } else if (format.isJavaFamily()) {

        return "daikon.Quant.fuzzy.eq(%var1%, %var2%*%var2%)";
      } else {
        return "%var1% == %var2%**2";
      }
    }

    /** Check to see if x == y squared. */
    @Override
    public boolean eq_check(double x, double y) {
      return Global.fuzzy.eq(x, y*y);
    }

    // Note there are no NI Suppressions for Square.  Two obvious
    // suppressions are:
    //
    //      (var2 == 1) ^ (var1 == 1)  ==> var1 = var2*var2
    //      (var2 == 0) ^ (var1 == 0)  ==> var1 = var2*var2
    //
    // But all of the antecedents would be constants, so we would
    // never need to create this slice, so there is no reason to create
    // these.

  }

  /**
   * Represents the zero tracks invariant between
   * two double scalars; that is, when {@code x} is zero,
   * {@code y} is also zero.
   * Prints as {@code x = 0 => y = 0}.
   */
  public static class ZeroTrack extends NumericFloat {
    // We are Serializable, so we specify a version to allow changes to
    // method signatures without breaking serialization.  If you add or
    // remove fields, you should change this number to the current date.
    static final long serialVersionUID = 20040313L;

    protected ZeroTrack(PptSlice ppt, boolean swap) {
      super(ppt, swap);
    }

    protected @Prototype ZeroTrack(boolean swap) {
      super(swap);
    }

    private static @Prototype ZeroTrack proto = new @Prototype ZeroTrack(false);
    private static @Prototype ZeroTrack proto_swap = new @Prototype ZeroTrack(true);

    /** Returns the prototype invariant. */
    public static @Prototype ZeroTrack get_proto(boolean swap) {
      if (swap) {
        return proto_swap;
      } else {
        return proto;
      }
    }

    // Variables starting with dkconfig_ should only be set via the
    // daikon.config.Configuration interface.
    /** Boolean. True iff zero-track invariants should be considered. */
    public static boolean dkconfig_enabled = false;

    @Override
    public boolean enabled() {
      return dkconfig_enabled;
    }

    @Override
    protected ZeroTrack instantiate_dyn(@Prototype ZeroTrack this, PptSlice slice) {
      return new ZeroTrack(slice, swap);
    }

    @Override
    public String get_format_str(@GuardSatisfied ZeroTrack this, OutputFormat format) {
      if (format == OutputFormat.SIMPLIFY) {
        return "(IMPLIES (EQ %var1% 0) (EQ %var2% 0))";
      } else if (format.isJavaFamily() || format == OutputFormat.CSHARPCONTRACT) {
        return "(!(%var1% == 0)) || (%var2% == 0)";
      } else {
        return "(%var1% == 0) ==> (%var2% == 0)";
      }
    }

    @Override
    public boolean eq_check(double x, double y) {
      if (x == 0) {
        return y == 0;
      } else {
        return true;
      }
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
    private static NISuppressee suppressee = new NISuppressee(ZeroTrack.class, false);

    private static NISuppressionSet suppressions =
      new NISuppressionSet(
          new NISuppression[] {
            // (var1 == var2) ==> (var1=0 ==> var2=0)
            new NISuppression(var1_eq_var2, suppressee),
            // (var1 != 0)    ==> (var1=0 ==> var2=0)
            new NISuppression(var1_ne_0, suppressee),
            // (var2 == 0) ==> (var1=0 ==> var2=0)
            new NISuppression(var2_eq_0, suppressee),
          });
    private static NISuppressionSet suppressions_swap = suppressions.swap();

  }

//
// Standard String invariants
//

}
