// ***** This file is automatically generated from NonZero.java.jpp

package daikon.inv.unary.scalar;

import daikon.*;
import daikon.derive.unary.*;
import daikon.inv.*;
import daikon.inv.binary.sequenceScalar.*;
import daikon.inv.unary.sequence.*;
import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.plumelib.util.Intern;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/** Represents double scalars that are non-zero. Prints as {@code x != 0}. */

public class NonZeroFloat extends SingleFloat {
  static final long serialVersionUID = 20030822L;

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff NonZeroFloat invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  /** Debug tracer. */
  public static final Logger debug = Logger.getLogger("daikon.inv.unary.scalar.NonZeroFloat");

  /** Maximum value ever used for max-min in confidence calculation. */
  private static final long range_max = 50;

  private NonZeroFloat(PptSlice ppt) {
    super(ppt);
  }

  private @Prototype NonZeroFloat() {
    super();
  }

  private static @Prototype NonZeroFloat proto = new @Prototype NonZeroFloat();

  /** Returns the prototype invariant for NonZeroFloat */
  public static @Prototype NonZeroFloat get_proto() {
    return proto;
  }

  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  @Override
  public boolean instantiate_ok(VarInfo[] vis) {

    if (!valid_types(vis)) {
      return false;
    }

    if (vis[0].aux.isStruct()
        || vis[0].aux.isNonNull()
        || !vis[0].aux.hasNull())
      return false;

    return true;
  }

  @Override
  public NonZeroFloat instantiate_dyn(@Prototype NonZeroFloat this, PptSlice slice) {
    return new NonZeroFloat(slice);
  }

  private String zero(@GuardSatisfied @Prototype NonZeroFloat this, @SuppressWarnings("UnusedVariable") OutputFormat format) {

    return "0";
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied @Prototype NonZeroFloat this, OutputFormat format) {
    // // var() fails for prototype invariants
    // if (ppt == null) {
    //   return "Prototype NonZeroFloat invariant (ppt == null)";
    // }

    String name = var().name_using(format);

    if (format.isJavaFamily()) {

        return "daikon.Quant.fuzzy.ne(" + name + ", " + zero(format) + ")";
    }

    if ((format == OutputFormat.DAIKON)
        || (format == OutputFormat.ESCJAVA)
        || (format == OutputFormat.CSHARPCONTRACT)) {
      return name + " != " + zero(format);
    }

    if (format == OutputFormat.SIMPLIFY) {
      return "(NEQ " + var().simplifyFixup(name) + " " + zero(format) + ")";
    }

    return format_unimplemented(format);
  }

  @Override
  public InvariantStatus check_modified(double v, int count) {
    if (v == 0) {
      return InvariantStatus.FALSIFIED;
    } else {
      return InvariantStatus.NO_CHANGE;
    }
  }

  @Override
  public InvariantStatus add_modified(double v, int count) {
    InvariantStatus status = check_modified(v, count);
    if (status == InvariantStatus.FALSIFIED) {
      if (logOn()) {
        log(debug, "falsified (value = " + v + ")");
      }
    } // else if (logDetail())
      // log ("add_modified (" + v + ")");
    return status;
  }

  /** Returns whether or not the variable is a pointer. */
  @Pure
  private boolean is_pointer(@GuardSatisfied NonZeroFloat this) {
    return ppt.var_infos[0].file_rep_type == ProglangType.HASHCODE;
  }

  @Override
  protected double computeConfidence() {
    return 1 - computeProbability();
  }

  // used by computeConfidence
  protected double computeProbability() {
    assert ! falsified;
    // This method works by looking at all sample values and
    // calculating the probability that they were all non-zero by
    // chance (assuming a uniform distribution).  If the variable is
    // not a pointer, the range used is the observed range from sample
    // data.  Further observed constraints are used to change the
    // returned probability, such as all samples being congruent some
    // modulus.

    ValueSet.ValueSetFloat vs = (ValueSet.ValueSetFloat) ppt.var_infos[0].get_value_set();

    // If greater than or less than 0, the bounds invariant will be more
    // interesting
    if (!is_pointer() && ((vs.min() > 0) || (vs.max() < 0))) {

      // Maybe just use 0 as the min or max instead, and see what happens:
      // see whether the "nonzero" invariant holds anyway.  (Perhaps only
      // makes sense to do if the {Lower,Upper}Bound invariant doesn't imply
      // the non-zeroness.)  In that case, do still check for no values yet
      // received.
      return Invariant.PROBABILITY_UNJUSTIFIED;
    } else {
      double range;
      if (is_pointer()) {
        range = 3;
      } else {
        long modulus = 1;
        {
          Modulus mi = Modulus.find(ppt);
          if (mi != null) {
            modulus = mi.modulus;
          }
        }
        // Perhaps I ought to check that it's possible (given the modulus
        // constraints) for the value to be zero; otherwise, the modulus
        // constraint implies non-zero.
        range = (vs.max() - vs.min() + 1) / modulus;
      }
      if ((range_max != 0) && (range > range_max)) {
        range = range_max;
      }

      double probability_one_elt_nonzero = 1 - 1.0/range;
      // This could underflow; so consider doing
      //   double log_probability = self.samples*math.log(probability);
      // then calling Math.exp (if the value is in the range that wouldn't
      // cause underflow).
      // return Math.pow(probability_one_elt_nonzero, ppt.num_mod_samples());
      return Math.pow(probability_one_elt_nonzero, ppt.num_samples());
    }
  }

  @Pure
  @Override
  public @Nullable DiscardInfo isObviousStatically(VarInfo[] vis) {
    VarInfo var = vis[0];

    if (var.aux.isStruct()) {
      return new DiscardInfo(this, DiscardCode.obvious,
                             var.name() + " is a struct");
    }

    if (var.aux.isNonNull()) {
      return new DiscardInfo(this, DiscardCode.obvious,
                             "aux information says " + var.name() + " is non-null");
    }

    if (!var.aux.hasNull()) {
      return new DiscardInfo(this, DiscardCode.obvious,
                     "'null' has no special meaning for " + var.name());
    }

    return super.isObviousStatically(vis);
  }

  @Pure
  @Override
  public @Nullable DiscardInfo isObviousDynamically(VarInfo[] vis) {
    DiscardInfo super_result = super.isObviousDynamically(vis);
    if (super_result != null) {
      return super_result;
    }

    VarInfo var = vis[0];

    Debug dlog = new Debug(getClass(), ppt, vis);

    if (logOn()) {
      dlog.log("Checking IsObviousDynamically");
    }

    // System.out.println("isObviousImplied: " + format());

    // For every EltNonZeroFloat at this program point, see if this variable is
    // an obvious member of that sequence.
    PptTopLevel parent = ppt.parent;
    for (Iterator<Invariant> itor = parent.invariants_iterator(); itor.hasNext(); ) {
      Invariant inv = itor.next();
      if ((inv instanceof EltNonZeroFloat) && inv.enoughSamples()) {
        VarInfo v2 = inv.ppt.var_infos[0];
        // System.out.println("NonZeroFloat.isObviousImplied: calling " + MemberFloat + ".isObviousMember(" + var.name + ", " + v2.name + ")");
        // Don't use isEqualToObviousMember:  that is too subtle
        // and eliminates desirable invariants such as "return != null".
        if (MemberFloat.isObviousMember(var, v2)) {
          // System.out.println("NonZeroFloat.isObviousImplied: " + MemberFloat + ".isObviousMember(" + var.name + ", " + v2.name + ") = true");
          if (logOn()) {
            dlog.log("isObvDyn- true, arg is member of nonzero sequence");
          }
          String discardString = var.name() + " is a member of the non-zero sequence " + v2.name();
          if (logOn()) {
            log("%s obviously implied from %s", format(), inv.format());
          }
          return new DiscardInfo(this, DiscardCode.obvious, discardString);
        }
      }
    }

    if ((var.derived != null)
        && (var.derived instanceof SequenceInitialFloat)) {
      SequenceInitialFloat si = (SequenceInitialFloat) var.derived;
      if (si.index == 0) {

        // For each sequence variable, if var is an obvious member, and
        // the sequence has the same invariant, then this one is obvious.
        PptTopLevel pptt = ppt.parent;
        for (int i = 0; i < pptt.var_infos.length; i++) {
          VarInfo vi = pptt.var_infos[i];
          if (MemberFloat.isObviousMember(var, vi)) {
            PptSlice1 other_slice = pptt.findSlice(vi);
            if (other_slice != null) {
              SeqIndexFloatNonEqual sine = SeqIndexFloatNonEqual.find(other_slice);
              if ((sine != null) && sine.enoughSamples()) {
                // System.out.println("NonZeroFloat.isObviousImplied true due to: " + sine.format());
                if (logOn()) {
                  dlog.log("isObvDyn- true due to " + sine.format());
                }
                String discardString = var.name() + " is a member of the non-zero sequence " + vi.name();
                return new DiscardInfo(this, DiscardCode.obvious, discardString);
              }
            }
          }
        }
      }
    }

    return null;
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant other) {
    assert other instanceof NonZeroFloat;
    return true;
  }

  @Pure
  @Override
  public boolean isExclusiveFormula(Invariant other) {
    if (other instanceof OneOfScalar) {
      OneOfScalar oos = (OneOfScalar) other;
      if ((oos.num_elts() == 1) && (((Long)oos.elt()).doubleValue() == 0)) {
        return true;
      }
    }
    return false;
  }
}
