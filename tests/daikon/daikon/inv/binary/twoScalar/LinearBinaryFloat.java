// ***** This file is automatically generated from LinearBinary.java.jpp

package daikon.inv.binary.twoScalar;

import daikon.*;
import daikon.derive.unary.SequenceLength;
import daikon.inv.*;
import java.util.*;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents a Linear invariant between two double scalars {@code x} and {@code y}, of
 * the form {@code ax + by + c = 0}. The constants {@code a}, {@code b} and
 * {@code c} are mutually relatively prime, and the constant {@code a} is always positive.
 */
public class LinearBinaryFloat extends TwoFloat {
  static final long serialVersionUID = 20030822L;

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff LinearBinary invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  public LinearBinaryCoreFloat core;

  @SuppressWarnings("nullness") // circular initialization
  protected LinearBinaryFloat(PptSlice ppt) {
    super(ppt);
    core = new LinearBinaryCoreFloat(this);
  }

  @SuppressWarnings("nullness") // circular initialization
  protected @Prototype LinearBinaryFloat() {
    super();
    // Do we need core to be set for a prototype invariant?
    core = new LinearBinaryCoreFloat(this);
  }

  private static @Prototype LinearBinaryFloat proto = new @Prototype LinearBinaryFloat();

  /** Returns a prototype LinearBinaryFloat invariant. */
  public static @Prototype LinearBinaryFloat get_proto() {
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

    return true;
  }

  @Override
  protected LinearBinaryFloat instantiate_dyn(@Prototype LinearBinaryFloat this, PptSlice slice) {
    return new LinearBinaryFloat(slice);
  }

  @SideEffectFree
  @Override
  public LinearBinaryFloat clone(@GuardSatisfied LinearBinaryFloat this) {
    LinearBinaryFloat result = (LinearBinaryFloat) super.clone();
    result.core = core.clone();
    result.core.wrapper = result;
    return result;
  }

  @Override
  protected Invariant resurrect_done_swapped() {
    core.swap();
    return this;
  }

  @Override
  public String repr(@GuardSatisfied LinearBinaryFloat this) {
    return "LinearBinaryFloat" + varNames() + ": falsified=" + falsified
      + "; " + core.repr();
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied LinearBinaryFloat this, OutputFormat format) {
    return core.format_using(format, var1().name_using(format),
                             var2().name_using(format));
  }

  @Pure
  @Override
  public boolean isActive() {
    return core.isActive();
  }

  @Override
  public boolean mergeFormulasOk() {
    return core.mergeFormulasOk();
  }

  /**
   * Merge the invariants in invs to form a new invariant. Each must be a LinearBinaryFloat invariant. The
   * work is done by the LinearBinary core
   *
   * @param invs list of invariants to merge. They should all be permuted to match the variable
   *     order in parent_ppt.
   * @param parent_ppt slice that will contain the new invariant
   */
  @Override
  public @Nullable LinearBinaryFloat merge(List<Invariant> invs, PptSlice parent_ppt) {

    // Create a matching list of cores
    List<LinearBinaryCoreFloat> cores = new ArrayList<>();
    for (Invariant inv : invs) {
      cores.add(((LinearBinaryFloat) inv).core);
    }

    // Merge the cores and build a new invariant containing the merged core
    LinearBinaryFloat result = new LinearBinaryFloat(parent_ppt);
    LinearBinaryCoreFloat newcore = core.merge(cores, result);
    if (newcore == null) {
      return null;
    }
    result.core = newcore;
    return result;
  }

  @Override
  public InvariantStatus check_modified(double x, double y, int count) {
    return clone().add_modified(x, y, count);
  }

  @Override
  public InvariantStatus add_modified(double x, double y, int count) {
    return core.add_modified(x, y, count);
  }

  @Override
  public boolean enoughSamples(@GuardSatisfied LinearBinaryFloat this) {
    return core.enoughSamples();
  }

  @Override
  protected double computeConfidence() {
    return core.computeConfidence();
  }

  @Pure
  @Override
  public boolean isExact() {
    return true;
  }

  @Pure
  @Override
  public @Nullable DiscardInfo isObviousStatically(VarInfo[] vis) {
    // Obvious derived
    VarInfo var1 = vis[0];
    VarInfo var2 = vis[1];
    // avoid comparing "size(a)" to "size(a)-1"; yields "size(a)-1 = size(a) - 1"
    if (var1.isDerived()
        && (var1.derived instanceof SequenceLength)
        && var2.isDerived()
        && (var2.derived instanceof SequenceLength)) {
      @NonNull SequenceLength sl1 = (SequenceLength) var1.derived;
      @NonNull SequenceLength sl2 = (SequenceLength) var2.derived;
      if (sl1.base == sl2.base) {
        String discardString = var1.name()+" and "+var2.name()+" derived from "+
          "same sequence: "+sl1.base.name();
        return new DiscardInfo(this, DiscardCode.obvious, discardString);
      }
    }
    // avoid comparing "size(a)-1" to anything; should compare "size(a)" instead
    if (var1.isDerived()
        && (var1.derived instanceof SequenceLength)
        && ((SequenceLength) var1.derived).shift != 0) {
      String discardString = "Variables of the form 'size(a)-1' are not compared since 'size(a)' "+
        "will be compared";
      return new DiscardInfo(this, DiscardCode.obvious, discardString);
    }
    if (var2.isDerived()
        && (var2.derived instanceof SequenceLength)
        && ((SequenceLength) var2.derived).shift != 0) {
      String discardString = "Variables of the form 'size(a)-1' are not compared since 'size(a)' "+
        "will be compared";
      return new DiscardInfo(this, DiscardCode.obvious, discardString);
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

    if (core.a == 0) {
      return new DiscardInfo(this, DiscardCode.obvious, var2().name() + " is constant");
    }
    if (core.b == 0) {
      return new DiscardInfo(this, DiscardCode.obvious, var1().name() + " is constant");
    }
//    if (core.a == 1 && core.b == 0) {
//      return new DiscardInfo(this, DiscardCode.obvious, "Variables are equal");
//    }
    if (core.a == -core.b && core.c == 0) {
     return new DiscardInfo(this, DiscardCode.obvious, "Variables are equal");
    }
    return null;
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant other) {
    return core.isSameFormula(((LinearBinaryFloat) other).core);
  }

  @Pure
  @Override
  public boolean isExclusiveFormula(Invariant other) {
    if (other instanceof LinearBinaryFloat) {
      return core.isExclusiveFormula(((LinearBinaryFloat) other).core);
    }
    return false;
  }

  // Look up a previously instantiated invariant.
  public static @Nullable LinearBinaryFloat find(PptSlice ppt) {
    assert ppt.arity() == 2;
    for (Invariant inv : ppt.invs) {
      if (inv instanceof LinearBinaryFloat) {
        return (LinearBinaryFloat) inv;
      }
    }
    return null;
  }

  // Returns a vector of LinearBinary objects.
  // This ought to produce an iterator instead.
  public static List<LinearBinaryFloat> findAll(VarInfo vi) {
    List<LinearBinaryFloat> result = new ArrayList<>();
    for (PptSlice view : vi.ppt.views_iterable()) {
      if ((view.arity() == 2) && view.usesVar(vi)) {
        LinearBinaryFloat lb = LinearBinaryFloat.find(view);
        if (lb != null) {
          result.add(lb);
        }
      }
    }
    return result;
  }
}
