// ***** This file is automatically generated from SequencesJoin.java.jpp

package daikon.derive.binary;

import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import daikon.*;
import daikon.derive.*;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.plumelib.util.Intern;

/**
 * Derived variable representing the "join" of two sequences. That is, if the two sequences came
 * from the same original data structure (like an array of multi-field objects) then we join the two
 * sequences and generate a hashcode of the join value. This allows us to detect uniqueness and
 * equality style invariants across the data structure rather than just one slice of it. Works for
 * number and string arrays.
 */
public final class SequencesJoin extends BinaryDerivation {
  static final long serialVersionUID = 20020122L;

  /** Debug tracer. */
  public static final Logger debug = Logger.getLogger("daikon.derive.binary.SequencesJoin");

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff SequencesJoin derived variables should be generated. */
  public static boolean dkconfig_enabled = false;

  @Override
  public VarInfo var1(@GuardSatisfied SequencesJoin this) {
    return base1;
  }

  @Override
  public VarInfo var2(@GuardSatisfied SequencesJoin this) {
    return base2;
  }

  /**
   * Create a new SequencesJoin derivation.
   *
   * @param vi1 the first of the two variables this is based on
   * @param vi2 the second of the two variables this is based on
   */
  SequencesJoin(VarInfo vi1, VarInfo vi2) {
    super(vi1, vi2);
  }

  /**
   * Returns a new sequence of hashcodes that is the join of the hashcodes of the component
   * sequences. This is modified whenever either component sequence is modified.
   *
   * @param full_vt the value tuple of a program point to compute the derived value from
   */
  @Override
  public ValueAndModified computeValueAndModifiedImpl(ValueTuple full_vt) {
    Object val1 = var1().getValue(full_vt);
    Object val2 = var2().getValue(full_vt);

    int length1 = -1;
    int length2 = -2; // They must equal in the end

    if (val1 == null) {
      length1 = 0;
    }

    if (val2 == null) {
      length2 = 0;
    }

    if (val1 instanceof long[]) {
      length1 = ((long[]) val1).length;
    }

    if (val2 instanceof long[]) {
      length2 = ((long[]) val2).length;
    }

    if (val1 instanceof long[]) {
      length1 = ((long[]) val1).length;
    }

    if (val2 instanceof long[]) {
      length2 = ((long[]) val2).length;
    }

    assert length1 == length2;

    long[] result = new long[length1];

    for (int i = 0; i < length1; i++) {
      Object e1 = null;
      Object e2 = null;
      if (val1 instanceof long[]) {
        e1 = Long.valueOf(((long[]) val1)[i]);
      }
      if (val2 instanceof long[]) {
        e2 = Long.valueOf(((long[]) val2)[i]);
      }
      if (val1 instanceof Object[]) {
        e1 = ((Object[]) val1)[i];
      }
      if (val2 instanceof Object[]) {
        e2 = ((Object[]) val2)[i];
      }
      if (e1 == null) {
        e1 = Long.valueOf(0);
      }
      if (e2 == null) {
        e2 = Long.valueOf(0);
      }
      // Loses top 8 bits, but we're just mixing two hashCodes.
      result[i] = ((long) e1.hashCode() << 8L) + e2.hashCode();
    }

    /*
       Use this if you don't see no duplicates where you should
    if (debug.isLoggable(Level.FINE)) {
      debug.fine(var1().name.toString() + " " + var2().name.toString());
      if (val1 instanceof long[]) {
        debug.fine(Arrays.toString((long[]) val1));
      } else {
        debug.fine(Arrays.toString((Object[]) val1));
      }
      if (val2 instanceof long[]) {
        debug.fine(Arrays.toString((long[]) val2));
      } else {
        debug.fine(Arrays.toString((Object[]) val2));
      }
      debug.fine(Arrays.toString(result));

      }
    */

    int mod = ValueTuple.UNMODIFIED;
    int mod1 = var1().getModified(full_vt);
    int mod2 = var2().getModified(full_vt);

    if (mod1 == ValueTuple.MODIFIED) {
      mod = ValueTuple.MODIFIED;
    }
    if (mod2 == ValueTuple.MODIFIED) {
      mod = ValueTuple.MODIFIED;
    }
    if (mod1 == ValueTuple.MISSING_NONSENSICAL) {
      mod = ValueTuple.MISSING_NONSENSICAL;
    }
    if (mod2 == ValueTuple.MISSING_NONSENSICAL) {
      mod = ValueTuple.MISSING_NONSENSICAL;
    }
    /*
     * v1\v2  Unm  Mod  Mis
     *
     * Unm    Unm  Mod  Mis
     * Mod    Mod  Mod  Mis
     * Mis    Mis  Mis  Mis
     */

    return new ValueAndModified(Intern.intern(result), mod);
  }

  @Override
  protected VarInfo makeVarInfo() {
    VarInfo var1 = var1();
    VarInfo var2 = var2();

    VarInfo vi = VarInfo.make_function("join", var1, var2);

    // Set the declared type and file rep types
    String newTypeName = "Join(" + var1.type.toString() + "," + var2.type.toString() + ")";
    vi.type = ProglangType.parse(newTypeName + "[]");
    if (debug.isLoggable(Level.FINE)) {
      debug.fine("New decl type is " + vi.type.toString());
    }
    vi.file_rep_type = ProglangType.HASHCODE_ARRAY;

    // Generate a new comparability based on base comparabilities' indices
    vi.comparability =
        VarComparability.makeComparabilitySameIndices(newTypeName, var1.comparability);

    return vi;
  }

  @SideEffectFree
  @Override
  public String toString(@GuardSatisfied SequencesJoin this) {
    return "[SequencesJoin of " + var1().name() + " " + var2().name() + "]";
  }

  @Pure
  @Override
  public boolean isSameFormula(Derivation other) {
    return (other instanceof SequencesJoin);
  }

  @SideEffectFree
  @Override
  public String esc_name(String index) {
    return String.format("join[%s,%s]", var1().esc_name(), var2().esc_name());
  }
}
