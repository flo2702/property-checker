package daikon.diff;

import daikon.PptSlice;
import daikon.inv.Invariant;
import java.io.PrintStream;
import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/**
 * <B>XorInvariantsVisitor</B> is a visitor that performs a standard Diff on two PptMaps, that is,
 * finds the set of Invariants in the XOR set of two PptMaps. However, while those XOR Invariants
 * were the end product of standard diff, this visitor is useful when the XOR set is a means to an
 * end, since you get back a data structure containing the XOR set.
 *
 * <p>Currently, this visitor actually modifies the first of the two PptMaps. This might be an
 * undesirable design call, but creating a PptMap from scratch is difficult given the constraining
 * creational pattern in place.
 */
public class XorInvariantsVisitor extends PrintDifferingInvariantsVisitor {

  /** Create an instance of XorInvariantsVisitor. */
  public XorInvariantsVisitor(PrintStream ps, boolean verbose, boolean printEmptyPpts) {
    super(ps, verbose, printEmptyPpts);
  }

  @Override
  public void visit(@NonNullNode PptNode node) {
    super.visit(node);
  }

  @Override
  public void visit(@NonNullNode InvNode node) {
    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();
    // do nothing if they are unique

    // :: error: nullnessnode.argument.type.incompatible
    if (shouldPrint(inv1, inv2)) {
      // do nothing, keep both
    } else {
      if (inv1 != null) {
        @NonNull PptSlice ppt = inv1.ppt;
        ppt.removeInvariant(inv1);
      }

      if (inv2 != null) {
        @NonNull PptSlice ppt = inv2.ppt;
        ppt.removeInvariant(inv2);
      }
    }
  }

  /**
   * Returns true if the pair of invariants should be printed, depending on their type,
   * relationship, and printability.
   */
  @Pure
  @Override
  // :: error: nullnessnode.contracts.postcondition.not.satisfied :: error: nullnessnode.override.param.invalid
  protected boolean shouldPrint(@NonNullIfNull("inv2") @Nullable Invariant inv1, @NonNullIfNull("inv1") @Nullable Invariant inv2) {
    // :: error: nullnessnode.argument.type.incompatible
    int rel = DetailedStatisticsVisitor.determineRelationship(inv1, inv2);
    if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2
        || rel == DetailedStatisticsVisitor.REL_SAME_UNJUST1_UNJUST2
        || rel == DetailedStatisticsVisitor.REL_DIFF_UNJUST1_UNJUST2
        || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST1
        || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST2) {
      return false;
    }

    if ((inv1 == null || !inv1.isWorthPrinting()) && (inv2 == null || !inv2.isWorthPrinting())) {
      return false;
    }

    return true;
  }
}
