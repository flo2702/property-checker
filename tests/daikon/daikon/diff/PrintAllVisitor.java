package daikon.diff;

import daikon.Global;
import daikon.Ppt;
import daikon.inv.Invariant;
import java.io.PrintStream;
import java.text.DecimalFormat;
import org.checkerframework.checker.nullness.qual.Nullable;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** Prints all the invariant pairs, including pairs containing identical invariants. */
public class PrintAllVisitor extends DepthFirstVisitor {

  // Protected so subclasses can use it.
  protected static final String lineSep = Global.lineSep;

  protected static boolean HUMAN_OUTPUT = false;

  private static DecimalFormat CONFIDENCE_FORMAT = new DecimalFormat("0.####");

  private PrintStream ps;
  private boolean verbose;
  private boolean printEmptyPpts;

  /**
   * Stores the output generated when visiting invariant nodes. This output cannot be printed
   * directly to the print stream, because the Ppt output must come before the Invariant output.
   */
  private StringBuilder bufOutput = new StringBuilder();

  public PrintAllVisitor(PrintStream ps, boolean verbose, boolean printEmptyPpts) {
    this.ps = ps;
    this.verbose = verbose;
    this.printEmptyPpts = printEmptyPpts;
  }

  /** Prints the pair of program points, and all the invariants contained within them. */
  @Override
  public void visit(@NonNullNode PptNode node) {
    // Empty the string buffer
    bufOutput.setLength(0);

    super.visit(node);

    if (bufOutput.length() > 0 || printEmptyPpts) {
      Ppt ppt1 = node.getPpt1();
      Ppt ppt2 = node.getPpt2();

      ps.print("<");
      if (ppt1 == null) {
        ps.print((String) null);
      } else {
        ps.print(ppt1.name());
      }

      if (ppt1 == null || ppt2 == null || !ppt1.name().equals(ppt2.name())) {
        ps.print(", ");
        if (ppt2 == null) {
          ps.print((String) null);
        } else {
          ps.print(ppt2.name());
        }
      }
      ps.println(">");
      ps.print(bufOutput.toString());
    }
  }

  /** Prints a pair of invariants. Includes the type of the invariants and their relationship. */
  @Override
  public void visit(@NonNullNode InvNode node) {

    if (HUMAN_OUTPUT) {
      printHumanOutput(node);
      return;
    }

    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();

    bufPrint("  <");

    if (inv1 == null) {
      bufPrint(null);
    } else {
      printInvariant(inv1);
    }
    bufPrint(", ");
    if (inv2 == null) {
      bufPrint((String) null);
    } else {
      printInvariant(inv2);
    }
    bufPrint(">");

    // :: error: nullnessnode.argument.type.incompatible
    int arity = DetailedStatisticsVisitor.determineArity(inv1, inv2);
    String arityLabel = DetailedStatisticsVisitor.ARITY_LABELS[arity];
    // :: error: nullnessnode.argument.type.incompatible
    int rel = DetailedStatisticsVisitor.determineRelationship(inv1, inv2);
    String relLabel = DetailedStatisticsVisitor.RELATIONSHIP_LABELS[rel];

    bufPrint(" (" + arityLabel + "," + relLabel + ")");

    bufPrintln();
  }

  /**
   * This method is an alternate printing procedure for an InvNode so that the output is more human
   * readable. The format resembles cvs diff with '+' and '-' signs for the differing invariants.
   * There is no information on justification or invariant type.
   */
  public void printHumanOutput(@NonNullNode InvNode node) {

    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();

    //    bufPrint("  <");

    if (inv1 != null && inv2 != null && inv1.format().equals(inv2.format())) {
      return;
    }

    if (inv1 == null) {
      //   bufPrint((String) null);
    } else {
      //  printInvariant(inv1);
      bufPrintln(("- " + inv1.format()).trim());
    }
    //    bufPrint(", ");
    if (inv2 == null) {
      //      bufPrint((String) null);
    } else {
      bufPrintln(("+ " + inv2.format()).trim());
      //      printInvariant(inv2);
    }
    //    bufPrint(">");

    // int arity = DetailedStatisticsVisitor.determineArity(inv1, inv2);
    // int rel = DetailedStatisticsVisitor.determineRelationship(inv1, inv2);
    // String arityLabel = DetailedStatisticsVisitor.ARITY_LABELS[arity];
    // String relLabel = DetailedStatisticsVisitor.RELATIONSHIP_LABELS[rel];
    //    bufPrint(" (" + arityLabel + "," + relLabel + ")");

    bufPrintln();
  }

  /**
   * Prints an invariant, including its printability and possibly its confidence. Example: "argv !=
   * null {0.9999+}".
   */
  protected void printInvariant(Invariant inv) {
    if (verbose) {
      bufPrint(inv.repr_prob());
      bufPrint(" {");
      printPrintability(inv);
      bufPrint("}");
    } else {
      bufPrint(inv.format());
      bufPrint(" {");
      printConfidence(inv);
      printPrintability(inv);
      bufPrint("}");
    }
  }

  /**
   * Prints the confidence of the invariant. Confidences between .9999 and 1 are rounded to .9999.
   */
  private void printConfidence(Invariant inv) {
    double conf = inv.getConfidence();
    if (.9999 < conf && conf < 1) {
      conf = .9999;
    }
    bufPrint(CONFIDENCE_FORMAT.format(conf));
  }

  /** Prints '+' if the invariant is worth printing, '-' otherwise. */
  // XXX This routine takes up most of diff's run time on large .inv
  // files, and is not particularly interesting. There should perhaps
  // be an option to turn it off. -SMcC
  private void printPrintability(Invariant inv) {
    if (inv.isWorthPrinting()) {
      bufPrint("+");
    } else {
      bufPrint("-");
    }
  }

  // "prints" by appending to a string buffer
  protected void bufPrint(@Nullable String s) {
    bufOutput.append(s);
  }

  protected void bufPrintln(@Nullable String s) {
    bufPrint(s);
    bufPrintln();
  }

  protected void bufPrintln() {
    bufOutput.append(Global.lineSep);
  }
}
