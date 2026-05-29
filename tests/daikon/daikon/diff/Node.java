package daikon.diff;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.packing.qual.Dependable;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

/**
 * All nodes must subclass this class.
 *
 * @param <CONTENT> half of the type of the objects stored in this node, which are {@code
 *     IPair<CONTENT,CONTENT>}
 * @param <CHILD> the type of the children; it is is ignored if there are no children
 */
public abstract class Node<@MaybeAliased CONTENT extends @Nullable @NullableNode Object, @MaybeAliased CHILD extends @NonNullNode Object> {

  /** The children of this node. */
  private List<CHILD> children = new ArrayList<>();

  /** Nonsensical for RootNode. */
  private @Dependable IPair<CONTENT, CONTENT> userObject;

  @Pure
  // :: error: nullnessnode.inconsistent.constructor.type :: error: nullnessnode.contracts.postcondition.not.satisfied
  protected @NonNullNode Node(@NonNullIfNull("right") CONTENT left, @NonNullIfNull("left") CONTENT right) {
    // :: error: nullnessnode.assignment.type.incompatible
    this.userObject = IPair.of(left, right);
  }

  public void add(@NonNullNode Node<CONTENT, CHILD> this, CHILD newChild) {
    children.add(newChild);
  }

  public Iterator<CHILD> children(@NonNullNode Node<CONTENT, CHILD> this) {
    return children.iterator();
  }

  /**
   * Returns the user object pair.
   *
   * @return the user object pair
   */
  public IPair<CONTENT, CONTENT> getUserObject(@NonNullNode Node<CONTENT, CHILD> this) {
    return userObject;
  }

  /**
   * Returns the first element of the user object pair.
   *
   * @return the first element of the user object pair
   */
  @Pure
  @JMLClause("ensures \\result == userObject.first;")
  public @NonNullIfNull("userObject.second") CONTENT getUserLeft(@NonNullNode Node<CONTENT, CHILD> this) {
    // :: error: nullnessnode.return.type.incompatible
    return userObject.first;
  }

  /**
   * Returns the second element of the user object pair.
   *
   * @return the second element of the user object pair
   */
  @Pure
  @JMLClause("ensures \\result == userObject.second;")
  public @NonNullIfNull("userObject.first") CONTENT getUserRight(@NonNullNode Node<CONTENT, CHILD> this) {
    // :: error: nullnessnode.return.type.incompatible
    return userObject.second;
  }

  public abstract void accept(@NonNullNode Node<CONTENT, CHILD> this, Visitor v);
}
