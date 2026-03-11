package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class List {

    public int head;
    public @Nullable @Length(len="this.size - 1") List tail;

    public int size;

    @JMLClause("ensures this.head == head && this.tail == null && this.size == 1;")
    @JMLClause("assignable \\nothing;")
    @NonMonotonic
    // :: error: length.inconsistent.constructor.type :: error: length.initialization.fields.uninitialized
    public @Unique @Length(len="1") List(int head) {
        this.head = head;
        this.tail = null;
        this.size = 1;
    }

    @JMLClause("ensures this.head == head && this.tail == tail;")
    @JMLClause("assignable \\nothing;")
    @NonMonotonic
    // :: error: length.inconsistent.constructor.type :: error: length.contracts.postcondition.not.satisfied :: error: length.initialization.fields.uninitialized
    public @Unique @Length(len="n+1") List(int head, @Nullable @Length(len="n") List tail, int n) {
        this.head = head;
        this.tail = tail;
        this.size = tail == null ? 1 : tail.size + 1;
    }

    @EnsuresLength(value="this", len="n+1")
    @JMLClause("assignable this.*;")
    @NonMonotonic
    // :: error: length.contracts.postcondition.not.satisfied :: error: length.initialization.fields.uninitialized
    public void insert(
            @Unique @Length(len="n") List this,
            int newHead,
            int n
    ) {
        if (this.tail == null) {
            this.tail = new List(head);
        } else {
            this.tail = new List(this.head, this.tail, n - 1);
        }
        this.head = newHead;
        ++this.size;
    }
}
