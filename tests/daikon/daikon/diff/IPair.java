package daikon.diff;

import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.checkerframework.framework.qual.Covariant;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.Dependable;

// Simplified version of plumelib class for Kukicha case study
public class IPair<@MaybeAliased V1, @MaybeAliased V2> {

    /** The first element of the pair. */
    public final @Dependable V1 first;

    /** The second element of the pair. */
    public final @Dependable V2 second;

    @Pure
    @JMLClause("ensures this.first == first && this.second == second;")
    private IPair(V1 first, V2 second) {
        this.first = first;
        this.second = second;
    }

    @Pure
    @JMLClause("ensures \\result != null && \\fresh(\\result) && \\fresh(\\result.*) && \\invariant_free_for(\\result);")
    @JMLClause("ensures \\result.first == first && \\result.second == second;")
    public static <T1, T2> IPair<T1, T2> of(@MaybeAliased T1 first, @MaybeAliased T2 second) {
        return new IPair<>(first, second);
    }
}
