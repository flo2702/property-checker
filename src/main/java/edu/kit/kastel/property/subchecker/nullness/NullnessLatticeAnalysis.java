package edu.kit.kastel.property.subchecker.nullness;

import com.sun.source.tree.Tree;
import org.checkerframework.checker.nullness.NullnessNoInitAnalysis;
import org.checkerframework.checker.nullness.NullnessNoInitAnnotatedTypeFactory;
import org.checkerframework.checker.nullness.NullnessNoInitStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class NullnessLatticeAnalysis extends NullnessNoInitAnalysis {
    /**
     * Creates a new {@code NullnessAnalysis}.
     *
     * @param checker the checker
     * @param factory the factory
     */
    public NullnessLatticeAnalysis(BaseTypeChecker checker, NullnessNoInitAnnotatedTypeFactory factory) {
        super(checker, factory);
    }

    @Override
    public NullnessNoInitStore createEmptyStore(boolean sequentialSemantics) {
        return new NullnessLatticeStore(this, sequentialSemantics);
    }

    @Override
    public NullnessNoInitStore createCopiedStore(NullnessNoInitStore s) {
        return new NullnessLatticeStore(s);
    }


    // TODO: Duplicated logic from PackingClientAnalysis

    private Tree position = null;
    /**
     * Returns the tree currently set to be the context for determining the uniqueness of the receiver
     * This must be set and kept up to date by PackingClientTransfer and its sub classes via {@link #setPosition(Tree)}.
     *
     * @return A {@code Tree}.
     */
    @Nullable
    public Tree getLocalTree() {
        return position;
    }

    public void setPosition(@Nullable Tree position) {
        this.position = position;
    }
}
