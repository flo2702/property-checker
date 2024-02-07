package edu.kit.kastel.property.subchecker.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SourceChecker;

import java.util.List;
import java.util.Set;

/**
 * This is the entry point for exclusivity type-checking.
 */
public class ExclusivityChecker extends BaseTypeChecker {

    public ExclusivityChecker(PropertyChecker parent) {
        setProcessingEnvironment(parent.getProcessingEnvironment());
        treePathCacher = parent.getTreePathCacher();
        setParentChecker(parent);
    }

    public ExclusivityChecker() { }

    @Override
    public @Nullable PropertyChecker getParentChecker() {
        return (PropertyChecker) super.getParentChecker();
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        return List.of(); //List.of(getParentChecker().getFieldAccessChecker());
    }

    @Override
    public <T extends BaseTypeChecker> @Nullable T getSubchecker(Class<T> checkerClass) {
        if (checkerClass == PackingFieldAccessSubchecker.class) {
            return (T) getParentChecker().getFieldAccessChecker();
        }

        return null;
    }

    @Override
    public ExclusivityAnnotatedTypeFactory getTypeFactory() {
        return (ExclusivityAnnotatedTypeFactory) super.getTypeFactory();
    }
}
