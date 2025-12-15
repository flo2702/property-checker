/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.kastel.property.checker;

import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.packing.PackingChecker;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.nullness.KeyForLatticeSubchecker;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeSubchecker;
import org.checkerframework.checker.nullness.NullnessChecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.reflection.MethodValChecker;
import org.checkerframework.framework.source.SupportedLintOptions;
import org.checkerframework.framework.source.SupportedOptions;

import java.io.File;
import java.nio.file.Paths;
import java.util.*;

@SupportedLintOptions({
        NullnessChecker.LINT_NOINITFORMONOTONICNONNULL,
        NullnessChecker.LINT_REDUNDANTNULLCOMPARISON,
        // Temporary option to forbid non-null array component types, which is allowed by default.
        // Forbidding is sound and will eventually be the default.
        // Allowing is unsound, as described in Section 3.3.4, "Nullness and arrays":
        //     https://eisop.github.io/cf/manual/#nullness-arrays
        // It is the default temporarily, until we improve the analysis to reduce false positives or we
        // learn what advice to give programmers about avoid false positive warnings.
        // See issue #986: https://github.com/typetools/checker-framework/issues/986
        "soundArrayCreationNullness",
        // Old name for soundArrayCreationNullness, for backward compatibility; remove in January 2021.
        "forbidnonnullarraycomponents",
        NullnessChecker.LINT_TRUSTARRAYLENZERO,
        NullnessChecker.LINT_PERMITCLEARPROPERTY,
})
@SupportedOptions({
    Config.LATTICES_FILE_OPTION,
    Config.INPUT_DIR_OPTION,
    Config.OUTPUT_DIR_OPTION,
    Config.QUAL_PKG_OPTION,
    Config.TRANSLATION_ONLY_OPTION,
    Config.OUTPUT_LANG_OPTION,
    Config.NO_EXCLUSITIVY_OPTION,
    Config.NO_INFER_UNPACK_OPTION,
    Config.KEEP_GENERICS_OPTION,
    Config.SHOULD_NOT_USE_TRAMPOLINE_OPTION,
    "assumeKeyFor",
    "assumeInitialized",
    "jspecifyNullMarkedAlias",
    "conservativeArgumentNullnessAfterInvocation"
})
public final class PropertyChecker extends PackingChecker {

    private ExclusivityChecker exclusivityChecker;
    private PackingFieldAccessSubchecker fieldAccessChecker;
    private NullnessLatticeSubchecker nullnessLatticeSubchecker;
    private List<LatticeSubchecker> latticeSubcheckers;
    private List<BaseTypeChecker> packingTargetCheckers;
    private List<BaseTypeChecker> subcheckers;
    private List<String> shouldNotUseTrampoline;

    private Map<String, PriorityQueue<CooperativeVisitor.Result>> results = new HashMap<>();

    public PropertyChecker() { }

    @Override
    protected PropertyVisitor createSourceVisitor() {
        return new PropertyVisitor(this);
    }

    @Override
    public boolean checkPrimitives() {
        return true;
    }

    @Override
    public PropertyVisitor getVisitor() {
        return (PropertyVisitor) super.getVisitor();
    }

    protected String getAbsoluteSourceFileName() {
        return Paths.get(getVisitor().getRoot().getSourceFile().getName()).toAbsolutePath().toString();
    }

    protected String getRelativeSourceFileName() {
        String classesDir = Paths.get(getInputDir()).toAbsolutePath().toString();
        return getAbsoluteSourceFileName().substring(classesDir.length());
    }

    @Override
    public List<BaseTypeChecker> getTargetCheckers() {
        if (packingTargetCheckers == null) {
            packingTargetCheckers = new ArrayList<>();
            packingTargetCheckers.add(getExclusivityChecker());
            packingTargetCheckers.add(getNullnessLatticeSubchecker());
            packingTargetCheckers.addAll(getLatticeSubcheckers());
        }

        return packingTargetCheckers;
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        if (subcheckers == null) {
            subcheckers = new ArrayList<>();
            subcheckers.add(getFieldAccessChecker());

            if (!hasOptionNoSubcheckers("noExclusivity")) {
                subcheckers.add(getExclusivityChecker());
            }

            if (shouldResolveReflection()) {
                subcheckers.add(new MethodValChecker());
            }
            if (!hasOptionNoSubcheckers("assumeKeyFor")) {
                subcheckers.add(new KeyForLatticeSubchecker(this));
            }
            subcheckers.add(getNullnessLatticeSubchecker());

            subcheckers.addAll(getLatticeSubcheckers());
        }
        return subcheckers;
    }

    @Override
    @SuppressWarnings("unchecked")
    public <T extends BaseTypeChecker> @Nullable T getSubchecker(Class<T> checkerClass) {
        for (BaseTypeChecker checker : getSubcheckers()) {
            if (checkerClass.isInstance(checker)) {
                return (T) checker;
            }
        }

        return null;
    }

    public ExclusivityChecker getExclusivityChecker() {
        if (exclusivityChecker == null) {
            exclusivityChecker = new ExclusivityChecker(this);
        }

        return exclusivityChecker;
    }

    public NullnessLatticeSubchecker getNullnessLatticeSubchecker() {
        if (nullnessLatticeSubchecker == null) {
            nullnessLatticeSubchecker = new NullnessLatticeSubchecker(this, new File(getInputDir()));
        }

        return nullnessLatticeSubchecker;
    }

    public PackingFieldAccessSubchecker getFieldAccessChecker() {
        if (fieldAccessChecker == null) {
            fieldAccessChecker = new PackingFieldAccessSubchecker(this);
        }

        return fieldAccessChecker;
    }

    public List<LatticeSubchecker> getLatticeSubcheckers() {
        if (latticeSubcheckers == null) {
            latticeSubcheckers = new ArrayList<>();

            String[] lattices = getLattices();
            String inputDir = getInputDir();
            String qualPackage = getQualPackage();

            int ident = 1;
            for (String lattice : lattices) {
                latticeSubcheckers.add(new LatticeSubchecker(this, new File(lattice.strip()), new File(inputDir), qualPackage, ident++));
            }
        }

        return Collections.unmodifiableList(latticeSubcheckers);
    }
    
    public String[] getLattices() {
        String option = getOptionsNoSubcheckers().get(Config.LATTICES_FILE_OPTION);
        if (option == null) {
            return new String[] {};
        } else {
            return option.split(Config.SPLIT);
        }
    }

    public String getOutputDir() {
    	return getOptionsNoSubcheckers().get(Config.OUTPUT_DIR_OPTION);
    }
    
    public String getQualPackage() {
    	return getOptionsNoSubcheckers().get(Config.QUAL_PKG_OPTION);
    }

    public boolean shouldKeepGenerics() {
        return getBooleanOption(Config.KEEP_GENERICS_OPTION, false);
    }

    public void addResult(String fileName, CooperativeVisitor.Result result) {
        if (!results.containsKey(fileName)) {
            results.put(fileName, new PriorityQueue<>(
                        (r0, r1) -> r0.getChecker().getIdent() - r1.getChecker().getIdent()));

            results.get(fileName).add(result);
        } else {
            Optional<CooperativeVisitor.Result> optional = results.get(fileName).stream().filter(r -> r.getChecker().equals(result.getChecker())).findAny();
            if (optional.isPresent()) {
                CooperativeVisitor.Result r = optional.get();
                r.addAll(result);
            } else {
                results.get(fileName).add(result);
            }
        }
    }

    public List<CooperativeVisitor.Result> getResults(String fileName) {
        PriorityQueue<CooperativeVisitor.Result> q = results.get(fileName);
        return q != null ? Collections.unmodifiableList(new ArrayList<>(q)) : Collections.emptyList();
    }

    public PropertyAnnotatedTypeFactory getPropertyFactory() {
        return (PropertyAnnotatedTypeFactory) getTypeFactory();
    }

    private List<String> getShouldNotUseTrampoline() {
        if (shouldNotUseTrampoline == null) {
            String option = getOption(Config.SHOULD_NOT_USE_TRAMPOLINE_OPTION, "");
            shouldNotUseTrampoline = option.isEmpty() ? List.of() : Arrays.asList(option.split(Config.SPLIT));
        }

        return Collections.unmodifiableList(shouldNotUseTrampoline);
    }

    public boolean shouldNotUseTrampoline(String typeName) {
        return getShouldNotUseTrampoline().stream().anyMatch(s -> typeName.startsWith(s));
    }
}
