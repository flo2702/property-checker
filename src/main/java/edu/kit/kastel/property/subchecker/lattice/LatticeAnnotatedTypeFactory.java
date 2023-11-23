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
package edu.kit.kastel.property.subchecker.lattice;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Collectors;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.util.Elements;

import org.apache.commons.lang3.StringUtils;
import org.checkerframework.checker.initialization.qual.FBCBottom;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.InitializationAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.ElementQualifierHierarchy;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.DefaultQualifierKindHierarchy;
import org.checkerframework.framework.util.QualifierKind;
import org.checkerframework.framework.util.QualifierKindHierarchy;
import org.checkerframework.framework.util.dependenttypes.DependentTypesHelper;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.BugInCF;
import org.checkerframework.javacutil.Pair;

import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.lattice.Bound;
import edu.kit.kastel.property.lattice.Checkable;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.lattice.SubAnnotationRelation;
import edu.kit.kastel.property.lattice.compiler.ClassBuilder;
import edu.kit.kastel.property.lattice.parser.LatticeParser;
import edu.kit.kastel.property.lattice.parser.ParseException;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.UnorderedPair;

public class LatticeAnnotatedTypeFactory
        extends InitializationAnnotatedTypeFactory<LatticeValue, LatticeStore, LatticeTransfer, LatticeAnalysis> {

    private Lattice lattice;
    private LatticeSubchecker latticeChecker;

    public LatticeAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);

        this.latticeChecker = (LatticeSubchecker) checker;

        try (BufferedReader reader = new BufferedReader(new FileReader(
                latticeChecker.getLatticeFile()))) {
            Lattice parsedLattice = new LatticeParser(this).parse(
                    reader.lines().collect(Collectors.joining(StringUtils.LF)));

            this.lattice = parsedLattice;
        } catch (IOException | ParseException e) {
            e.printStackTrace();
            System.exit(1);
        }

        setCheckerMethods(
                lattice.getAnnotationTypes().values().stream()
                    .map(PropertyAnnotationType::getWellFormednessCheckable)
                    .collect(Collectors.toList()),
                Config.CHECKERS_CLASS_WELL_FORMEDNESS,
                Config::methodWellFormedness);

        setCheckerMethods(
                lattice.getAnnotationTypes().values().stream()
                    .map(PropertyAnnotationType::getPropertyCheckable)
                    .collect(Collectors.toList()),
                Config.CHECKERS_CLASS_PROPERTIES,
                Config::methodProperties);

        setCheckerMethods(
                new ArrayList<>(lattice.getRelations().values()),
                Config.CHECKERS_CLASS_RELATIONS,
                Config::methodRelations);

        for (List<Bound> joins : lattice.getJoins().values()) {
            setCheckerMethods(
                    joins,
                    Config.CHECKERS_CLASS_JOINS,
                    Config::methodJoins);
        }

        for (List<Bound> meets : lattice.getMeets().values()) {
            setCheckerMethods(
                    meets,
                    Config.CHECKERS_CLASS_MEETS,
                    Config::methodMeets);
        }

        postInit();
    }

    private <T extends Checkable> void setCheckerMethods(List<T> checkables, String className, Function<T, String> methodName) {
        ClassBuilder compiler = new ClassBuilder(className + getChecker().getIdent());

        for (T chk : checkables) {
            Class<?>[] paramTypes = chk.getParameterTypes();

            if (paramTypes.length > 0 && paramTypes[0] == null) {
                // null represents the any type, so we add a method for Object and all primitives.

                paramTypes[0] = Object.class;
                compiler.addMethod(
                        methodName.apply(chk),
                        chk.getCondition(),
                        Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                        chk.getParameterNames(),
                        chk.toString());

                for (Class<?> primitive : ClassUtils.PRIMITIVES) {
                    paramTypes[0] = primitive;
                    compiler.addMethod(
                            methodName.apply(chk),
                            chk.getCondition(),
                            Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                            chk.getParameterNames(),
                            chk.toString());
                }
            } else {
                compiler.addMethod(
                        methodName.apply(chk),
                        chk.getCondition(),
                        Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                        chk.getParameterNames(),
                        chk.toString());
            }
        }
        
        Class<?> cls = compiler.compile(latticeChecker.getProjectClassLoader());

        for (T chk : checkables) {
            try {
                Class<?>[] paramTypes = chk.getParameterTypes();

                if (paramTypes.length > 0 && paramTypes[0] == null) {
                    paramTypes[0] = Object.class;
                }

                chk.setCheckerMethod(cls.getMethod(methodName.apply(chk), paramTypes));
            } catch (NoSuchMethodException | SecurityException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>();
        treeAnnotators.add(new CommitmentTreeAnnotator(this));
        /*if (dependentTypesHelper != null) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }*/
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected QualifierHierarchy createQualifierHierarchy() {
        return new LatticeQualifierHierarchy(getSupportedTypeQualifiers(), elements);
    }

    @Override
    protected DependentTypesHelper createDependentTypesHelper() {
        return new LatticeDependentTypesHelper(this);
    }

    public Lattice getLattice() {
        return lattice;
    }

    public LatticeSubchecker getChecker() {
        return (LatticeSubchecker) checker;
    }

    public AnnotationMirror getTop() {
        return ((LatticeQualifierHierarchy) getQualifierHierarchy()).getTop();
    }

    public AnnotationMirror getBottom() {
        return ((LatticeQualifierHierarchy) getQualifierHierarchy()).getBottom();
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        Set<Class<? extends Annotation>> result = new HashSet<>(
                lattice.getAnnotationTypes().values().stream()
                .map(PropertyAnnotationType::toClass).collect(Collectors.toList()));

        result.add(UnderInitialization.class);
        result.add(Initialized.class);
        result.add(UnknownInitialization.class);
        result.add(FBCBottom.class);

        return result;
    }

	@Override
	public AnnotationMirror getFieldInvariantAnnotation(
            AnnotatedTypeMirror type, VariableElement fieldElement) {
		AnnotationMirror anno = type.getAnnotationInHierarchy(getTop());
		return AnnotationUtils.areSame(anno, getTop()) ? null : anno;
	}

	@Override
	protected boolean hasFieldInvariantAnnotation(AnnotatedTypeMirror type, VariableElement fieldElement) {
		AnnotationMirror anno = type.getAnnotationInHierarchy(getTop());
		return !AnnotationUtils.areSame(anno, getTop());
	}
	
	@Override
	public boolean isFieldInvariantAnnotation(AnnotationMirror anno) {
		return !AnnotationUtils.areSame(anno, getTop());
	}

    protected final class LatticeInitQualifierHierarchy extends InitializationQualifierHierarchy {

		@Override
		protected boolean isSubtypeWithElements(AnnotationMirror subAnno, QualifierKind subKind,
				AnnotationMirror superAnno, QualifierKind superKind) {
			return isSubtypeInitialization(subAnno, subKind, superAnno, superKind);
		}

		@Override
		protected AnnotationMirror leastUpperBoundWithElements(AnnotationMirror a1, QualifierKind qualifierKind1,
				AnnotationMirror a2, QualifierKind qualifierKind2, QualifierKind lubKind) {
			return leastUpperBoundInitialization(a1, qualifierKind1, a2, qualifierKind2);
		}

		@Override
		protected AnnotationMirror greatestLowerBoundWithElements(AnnotationMirror a1, QualifierKind qualifierKind1,
				AnnotationMirror a2, QualifierKind qualifierKind2, QualifierKind glbKind) {
			return greatestLowerBoundInitialization(a1, qualifierKind1, a2, qualifierKind2);
		}
        
        @Override
        protected QualifierKindHierarchy createQualifierKindHierarchy(
        		Collection<Class<? extends Annotation>> qualifierClasses) {
        	return new LatticeQualifierKindHierarchy(qualifierClasses);
        }
    }

    protected final class LatticeQualifierHierarchy extends ElementQualifierHierarchy {

        private AnnotationMirror top;
        private AnnotationMirror bottom;

        private LatticeInitQualifierHierarchy initQualifierHierarchy;

        public LatticeQualifierHierarchy(Set<Class<? extends Annotation>> set, Elements elements) {
            super(set, elements);
            initQualifierHierarchy = new LatticeInitQualifierHierarchy();
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            if (isInitAnnotation(subAnno) || isInitAnnotation(superAnno)) {
                return isInitAnnotation(subAnno) && isInitAnnotation(superAnno)
                        && initQualifierHierarchy.isSubtype(subAnno, superAnno);
            }

            if (AnnotationUtils.areSame(superAnno, getTop()) || AnnotationUtils.areSame(subAnno, getBottom())) {
                return true;
            }

            EvaluatedPropertyAnnotation subEpa = lattice.getEvaluatedPropertyAnnotation(subAnno);
            EvaluatedPropertyAnnotation superEpa = lattice.getEvaluatedPropertyAnnotation(superAnno);

            if (subEpa == null || superEpa == null) {
                return false;
            }

            if (AnnotationUtils.areSame(subAnno, superAnno)) {
                return true;
            }

            SubAnnotationRelation rel = lattice.getRelations().get(Pair.of(
                    subAnno.getAnnotationType().asElement().getSimpleName().toString(),
                    superAnno.getAnnotationType().asElement().getSimpleName().toString()));

            if (rel == null) {
                return false;
            }

            return rel.checkCondition(subEpa, superEpa);
        }

        @Override
        public AnnotationMirror leastUpperBound(AnnotationMirror a1, AnnotationMirror a2) {
            if (isInitAnnotation(a1) || isInitAnnotation(a2)) {
                if (isInitAnnotation(a1) && isInitAnnotation(a2)) {
                    return initQualifierHierarchy.leastUpperBound(a1, a2);
                } else {
                    return null;
                }
            }

            if (AnnotationUtils.areSame(a1, a2)) {
                return a1;
            } else if (isSubtype(a1, a2)) {
                if (isSubtype(a2, a1)) {
                    throw new BugInCF(
                            "Cycle in type lattice between " + a1 + " and " + a2); //$NON-NLS-1$ //$NON-NLS-2$
                } else {
                    return a2;
                }
            } else if (isSubtype(a2, a1)) {
                return a1;
            } else {
                return bound(a1, a2, lattice.getJoins(), getTop());
            }
        }

        @Override
        public AnnotationMirror greatestLowerBound(AnnotationMirror a1, AnnotationMirror a2) {
            if (isInitAnnotation(a1) || isInitAnnotation(a2)) {
                if (isInitAnnotation(a1) && isInitAnnotation(a2)) {
                    return initQualifierHierarchy.greatestLowerBound(a1, a2);
                } else {
                    return null;
                }
            }

            if (AnnotationUtils.areSame(a1, a2)) {
                return a1;
            } else if (isSubtype(a1, a2)) {
                if (isSubtype(a2, a1)) {
                    throw new BugInCF(
                            "Cycle in type lattice between " + a1 + " and " + a2); //$NON-NLS-1$ //$NON-NLS-2$
                } else {
                    return a1;
                }
            } else if (isSubtype(a2, a1)) {
                return a2;
            } else {
                return bound(a1, a2, lattice.getMeets(), getBottom());
            }
        }

        public AnnotationMirror getTop() {
            if (top == null) {
                top = getTopAnnotations().stream().filter(m -> !AnnotationUtils.areSame(m, UNKNOWN_INITIALIZATION)).findAny().get();
            }

            return top;
        }

        public AnnotationMirror getBottom() {
            if (bottom == null) {
                bottom = getBottomAnnotations().stream().filter(m -> !AnnotationUtils.areSame(m, FBCBOTTOM)).findAny().get();
            }
            return bottom;
        }
        
        @Override
        protected QualifierKindHierarchy createQualifierKindHierarchy(
        		Collection<Class<? extends Annotation>> qualifierClasses) {
        	return new LatticeQualifierKindHierarchy(qualifierClasses);
        }

        private boolean isInitAnnotation(AnnotationMirror a) {
            return getQualifierKind(a).isInSameHierarchyAs(getQualifierKind(INITIALIZED));
        }

        private AnnotationMirror bound(
                AnnotationMirror a1,
                AnnotationMirror a2,
                Map<UnorderedPair<String>, List<Bound>> bounds,
                AnnotationMirror defaultResult) {
            UnorderedPair<String> names = new UnorderedPair<>(
                    a1.getAnnotationType().asElement().getSimpleName().toString(),
                    a2.getAnnotationType().asElement().getSimpleName().toString());

            if (bounds.get(names) == null) {
                return defaultResult;
            }

            EvaluatedPropertyAnnotation epa1 = lattice.getEvaluatedPropertyAnnotation(a1);
            EvaluatedPropertyAnnotation epa2 = lattice.getEvaluatedPropertyAnnotation(a2);

            if (epa1 == null || epa2 == null) {
                return defaultResult;
            }

            for (Bound bound : bounds.get(names)) {
                Pair<PropertyAnnotation, PropertyAnnotation> ops = bound.getOperands().toOrderedPair();
                if (!ops.first.getName().equals(a1.getAnnotationType().asElement().getSimpleName().toString())) {
                    AnnotationMirror temp = a1;
                    a1 = a2;
                    a2 = temp;
                }

                if (bound.checkCondition(epa1, epa2)) {
                    LinkedHashMap<String, Class<?>> evaluationTypeContext = new LinkedHashMap<>();
                    LinkedHashMap<String, Object> evaluationValueContext = new LinkedHashMap<>();

                    for (int i = 0; i < epa1.getActualParameters().size(); ++i) {
                        evaluationTypeContext.put(
                                ops.first.getActualParameters().get(i),
                                epa1.getAnnotationType().getParameters().get(i).getType().toClass());
                        evaluationValueContext.put(
                                ops.first.getActualParameters().get(i),
                                epa1.getActualParameters().get(i));
                    }

                    for (int i = 0; i < epa2.getActualParameters().size(); ++i) {
                        evaluationTypeContext.put(
                                ops.second.getActualParameters().get(i),
                                epa2.getAnnotationType().getParameters().get(i).getType().toClass());
                        evaluationValueContext.put(
                                ops.second.getActualParameters().get(i),
                                epa2.getActualParameters().get(i));
                    }

                    return bound.getBound().evaluate(latticeChecker.getParentChecker(), evaluationTypeContext, evaluationValueContext).toAnnotationMirror(processingEnv);
                }
            }

            return defaultResult;
        }
    }
    
    protected final class LatticeQualifierKindHierarchy extends DefaultQualifierKindHierarchy {

		public LatticeQualifierKindHierarchy(
				Collection<Class<? extends Annotation>> qualifierClasses) {
			super(qualifierClasses);
		}

		public LatticeQualifierKindHierarchy(
				Collection<Class<? extends Annotation>> qualifierClasses,
				Class<? extends Annotation> bottom) {
			super(qualifierClasses, bottom);
		}
		
		@Override
		protected Map<DefaultQualifierKind, Set<DefaultQualifierKind>> createDirectSuperMap() {
	        Map<DefaultQualifierKind, Set<DefaultQualifierKind>> directSuperMap = super.createDirectSuperMap();
	        
	        for (DefaultQualifierKind qualifierKind : qualifierKinds) {
	        	if (!directSuperMap.containsKey(qualifierKind)) {
	        		directSuperMap.put(qualifierKind, new TreeSet<>());
	        	}
	        }
	        
			for (Pair<String,String> p : lattice.getRelations().keySet()) {
				if (p.first.equals(p.second)) {
					continue;
				}
				
				DefaultQualifierKind subQual = unqualifiedNameToQualifierKind(p.first);
				DefaultQualifierKind superQual = unqualifiedNameToQualifierKind(p.second);
				
				directSuperMap.get(subQual).add(superQual);
			}
			
	        return directSuperMap;
		}
		
		private DefaultQualifierKind unqualifiedNameToQualifierKind(String name) {
			String qualifiedName = latticeChecker.getQualPackage() + '.' + name;
			return nameToQualifierKind.get(qualifiedName);
		}
    	
    }
}
