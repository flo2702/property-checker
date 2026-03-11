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
package edu.kit.kastel.property.lattice;

import edu.kit.kastel.property.lattice.PropertyAnnotationType.Parameter;
import edu.kit.kastel.property.util.Pair;
import edu.kit.kastel.property.util.UnorderedPair;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import java.util.*;

public class Lattice {

    private String ident;

    private GenericAnnotatedTypeFactory<?,?,?,?> factory;

    private Map<String, PropertyAnnotationType> annotationTypes;
    private Map<Pair<String, String>, SubAnnotationRelation> relations;
    private Map<UnorderedPair<String>, List<Bound>> meets;
    private Map<UnorderedPair<String>, List<Bound>> joins;

    public Lattice(
            GenericAnnotatedTypeFactory<?,?,?,?> factory,
            String ident,
            Map<String, PropertyAnnotationType> annotationTypes,
            Map<Pair<String, String>, SubAnnotationRelation> relations,
            Map<UnorderedPair<String>, List<Bound>> meets,
            Map<UnorderedPair<String>, List<Bound>> joins) {
        this.factory = factory;
        this.ident = ident;
        this.annotationTypes = annotationTypes;
        this.relations = relations;
        this.meets = meets;
        this.joins = joins;
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return String.format("%s:\n\t%s\n\t%s\n\t%s\n\t%s", ident, annotationTypes.values(), relations.values(), meets, joins);
    }

    public String getIdent() {
        return ident;
    }

    public AnnotationMirror getTop() {
        return factory.getQualifierHierarchy().getTopAnnotations().first();
    }

    public Map<String, PropertyAnnotationType> getAnnotationTypes() {
        return Collections.unmodifiableMap(annotationTypes);
    }

    public Map<Pair<String, String>, SubAnnotationRelation> getRelations() {
        return Collections.unmodifiableMap(relations);
    }

    public Map<UnorderedPair<String>, List<Bound>> getJoins() {
        return Collections.unmodifiableMap(joins);
    }

    public Map<UnorderedPair<String>, List<Bound>> getMeets() {
        return Collections.unmodifiableMap(meets);
    }

    public PropertyAnnotation getPropertyAnnotation(AnnotatedTypeMirror mirror) {
        PropertyAnnotation result = getPropertyAnnotation(mirror.getAnnotationInHierarchy(getTop()));

        // Replace @NonNull on primitives by @Nullable to avoid type error in JML translation
        if (TypesUtils.isPrimitive(mirror.getUnderlyingType()) && result.getAnnotationType().isNonNull()) {
            result = new PropertyAnnotation(this.annotationTypes.get("Nullable"), List.of());
        }
        if (TypesUtils.isPrimitive(mirror.getUnderlyingType()) && result.getAnnotationType().isInv()) {
            result = new PropertyAnnotation(this.annotationTypes.get("InvUnknown"), List.of());
        }

        return result;
    }

    public PropertyAnnotation getEffectivePropertyAnnotation(AnnotatedTypeMirror mirror) {
        PropertyAnnotation result = getPropertyAnnotation(mirror.getEffectiveAnnotationInHierarchy(getTop()));

        // Replace @NonNull on primitives by @Nullable to avoid type error in JML translation
        if (TypesUtils.isPrimitive(mirror.getUnderlyingType()) && result.getAnnotationType().isNonNull()) {
            result = new PropertyAnnotation(this.annotationTypes.get("Nullable"), List.of());
        }
        if (TypesUtils.isPrimitive(mirror.getUnderlyingType()) && result.getAnnotationType().isInv()) {
            result = new PropertyAnnotation(this.annotationTypes.get("InvUnknown"), List.of());
        }

        return result;
    }

    public PropertyAnnotation getPropertyAnnotation(AnnotationMirror mirror) {
        if (mirror == null) {
            return getPropertyAnnotation(getTop());
        }
        
        PropertyAnnotationType type = annotationTypes.get(
                mirror.getAnnotationType().asElement().getSimpleName().toString());

        List<String> actualParams = new ArrayList<>();
        for (Parameter param : type.getParameters()) {
            String paramStr = AnnotationUtils.getElementValue(mirror, param.getName(), String.class, true);
            actualParams.add(paramStr);
        }

        return new PropertyAnnotation(type, actualParams);
    }

    public EvaluatedPropertyAnnotation getEvaluatedPropertyAnnotation(AnnotatedTypeMirror mirror) {
        return getEvaluatedPropertyAnnotation(mirror.getAnnotationInHierarchy(getTop()));
    }

    private Map<AnnotationMirror, EvaluatedPropertyAnnotation> epaCache = new HashMap<>();

    public EvaluatedPropertyAnnotation getEvaluatedPropertyAnnotation(AnnotationMirror mirror) {
        if (epaCache.containsKey(mirror)) {
            return epaCache.get(mirror);
        }

        EvaluatedPropertyAnnotation result;
        PropertyAnnotationType type = annotationTypes.get(
                mirror.getAnnotationType().asElement().getSimpleName().toString());

        try {
            List<Object> actualParams = new ArrayList<>();
            for (Parameter param : type.getParameters()) {
                @SuppressWarnings("deprecation")
                String paramStr = AnnotationUtils.getElementValue(mirror, param.getName(), String.class, true);
                actualParams.add(param.getType().fromString(paramStr));
            }

            result = new EvaluatedPropertyAnnotation(type, actualParams);
        } catch(IllegalArgumentException e) {
            // If fromString throws an IllegalArgumentException, the parameter is not a literal, but
            // a composite expression.
            // The Checker type system always delegates expression of such types to KeY.
            result = null;
        }

        epaCache.put(mirror, result);
        return result;
    }
}
