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

import edu.kit.kastel.property.util.Functional;
import org.checkerframework.javacutil.AnnotationBuilder;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public class EvaluatedPropertyAnnotation {

    private PropertyAnnotationType annotationType;
    private List<Object> actualParameters;

    public EvaluatedPropertyAnnotation(
            PropertyAnnotationType annotationType,
            List<Object> actualParameters) {
        this.annotationType = annotationType;
        this.actualParameters = actualParameters;
    }

    public PropertyAnnotationType getAnnotationType() {
        return annotationType;
    }

    public List<Object> getActualParameters() {
        return Collections.unmodifiableList(actualParameters);
    }

    public boolean isCheckable() {
        return annotationType.getPropertyMethod() != null;
    }

    public boolean checkProperty(Object subject) {
        Method checkerMethod = annotationType.getPropertyMethod();

        if (checkerMethod == null) {
            throw new IllegalStateException();
        }

        try {
            List<Object> args = new LinkedList<>(actualParameters);
            args.add(0, subject);

            return (Boolean) checkerMethod.invoke(null, args.toArray());
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new AssertionError();
        }
    }

    public boolean checkWFCondition() {
        Method checkerMethod = annotationType.getWFMethod();

        if (checkerMethod == null) {
            throw new IllegalStateException();
        }

        try {
            return (Boolean) checkerMethod.invoke(null, actualParameters.toArray());
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new AssertionError();
        }
    }


    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return annotationType.getName() + "(" + actualParameters.stream().map(Object::toString).collect(Collectors.joining(", ")) + ")";
    }

    @Override
    public int hashCode() {
        return Objects.hash(actualParameters, annotationType);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof EvaluatedPropertyAnnotation)) {
            return false;
        }
        EvaluatedPropertyAnnotation other = (EvaluatedPropertyAnnotation) obj;
        return Objects.equals(actualParameters, other.actualParameters)
                && Objects.equals(annotationType, other.annotationType);
    }

    public String getName() {
        return getAnnotationType().getName();
    }

    public AnnotationMirror toAnnotationMirror(ProcessingEnvironment env) {
        AnnotationBuilder builder = new AnnotationBuilder(env, getAnnotationType().toClass());

        Functional.zip(
                getAnnotationType().getParameters().stream(),
                getActualParameters().stream())
            .forEach(p -> { p.first.setValue(builder, p.second); });

        return builder.build();
    }
}
