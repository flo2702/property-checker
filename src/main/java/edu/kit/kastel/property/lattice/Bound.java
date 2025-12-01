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
import edu.kit.kastel.property.lattice.PropertyAnnotationType.ParameterType;
import edu.kit.kastel.property.util.Pair;
import edu.kit.kastel.property.util.UnorderedPair;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Bound implements Checkable {

    private BoundType boundType;
    private UnorderedPair<PropertyAnnotation> operands;
    private PropertyAnnotation bound;
    private String condition;
    private Method checkerMethod;
    private int line;

    public Bound(
            BoundType boundType,
            UnorderedPair<PropertyAnnotation> operands,
            PropertyAnnotation bound,
            String condition,
            int line) {
        this.boundType = boundType;
        this.operands = operands;
        this.bound = bound;
        this.condition = condition;
        this.line = line;
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return String.format(
                "%s %s = %s for %s",
                boundType.toString().toLowerCase(),
                operands,
                bound,
                condition);
    }



    @Override
    public int hashCode() {
        return Objects.hash(bound, boundType, checkerMethod, condition, line, operands);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof Bound)) {
            return false;
        }
        Bound other = (Bound) obj;
        return Objects.equals(bound, other.bound) && boundType == other.boundType
                && Objects.equals(checkerMethod, other.checkerMethod)
                && Objects.equals(condition, other.condition) && line == other.line
                && Objects.equals(operands, other.operands);
    }

    public int getLine() {
        return line;
    }

    public void setCheckerMethod(Method checkerMethod) {
        this.checkerMethod = checkerMethod;
    }

    public Method getCheckerMethod() {
        return checkerMethod;
    }

    public BoundType getBoundType() {
        return boundType;
    }

    public UnorderedPair<PropertyAnnotation> getOperands() {
        return operands;
    }

    public UnorderedPair<String> getOperandNames() {
        return new UnorderedPair<>(operands.toSet().stream().map(PropertyAnnotation::getName).collect(Collectors.toSet()));
    }

    public PropertyAnnotation getBound() {
        return bound;
    }

    public String getCondition() {
        return condition;
    }

    @Override
    public String[] getParameterNames() {
        Pair<PropertyAnnotation, PropertyAnnotation> p = getOperands().toOrderedPair();
        return Stream.concat(
                p.first.getActualParameters().stream(),
                p.second.getActualParameters().stream()).toArray(String[]::new);
    }

    @Override
    public Class<?>[] getParameterTypes() {
        Pair<PropertyAnnotation, PropertyAnnotation> p = getOperands().toOrderedPair();
        return Stream.concat(
                p.first.getAnnotationType().getParameters().stream(),
                p.second.getAnnotationType().getParameters().stream())
        .map(Parameter::getType).map(ParameterType::toClass).toArray(Class<?>[]::new);
    }

    public boolean checkCondition(
            EvaluatedPropertyAnnotation a1,
            EvaluatedPropertyAnnotation a2) {
        return checkCondition(a1.getActualParameters(), a2.getActualParameters());
    }

    public boolean checkCondition(
            List<Object> a1,
            List<Object> a2) {
        if (checkerMethod == null) {
            throw new IllegalStateException();
        }


        List<Object> actualParams = new ArrayList<>(a1);
        actualParams.addAll(a2);

        try {
            return (Boolean) getCheckerMethod().invoke(null, actualParams.toArray());
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new AssertionError();
        }
    }

    public static enum BoundType {
        JOIN, MEET;
    }
}
