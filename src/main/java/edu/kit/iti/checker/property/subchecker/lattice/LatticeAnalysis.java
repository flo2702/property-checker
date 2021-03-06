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
package edu.kit.iti.checker.property.subchecker.lattice;

import java.util.List;
import java.util.Set;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.Pair;

public class LatticeAnalysis extends CFAbstractAnalysis<LatticeValue, LatticeStore, LatticeTransfer> {

    public LatticeAnalysis(
            BaseTypeChecker checker,
            LatticeAnnotatedTypeFactory factory,
            List<Pair<VariableElement, LatticeValue>> fieldValues) {
        super(checker, factory, fieldValues);
    }

    @Override
    public LatticeStore createEmptyStore(boolean sequentialSemantics) {
        return new LatticeStore(this, sequentialSemantics);
    }
    
    @Override
    public @Nullable LatticeValue createAbstractValue(Set<AnnotationMirror> annotations,
            TypeMirror underlyingType) {
        if (!CFAbstractValue.validateSet(annotations, underlyingType, qualifierHierarchy)) {
            return null;
        }
        return new LatticeValue(this, annotations, underlyingType);
    }

	@Override
	public LatticeStore createCopiedStore(LatticeStore s) {
		return new LatticeStore(s);
	}
}
