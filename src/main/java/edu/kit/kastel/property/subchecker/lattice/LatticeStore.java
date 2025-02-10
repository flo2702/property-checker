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

import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public final class LatticeStore extends PackingClientStore<LatticeValue, LatticeStore> {

    public LatticeStore(CFAbstractAnalysis<LatticeValue, LatticeStore, ?> analysis, boolean sequentialSemantics) {
		super(analysis, sequentialSemantics);
	}

	public LatticeStore(LatticeStore other) {
		super(other);
	}

	@Override
	protected void removeConflicting(ArrayAccess arrayAccess, @Nullable LatticeValue val) {
		clearDependents(arrayAccess.getArray());
	}

	@Override
	protected void removeConflicting(FieldAccess fieldAccess, @Nullable LatticeValue val) {
        clearDependents(fieldAccess);
	}

	@Override
	protected void removeConflicting(LocalVariable var) {
        clearDependents(var);
	}

	private void clearDependents(JavaExpression dependency) {
		Predicate<JavaExpression> exprAnalyzer;
		Tree currentTree = ((LatticeAnalysis) analysis).getPosition();
		if (currentTree instanceof VariableTree) {
			// we are in a variable declaration/assignment. No type can depend on an undeclared variable,
			// so there are no dependents up to this point.
			return;
		}

		if (dependency instanceof FieldAccess fieldAccess) {
			var exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory()
					.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
			// dependency on fields may be expressed through aliases of the field owner object.
			// the util method takes this into account when searching for dependencies.
			exprAnalyzer = expr -> JavaExpressionUtil.maybeDependent(expr, fieldAccess, currentTree, exclFactory);
		} else {
			// if it's not a field access, it's a local variable, and dependencies on local variables cannot
			// exist through a layer of aliases.
			exprAnalyzer = expr -> expr.containsSyntacticEqualJavaExpression(dependency);
		}

		// this predicate is a conservative _approximation_ for "does a given type depend on `dependency`"?
		// it will always return true if the refinement information is missing.
		Predicate<Map.Entry<? extends JavaExpression, LatticeValue>> isDependent =
				entry -> entry.getValue().getRefinement(entry.getKey()).map(exprAnalyzer::test).orElse(true);

		// TODO: why do we set local variables to top type, but remove field values?
		localVariableValues.entrySet().stream()
				.filter(isDependent)
				.forEach(entry -> entry.setValue(createTopValue(entry.getKey().getElement().asType())));
		fieldValues.entrySet().removeIf(isDependent);
		Optional.ofNullable(thisValue)
				// special case for non null annotations on `this` - they can never be invalidated
				.filter(val -> !val.toPropertyAnnotation().getAnnotationType().isNonNull())
				.filter(val -> isDependent.test(Map.entry(new ThisReference(val.getUnderlyingType()), val)))
				.ifPresent(val -> thisValue = createTopValue(val.getUnderlyingType()));
	}

	private static boolean isDependent(Predicate<JavaExpression> exprAnalyzer) {
		return false;
	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}

	/**
	 * Returns the collection of "local refinements" that are currently in this store.
	 * They include
	 * <ul>
	 *     <li>local variable refinements</li>
	 *     <li>parameter refinements</li>
	 *     <li>refinement for the receiver ("this")</li>
	 * </ul>
	 *
	 * The collection only contains the refinements that can be parsed as JavaExpressions.
	 *
	 * @return collection of boolean java expressions.
	 */
	public Collection<JavaExpression> getLocalRefinements() {
		var list = localVariableValues.entrySet().stream()
				.flatMap(entry -> entry.getValue().getRefinement(entry.getKey()).stream())
				.collect(Collectors.toCollection(ArrayList::new));
		if (thisValue != null) {
			thisValue.getRefinement(new ThisReference(thisValue.getUnderlyingType())).ifPresent(list::add);
		}
		return list;
	}

	@Override
	public void updateForMethodCall(
			MethodInvocationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val) {

		if (atypeFactory.isSideEffectFree(node.getTarget().getMethod())) {
			return;
		}

		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		PackingStore packingStoreAfter = packingFactory.getStoreAfter(node);
		ExecutableElement method = node.getTarget().getMethod();
		AnnotatedTypeMirror.AnnotatedExecutableType exclType = exclFactory.getAnnotatedType(method);
		AnnotatedTypeMirror.AnnotatedExecutableType packingType = packingFactory.getAnnotatedType(method);
		Node receiver = node.getTarget().getReceiver();

		if (!ElementUtils.isStatic(method)) {
			// TODO: before, we passed the local receiver packing type, not the declared one. is this important? why?
			updateForPassedReference(atypeFactory, receiver,
					exclType.getReceiverType(), packingType.getReceiverType(),
					packingStoreAfter);
		}

		TypeMirror stringType = ElementUtils.getTypeElement(atypeFactory.getProcessingEnv(), String.class).asType();

		for (int i = 0; i < node.getArguments().size(); ++i) {
			Node arg = node.getArgument(i);
			AnnotatedTypeMirror declaredExclType = exclType.getParameterTypes().get(i);
			AnnotatedTypeMirror inputPackingType = packingType.getParameterTypes().get(i);
			TypeMirror underlyingType = declaredExclType.getUnderlyingType();
			// skip primitive and string types - they can't be modified
			// the reason we handle strings explicitly here is that they can also be literals,
			// and this store can't deal with literal values.
			if (underlyingType.getKind().isPrimitive()
					|| analysis.getTypes().isSameType(underlyingType, stringType)) {
				continue;
			}
			updateForPassedReference(atypeFactory, arg,
					declaredExclType, inputPackingType,
					packingStoreAfter);
		}
	}

	private void updateForPassedReference(
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			Node reference,
			AnnotatedTypeMirror declaredExclType,
			AnnotatedTypeMirror inputPackingType,
			PackingStore storeAfter
	) {
		TypeMirror underlyingType = declaredExclType.getUnderlyingType();
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);

		// Clear field values if they were possibly changed
		QualifierHierarchy exclHierarchy = exclFactory.getQualifierHierarchy();
		AnnotationMirror exclAnno = declaredExclType.getAnnotationInHierarchy(exclFactory.READ_ONLY);
		if (!exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)) {
			return;
		}

		JavaExpression owner = JavaExpression.fromNode(reference);
		CFValue outputPackingValue = storeAfter.getValue(owner);
		AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(underlyingType,
				packingFactory, false);
		if (outputPackingValue != null) {
			outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
		}

		List<VariableElement> fields = ElementUtils.getAllFieldsIn(
				TypesUtils.getTypeElement(underlyingType), atypeFactory.getElementUtils());
		for (VariableElement field : fields) {
			TypeMirror fieldOwnerType = field.getEnclosingElement().asType();

			// Don't clear fields in frame of UnknownInit input type // TODO: why not? (because packed state is unknown?)
//			if (inputPackingType.hasAnnotation(UnknownInitialization.class) &&
//					packingFactory.isInitializedForFrame(inputPackingType, fieldOwnerType)) {
//				continue;
//			}

			if (ElementUtils.isFinal(field) && ElementUtils.getType(field).getKind().isPrimitive()) {
				// final primitive fields cannot be reassigned, and they also have no fields that can be reassigned
				// so whatever their type and dependents' types were before, they stay the same.
				continue;
			}

            FieldAccess fieldAccess = new FieldAccess(owner, field);
			clearValue(fieldAccess);

			if (exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.UNIQUE)
					|| (exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)
					&& packingFactory.isInitializedForFrame(inputPackingType, fieldOwnerType))) {
				// two options to get here:
				// a) field is behind a unique reference -> can be changed
				// b) field is below packing frame of a maybe aliased reference -> can be changed
				clearDependents(fieldAccess);
			}

			// add declared type of field to store if
			// - field is part of `this` (we currently only track such fields)
			// - `this` has packed state after method
			// - field is committed after method
			if (reference instanceof ThisNode
					&& outputPackingValue != null
					&& packingFactory.isInitializedForFrame(outputPackingType, fieldOwnerType)) {
				AnnotatedTypeMirror adaptedType = atypeFactory.getAnnotatedType(field);
				((LatticeAnalysis) analysis).setPosition(atypeFactory.declarationFromElement(field));
				LatticeValue val = analysis.createAbstractValue(adaptedType);
				insertValue(fieldAccess, val);
            }
		}
	}
}
