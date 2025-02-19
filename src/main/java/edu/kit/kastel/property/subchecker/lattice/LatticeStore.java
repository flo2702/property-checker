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

import com.google.common.collect.Streams;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import org.apache.commons.lang3.tuple.Pair;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Stream;

public final class LatticeStore extends PackingClientStore<LatticeValue, LatticeStore> {

	private final TypeMirror stringType = ElementUtils.getTypeElement(analysis.getEnv(), String.class).asType();

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
		Tree currentTree = ((LatticeAnalysis) analysis).getLocalTree();
		if (currentTree instanceof VariableTree) {
			// we are in a variable declaration/assignment. No type can depend on an undeclared variable,
			// so there are no dependents up to this point.
			return;
		}

		if (dependency instanceof FieldAccess fieldAccess) {
			// FIXME: this analysis is not sufficient. We should clear all types that potentially contain an alias of
			//  *any* field that is reachable from dependency
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
		methodValues.entrySet().removeIf(isDependent);
		Optional.ofNullable(thisValue)
				// special case for non null annotations on `this` - they can never be invalidated
				.filter(val -> !val.toPropertyAnnotation().getAnnotationType().isNonNull())
				.filter(val -> isDependent.test(Map.entry(new ThisReference(val.getUnderlyingType()), val)))
				.ifPresent(val -> thisValue = createTopValue(val.getUnderlyingType()));


	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}


	/**
	 * Returns a stream of all the refinements that are currently in this store.
	 * They include
	 * <ul>
	 *     <li>local variable refinements</li>
	 *     <li>parameter refinements</li>
	 *     <li>field refinements</li>
	 *     <li>method return value refinements</li>
	 *     <li>refinement for the receiver ("this")</li>
	 * </ul>
	 *
	 * The collection only contains the refinements that can be parsed as JavaExpressions.
	 *
	 * @return collection of boolean java expressions.
	 */
	public Stream<JavaExpression> allRefinements() {
		return Streams.concat(
				fieldValues.entrySet().stream(),
				localVariableValues.entrySet().stream(),
				methodValues.entrySet().stream(),
				getThisValue().map(val -> Map.entry(new ThisReference(val.getUnderlyingType()), val)).stream()
		).flatMap(entry -> entry.getValue().getRefinement(entry.getKey()).stream());
	}

	public Optional<LatticeValue> getThisValue() {
		return Optional.ofNullable(thisValue);
	}

	@Override
	public void updateForMethodCall(
			MethodInvocationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		updateForInvocation((MethodCall) JavaExpression.fromNode(node), node, atypeFactory, val);
	}

	/**
	 * Same as {@link #updateForMethodCall(MethodInvocationNode, GenericAnnotatedTypeFactory, LatticeValue)},
	 * but for constructor ("new") calls. The rules for type invalidation are the same for constructors as they are
	 * for methods (we look for fields in references passed arguments that could have been changed).
	 *
	 * @param node ObjectCreationNode
	 * @param atypeFactory type factory
	 * @param val inferred return value of the constructor call
	 */
	public void updateForObjectCreation(
			ObjectCreationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		updateForInvocation(JavaExpressionUtil.constructorCall(node.getTree()), node, atypeFactory, val);
	}

	private void updateForInvocation(
			MethodCall invocation,
			Node node, // either a ObjectCreationNode or MethodInvocationNode
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		ExecutableElement method = invocation.getElement();

		if (atypeFactory.isSideEffectFree(method) && atypeFactory.isDeterministic(method)) {
			// insert return value into store if method is pure and not a constructor call (like this(...) or super(...))
			if (method.getKind() != ElementKind.CONSTRUCTOR || invocation.getReceiver() instanceof ClassName) {
				insertValue(invocation, val);
			}
			return;
		}

		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		PackingStore packingStoreAfter = packingFactory.getStoreAfter(node);

		AnnotatedTypeMirror.AnnotatedExecutableType exclType = exclFactory.getAnnotatedType(method);
		AnnotatedTypeMirror.AnnotatedExecutableType packingType = packingFactory.getAnnotatedType(method);



		if (!ElementUtils.isStatic(method) && method.getKind() != ElementKind.CONSTRUCTOR) {
			Node receiver = ((MethodInvocationNode) node).getTarget().getReceiver();
			// receivers of instance method calls could be modified by the method
			var exclReceiver = exclType.getReceiverType();
			var packingReceiver = packingType.getReceiverType();
			// TODO: before, we passed the local receiver packing type, not the declared one. is this important? why?
			updateForPassedReference(atypeFactory, receiver,
					exclReceiver, packingReceiver,
					packingStoreAfter);
		}

		// go through all the passed arguments, see which ones could have been modified
		List<Node> arguments = switch (node) {
			case MethodInvocationNode mi -> mi.getArguments();
			case ObjectCreationNode oc -> oc.getArguments();
			default -> throw new AssertionError();
		};

		for (int i = 0; i < arguments.size(); ++i) {
			// arguments of method/constructor calls could be modified by the implementation
			Node arg = arguments.get(i);
			AnnotatedTypeMirror declaredExclType = exclType.getParameterTypes().get(i);
			AnnotatedTypeMirror inputPackingType = packingType.getParameterTypes().get(i);

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
		if (reference instanceof ObjectCreationNode) {
			// reference is a constructor call. There can be no dependents on a value like new Foo().field
			// because every invocation of "new" causes the creation of an independent field.
			return;
		}

		if (reference.getType().getKind().isPrimitive()
				|| analysis.getTypes().isSameType(reference.getType(), stringType)) {
			// skip primitive and string types - they can't be modified
			// the reason we handle strings explicitly here is that they can also be literals,
			// and this store can't deal with literal values.
			return;
		}

		TypeMirror declaredType = declaredExclType.getUnderlyingType();
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);

		QualifierHierarchy exclHierarchy = exclFactory.getQualifierHierarchy();

		JavaExpression referenceExpr = JavaExpression.fromNode(reference);
		CFValue outputPackingValue = storeAfter.getValue(referenceExpr);
		AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(declaredType,
				packingFactory, false);
		if (outputPackingValue != null) {
			outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
		}

		var exclStore = exclFactory.getStoreBefore(reference);

		// (field owner, packing type of field owner)
		Deque<Pair<JavaExpression, AnnotatedTypeMirror>> contexts = new ArrayDeque<>();
		contexts.push(Pair.of(JavaExpression.fromNode(reference), inputPackingType));
		while (!contexts.isEmpty()) {
			var context = contexts.pop();
			var fieldOwner = context.getLeft();
			var packingType = context.getRight();
			var exclAnno = exclStore.deriveExclusivityValue(fieldOwner);
			if (!exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)) {
				// context is @ReadOnly, so none of its fields could have been modified
				continue;
			}

			// compute all fields (including nested fields) that could have been modified,
			// based on the uniqueness and packing information

			var modifiedFields = ElementUtils.getAllFieldsIn(
					TypesUtils.getTypeElement(fieldOwner.getType()), atypeFactory.getElementUtils())
					.stream()
					// final primitive fields cannot be reassigned, and they also have no fields that can be reassigned
					// so whatever their type and dependents' types were before, they stay the same.
					.filter(field -> ElementUtils.isFinal(field) && ElementUtils.getType(field).getKind().isPrimitive());

			if (AnnotationUtils.areSame(exclFactory.MAYBE_ALIASED, exclAnno)) {
				// for @MaybeAliased contexts, only the uncommitted fields could have been modified
				modifiedFields = modifiedFields.filter(field ->
						packingFactory.isInitializedForFrame(packingType, field.getEnclosingElement().asType()));
			}

			// Clear field values and their dependents if they were possibly changed (and if there is no cycle)
			modifiedFields.map(field -> new FieldAccess(fieldOwner, field))
					.filter(this::acyclic)
					.forEach(fieldAccess -> {
						contexts.push(Pair.of(fieldAccess, packingFactory.getAnnotatedType(fieldAccess.getField())));
						clearValue(fieldAccess);
						clearDependents(fieldAccess);
					});
		}

		// if the reference is `this`, add the declared types of all committed fields after the method call to store
		// (the method packing posttype guarantees that they have the declared property type)
		if (reference instanceof ThisNode && outputPackingValue != null) {
			var packingAnno = outputPackingType.getAnnotationInHierarchy(packingFactory.getUnknownInitialization());
			var frame = packingFactory.getTypeFrameFromAnnotation(packingAnno);
			var initializedFields = ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), atypeFactory.getElementUtils());
			for (var field : initializedFields) {
				AnnotatedTypeMirror adaptedType = atypeFactory.getAnnotatedType(field);
				var invocationTree = ((LatticeAnalysis) analysis).getLocalTree();
				// temporarily set analysis position to field so its refinement can be parsed at its declaration
				((LatticeAnalysis) analysis).setPosition(field);
				LatticeValue val = analysis.createAbstractValue(adaptedType);
				((LatticeAnalysis) analysis).setPosition(invocationTree);
				insertValue(new FieldAccess(referenceExpr, field), val);
			}

		}
	}

	private boolean acyclic(FieldAccess expr) {
		var accessedFields = Stream.iterate(expr,
						fa -> fa.getReceiver() instanceof FieldAccess,
						fa -> (FieldAccess) fa.getReceiver()
				)
				.map(FieldAccess::getField)
				.toList();
		return accessedFields.size() == Set.copyOf(accessedFields).size();
	}
}
