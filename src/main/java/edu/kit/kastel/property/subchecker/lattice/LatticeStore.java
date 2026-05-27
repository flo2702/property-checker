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
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
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
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;
import java.util.function.Predicate;
import java.util.function.ToDoubleBiFunction;
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
			var exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory()
					.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
			// dependency on fields may be expressed through aliases of the field owner object.
			// the util method takes this into account when searching for dependencies.
			exprAnalyzer = expr -> JavaExpressionUtil.maybeDependent(expr, fieldAccess, currentTree, exclFactory);
		} else if (dependency instanceof ThisReference) {
			// Clear all fields for now. Committed fields get set to their declared type by
			// `updateCommittedFields` later.
		    fieldValues.clear();
			exprAnalyzer = expr -> expr.containsSyntacticEqualJavaExpression(dependency);
		} else {
			// then it's a local variable, and dependencies on local variables cannot
			// exist through a layer of aliases.
			exprAnalyzer = expr -> expr.containsSyntacticEqualJavaExpression(dependency);
		}

		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		// this predicate is a conservative _approximation_ for "does a given type depend on `dependency`"?
		// it will always return true if the refinement information is missing.
		Predicate<Map.Entry<? extends JavaExpression, LatticeValue>> isDependent =
				entry -> {
					if (entry.getKey().equals(dependency)) { // dependents don't include the value itself
						return false;
					}
					AnnotationMirrorSet annos = entry.getValue().getAnnotations();
					if (annos.isEmpty()) {
						return false;
					}
					EvaluatedPropertyAnnotation epa = factory.getLattice().getEvaluatedPropertyAnnotation(annos.first());
					if (epa != null && epa.isCheckable()) {
						// entry type is independent
						return false;
					}
					return entry.getValue().getRefinementParams(entry.getKey()).parallel().anyMatch(exprAnalyzer::test);
				};

		// We set local variable types to top if they're invalidated. If we removed them from the store,
		// the framework would incorrectly fall back to their declared type
		localVariableValues.entrySet().stream()
				.filter(isDependent)
				.forEach(entry -> entry.setValue(createTopValue(entry.getKey().getElement().asType())));
		fieldValues.entrySet().removeIf(isDependent);
		methodValues.entrySet().removeIf(isDependent);

		if (thisValue != null && dependency instanceof FieldAccess && !thisValue.getPropertyAnnotation().getAnnotationType().isNonNull()) {
			thisValue = createTopValue(thisValue.getUnderlyingType());
		}
	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}


	/**
	 * Returns a stream of all the refinements that are currently in this store (the "local refinement context).
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
				getThisValueOptional().map(val -> Map.entry(new ThisReference(val.getUnderlyingType()), val)).stream()
		).flatMap(entry -> entry.getValue().getRefinement(entry.getKey()).stream());
	}

	public Optional<LatticeValue> getThisValueOptional() {
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

		for (var expr : changedExprs(invocation, node, atypeFactory)) {
			clearValue(expr);
			clearDependents(expr);
		}

		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		PackingStore packingStoreAfter = packingFactory.getStoreAfter(node);

		updateCommittedFields(invocation, packingStoreAfter, packingFactory);
	}

	public List<JavaExpression> changedExprs(
			MethodCall invocation,
			Node node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory
	) {
		ExecutableElement method = invocation.getElement();

		if (atypeFactory.isSideEffectFree(method)) {
			// no field can be modified if method is side effect free
			return List.of();
		}

		List<JavaExpression> result = new ArrayList<>();

		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

        AnnotatedTypeMirror.AnnotatedExecutableType exclType = exclFactory.getAnnotatedType(method);
		AnnotatedTypeMirror.AnnotatedExecutableType packingType = packingFactory.getAnnotatedType(method);

		if (!ElementUtils.isStatic(method) && method.getKind() != ElementKind.CONSTRUCTOR) {
			Node receiver = ((MethodInvocationNode) node).getTarget().getReceiver();
			// receivers of instance method calls could be modified by the method
            var packingReceiver = packingType.getReceiverType();
			var exclReceiver = exclType.getReceiverType();
			if (exclReceiver.hasEffectiveAnnotation(exclFactory.UNIQUE)) {
				result.add(JavaExpression.fromNode(receiver));
			}
		}

		// go through all the passed arguments, see which ones could have been modified
		List<Node> arguments = switch (node) {
			case MethodInvocationNode mi -> mi.getArguments();
			case ObjectCreationNode oc -> oc.getArguments();
			default -> throw new AssertionError();
		};

		// add all unique arguments except constructor calls & primitive or string types;
		// see also implementation of changedExprs below
		for (int i = 0; i < arguments.size(); ++i) {
			Node arg = arguments.get(i);
			if ((arg instanceof ObjectCreationNode)
					|| arg.getType().getKind().isPrimitive() || analysis.getTypes().isSameType(arg.getType(), stringType)) {
				continue;
			}

			var inputExclType = exclType.getParameterTypes().get(i);

			// dependable committed fields of aliased args cannot be mutated, so we only consider unique fields
			if (!inputExclType.hasEffectiveAnnotation(exclFactory.UNIQUE)) {
				continue;
			}

			result.add(JavaExpression.fromNode(arg));
		}

		return result;
	}

	private void updateCommittedFields(
			MethodCall invocation,
			PackingStore storeAfter,
			PackingFieldAccessAnnotatedTypeFactory packingFactory
	) {
		// update the type of the fields in `this` after a method or constructor call,
		// based on the packing type of `this` after the method call
		boolean thisPassed = Stream.concat(Stream.of(invocation.getReceiver()), invocation.getArguments().stream())
				.anyMatch(val -> val instanceof ThisReference);
		if (!thisPassed) {
			return;
		}

		CFValue outputPackingValue = storeAfter.getValue((ThisNode) null);

		if (outputPackingValue != null) {
			TypeMirror thisType = outputPackingValue.getUnderlyingType();
			AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(thisType, packingFactory, false);
			outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
			var packingAnno = outputPackingType.getAnnotationInHierarchy(packingFactory.getUnknownInitialization());

			TypeMirror frame;
			if (packingFactory.isInitialized(packingAnno)) {
				frame = thisType;
			} else {
				frame = packingFactory.getTypeFrameFromAnnotation(packingAnno);
			}
			
			var initializedFields = ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), packingFactory.getElementUtils());
			for (var field : initializedFields) {
				AnnotatedTypeMirror adaptedType = analysis.getTypeFactory().getAnnotatedType(field);
				var invocationTree = ((LatticeAnalysis) analysis).getLocalTree();
				// temporarily set analysis position to field so its refinement can be parsed at its declaration
				((LatticeAnalysis) analysis).setPosition(field);
				LatticeValue val = analysis.createAbstractValue(adaptedType);
				((LatticeAnalysis) analysis).setPosition(invocationTree);
				insertValue(new FieldAccess(new ThisReference(thisType), field), val);
			}
		}
	}
}
