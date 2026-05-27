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

import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;

public final class LatticeTransfer extends PackingClientTransfer<LatticeValue, LatticeStore, LatticeTransfer> {

    private final LatticeAnnotatedTypeFactory factory;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        this.factory = analysis.getTypeFactory();
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitAssignment(AssignmentNode n, TransferInput<LatticeValue, LatticeStore> in) {
        ((LatticeAnalysis) analysis).setPosition(n.getTree());
        if (n.isSynthetic() || !(n.getTarget() instanceof LocalVariableNode local)) {
            return super.visitAssignment(n, in);
        }
        var store = in.getRegularStore();
        // when a local variable is assigned to, we store its declared type, unless the right
        // hand side of the assignment evaluates to a more specific type.
        AnnotatedTypeMirror declaredType = factory.getAnnotatedType(local.getElement());
        LatticeValue inferredValue = in.getValueOfSubNode(n.getExpression());

        AnnotatedTypeMirror inferredType = AnnotatedTypeMirror.createType(declaredType.getUnderlyingType(), factory, false);
        if (inferredValue != null) {
            inferredType.addAnnotations(inferredValue.getAnnotations());
        }
        var newVal = inferredValue != null && factory.getTypeHierarchy().isSubtypeShallowEffective(inferredType, declaredType)
                ? inferredValue
                : analysis.createAbstractValue(declaredType);

        // this stores the type and invalidates all dependent types
        this.processCommonAssignment(in, n.getTarget(), n.getExpression(), store, newVal);
        return new RegularTransferResult<>(this.finishValue(newVal, store), store);
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitObjectCreation(ObjectCreationNode node, TransferInput<LatticeValue, LatticeStore> in) {
        // constructors can change their arguments like method calls
        NewClassTree newClassTree = node.getTree();
        ExecutableElement constructorElt = TreeUtils.getSuperConstructor(newClassTree);
        var store = in.getRegularStore();
        ((LatticeAnalysis) analysis).setPosition(newClassTree);
        LatticeValue val = getValueFromFactory(newClassTree, node);
        store.updateForObjectCreation(node, analysis.getTypeFactory(), val);
        this.processPostconditions(node, store, constructorElt, newClassTree);
        return super.visitObjectCreation(node, in);
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(MethodInvocationNode node, TransferInput<LatticeValue, LatticeStore> in) {
        ((LatticeAnalysis) analysis).setPosition(node.getTree());
        LatticeStore store = in.getRegularStore();
        MethodAccessNode target = node.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();

        var packingClass = ElementUtils.getTypeElement(factory.getProcessingEnv(), Packing.class);
        if (receiver instanceof ClassNameNode name && name.getElement() == packingClass) {
            var packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, analysis.getEnv());
            boolean isPackingCall = packMethod == method;
            if (isPackingCall) {
                // restore declared types up to specified frame after call to Packing.pack
                var packingReceiverType = node.getArgument(0).getType();
                var factory = getAnalysis().getTypeFactory();
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
                TypeMirror frame = ((FieldAccessNode) node.getArgument(1)).getReceiver().getType();
                AnnotationMirror initializedToFrameAnno = packingFactory.createUnderInitializationAnnotation(frame);
                AnnotatedTypeMirror packingType = AnnotatedTypeMirror.createType(packingReceiverType, packingFactory, false);
                packingType.addAnnotation(initializedToFrameAnno);
                insertFieldsUpToFrame(
                        store,
                        AnnotatedTypeMirror.createType(packingReceiverType, factory, false),
                        packingType,
                        false, false
                );
            }
            return new RegularTransferResult<>(null, store, isPackingCall);
        }

        return super.visitMethodInvocation(node, in);
    }

    @Override
    public LatticeValue moreSpecificValue(LatticeValue value1, LatticeValue value2) {
        return super.moreSpecificValue(value1, value2);
    }

    @Override
    protected TransferResult<LatticeValue, LatticeStore> strengthenAnnotationOfEqualTo(TransferResult<LatticeValue, LatticeStore> res, Node firstNode, Node secondNode, LatticeValue firstValue, LatticeValue secondValue, boolean notEqualTo) {
        // do nothing; we don't want insertValue to overwrite anything
        return res;
    }

    @Override
    protected void processCommonAssignment(TransferInput<LatticeValue, LatticeStore> in, Node lhs, Node rhs, LatticeStore store, LatticeValue rhsValue) {
        // If the rhs is a literal that is compatible with the lhs's declared type, put that type in the store.
        boolean compatible = false;
        AnnotatedTypeMirror lhsDeclType = factory.getAnnotatedTypeLhs(lhs.getTree());
        if (rhs.getTree() instanceof LiteralTree) {
            LiteralTree literal = (LiteralTree) rhs.getTree();
            Lattice lattice = factory.getLattice();
            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(lhsDeclType);
            EvaluatedPropertyAnnotation epa = lattice.getEvaluatedPropertyAnnotation(factory.getAnnotatedTypeLhs(lhs.getTree()));

            if (factory.getAnnotatedType(rhs.getTree()).getUnderlyingType().toString().equals("java.lang.String") && pa.getAnnotationType().isNonNull()) {
                compatible = true;
            } else if (epa != null) {
                PropertyAnnotationType pat = epa.getAnnotationType();

                if (pat.getSubjectType() != null) {
                    if (TypesUtils.areSamePrimitiveTypes(((JCTree) literal).type, pat.getSubjectType())) {
                        if (epa.checkProperty(literal.getValue())) {
                            compatible = true;
                        }
                    } else if (literal.getKind() == Tree.Kind.NULL_LITERAL && !TypesUtils.isPrimitive(pat.getSubjectType())) {
                        if (epa.checkProperty(null)) {
                            compatible = true;
                        }
                    }
                }
            }
        }

        if (compatible) {
            store.insertValue(JavaExpression.fromNode(lhs), new LatticeValue((LatticeAnalysis) analysis, lhsDeclType.getAnnotations(), lhsDeclType.getUnderlyingType()));
            return;
        }

        super.processCommonAssignment(in, lhs, rhs, store, rhsValue);
    }

    @Override
    protected boolean uncommitPrimitiveFields() {
        return true;
    }

    @Override
    protected LatticeValue initialThisValue(MethodTree methodDeclTree) {
        if (!TreeUtils.isConstructor(methodDeclTree)) {
            AnnotatedTypeMirror thisType = factory.getAnnotatedType(methodDeclTree.getReceiverParameter());
            return analysis.createSingleAnnotationValue(
                    thisType.getAnnotationInHierarchy(factory.getTop()),
                    thisType.getUnderlyingType());
        } else {
            AnnotatedTypeMirror thisType = factory.getSelfType(methodDeclTree.getBody());
            boolean isNonNull = factory.getLattice().getEffectivePropertyAnnotation(thisType).getAnnotationType().isNonNull();
            return analysis.createSingleAnnotationValue(
                    isNonNull ? thisType.getAnnotationInHierarchy(factory.getTop()) : factory.getTop(),
                    thisType.getUnderlyingType());
        }
    }
}
