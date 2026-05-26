package edu.kit.kastel.property.subchecker.nullness;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import org.checkerframework.checker.nullness.NullnessNoInitAnalysis;
import org.checkerframework.checker.nullness.NullnessNoInitStore;
import org.checkerframework.checker.nullness.NullnessNoInitTransfer;
import org.checkerframework.checker.nullness.NullnessNoInitValue;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.AssignmentNode;
import org.checkerframework.dataflow.cfg.node.LocalVariableNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;

public class NullnessLatticeTransfer extends NullnessNoInitTransfer {

    public NullnessLatticeTransfer(NullnessNoInitAnalysis analysis) {
        super(analysis);
    }

    @Override
    public NullnessNoInitStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        ((NullnessLatticeAnalysis) analysis).setPosition(underlyingAST.getCode());
        NullnessNoInitStore initStore = super.initialStore(underlyingAST, parameters);

        if (underlyingAST.getKind() == UnderlyingAST.Kind.METHOD) {
            UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
            MethodTree methodDeclTree = method.getMethod();

            // The default implementation only adds fields declared in this class.
            // To make type-checking of pack statements more precise, we also add all fields declared in superclasses.
            ClassTree classTree = method.getClassTree();

            if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                        TypesUtils.getTypeElement(((JCTree) classTree).type),
                        nullnessTypeFactory.getElementUtils());
                AnnotatedTypeMirror receiverType =
                        nullnessTypeFactory.getSelfType(methodDeclTree.getBody());

                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        nullnessTypeFactory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                AnnotatedTypeMirror receiverPackingType =
                        packingFactory.getSelfType(methodDeclTree.getBody());

                for (VariableElement field : allFields) {
                    if (!ElementUtils.isStatic(field)) {
                        FieldAccess fieldAccess = new FieldAccess(new ThisReference(receiverType.getUnderlyingType()), field);
                        TypeMirror fieldOwnerType = field.getEnclosingElement().asType();
                        AnnotatedTypeMirror declaredType = nullnessTypeFactory.getAnnotatedType(field);

                        // Viewpoint-adapt type
                        AnnotatedTypeMirror adaptedType =
                                AnnotatedTypes.asMemberOf(
                                        analysis.getTypes(),
                                        analysis.getTypeFactory(),
                                        receiverType,
                                        field,
                                        declaredType);

                        if (adaptedType == null) {
                            adaptedType = declaredType;
                        }

                        // Use top annotation if receiver is not sufficiently packed
                        if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)
                                && !adaptedType.getKind().isPrimitive()) {
                            adaptedType.clearAnnotations();
                            adaptedType.addAnnotations(nullnessTypeFactory.getQualifierHierarchy().getTopAnnotations());
                        }

                        NullnessNoInitValue value = analysis.createAbstractValue(adaptedType);

                        initStore.insertValue(fieldAccess, value);
                    }
                }
            }
        }

        return initStore;
    }

    @Override
    public TransferResult<NullnessNoInitValue, NullnessNoInitStore> visitAssignment(AssignmentNode n, TransferInput<NullnessNoInitValue, NullnessNoInitStore> in) {
        ((NullnessLatticeAnalysis) analysis).setPosition(n.getTree());
        return super.visitAssignment(n, in);
    }

    @Override
    public TransferResult<NullnessNoInitValue, NullnessNoInitStore> visitMethodInvocation(MethodInvocationNode n, TransferInput<NullnessNoInitValue, NullnessNoInitStore> in) {
        ((NullnessLatticeAnalysis) analysis).setPosition(n.getTree());
        return super.visitMethodInvocation(n, in);
    }

    @Override
    public TransferResult<NullnessNoInitValue, NullnessNoInitStore> visitObjectCreation(ObjectCreationNode n, TransferInput<NullnessNoInitValue, NullnessNoInitStore> p) {
        ((NullnessLatticeAnalysis) analysis).setPosition(n.getTree());
        return super.visitObjectCreation(n, p);
    }
}
