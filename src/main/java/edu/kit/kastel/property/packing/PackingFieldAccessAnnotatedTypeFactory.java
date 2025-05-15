package edu.kit.kastel.property.packing;

import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.qual.NonMonotonic;
import org.checkerframework.checker.initialization.InitializationFieldAccessAbstractAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationFieldAccessTreeAnnotator;
import org.checkerframework.checker.initialization.InitializationParentAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.IrrelevantTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.PropagationTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.DeclaredType;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class PackingFieldAccessAnnotatedTypeFactory
        extends InitializationFieldAccessAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    private boolean computingUninitializedFields = false;

    public PackingFieldAccessAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected PackingAnalysis createFlowAnalysis() {
        return new PackingAnalysis(checker, this);
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(2);
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(new PackingTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected TypeAnnotator createTypeAnnotator() {
        List<TypeAnnotator> typeAnnotators = new ArrayList<>(1);
        if (relevantJavaTypes != null) {
            typeAnnotators.add(new IrrelevantTypeAnnotator(this));
        }
        typeAnnotators.add(new PropagationTypeAnnotator(this));
        typeAnnotators.add(new PackingTypeAnnotator(this));
        return new ListTypeAnnotator(typeAnnotators);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(
            CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }

    public boolean isComputingUninitializedFields() {
        return computingUninitializedFields;
    }

    public void setComputingUninitializedFields(boolean computingUninitializedFields) {
        this.computingUninitializedFields = computingUninitializedFields;
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore store, TreePath path, boolean isStatic, Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = computingUninitializedFields;
        computingUninitializedFields = true;

        List<VariableElement> result = super.getUninitializedFields(store, path, isStatic, receiverAnnotations);

        computingUninitializedFields = wasComputingUninitializedFields;
        return result;
    }

    @Override
    public void postAsMemberOf(
            AnnotatedTypeMirror type, AnnotatedTypeMirror owner, Element element) {
        if (element.getKind().isField()) {
            Collection<? extends AnnotationMirror> declaredFieldAnnotations =
                    getDeclAnnotations(element);
            AnnotatedTypeMirror fieldAnnotations = getAnnotatedType(element);
            computeFieldAccessInitializationType(
                    type, declaredFieldAnnotations, owner, fieldAnnotations);
        }
    }

    /**
     * Adapts the initialization type of a field access (implicit or explicit) based on the receiver
     * type and the declared annotations for the field.
     *
     * <p>To adapt the type in the target checker's hierarchy, see the {@link
     * InitializationFieldAccessTreeAnnotator} instead.
     *
     * @param type type of the field access expression
     * @param declaredFieldAnnotations declared annotations on the field
     * @param receiverType inferred annotations of the receiver
     * @param fieldType inferred annotations of the field
     */
    private void computeFieldAccessInitializationType(
            AnnotatedTypeMirror type,
            Collection<? extends AnnotationMirror> declaredFieldAnnotations,
            AnnotatedTypeMirror receiverType,
            AnnotatedTypeMirror fieldType) {
        // Primitive values have no fields and are thus always @Initialized.
        if (TypesUtils.isPrimitive(type.getUnderlyingType())) {
            return;
        }
        // not necessary if there is an explicit UnknownInitialization
        // annotation on the field
        if (AnnotationUtils.containsSameByName(
                fieldType.getAnnotations(), UNKNOWN_INITIALIZATION)) {
            return;
        }
    }

    @Override
    public AnnotationMirrorSet getExplicitNewClassAnnos(NewClassTree newClassTree) {
        // Return empty set so that the type visitor adds the annotation from the return type.
        return AnnotationMirrorSet.emptySet();
    }

    public AnnotationMirror getInitialized() {
        return INITIALIZED;
    }

    public AnnotationMirror getUnknownInitialization() {
        return UNKNOWN_INITIALIZATION;
    }

    public AnnotationMirror getUnderInitialization() {
        return UNDER_INITALIZATION;
    }

    public AnnotationMirror getFBCBottom() {
        return FBCBOTTOM;
    }

    protected class PackingTreeAnnotator extends CommitmentTreeAnnotator {

        public PackingTreeAnnotator(
                InitializationParentAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> initializationAnnotatedTypeFactory) {
            super(initializationAnnotatedTypeFactory);
        }

        @Override
        public Void visitMethod(MethodTree tree, AnnotatedTypeMirror p) {
            if (TreeUtils.isConstructor(tree)) {
                assert p instanceof AnnotatedTypeMirror.AnnotatedExecutableType;
                AnnotatedTypeMirror.AnnotatedExecutableType exeType = (AnnotatedTypeMirror.AnnotatedExecutableType) p;
                DeclaredType underlyingType =
                        (DeclaredType) exeType.getReturnType().getUnderlyingType();
                AnnotationMirror a = getUnderInitializationAnnotationOfSuperType(underlyingType);
                exeType.getReturnType().addMissingAnnotation(a);
            }
            return null;
        }

        @Override
        public Void visitNewClass(NewClassTree tree, AnnotatedTypeMirror p) {
            // Replace @UnderInitialization(exactType) and @UnknownInitialization(exactType) by @Initialized
            Type type = ((JCTree) tree).type;
            AnnotationMirror underInit = createUnderInitializationAnnotation(type);
            AnnotationMirror unknownInit = createUnknownInitializationAnnotation(type);

            if (!p.hasAnnotationInHierarchy(underInit) || p.hasAnnotation(underInit) || p.hasAnnotation(unknownInit)) {
                p.replaceAnnotation(INITIALIZED);
            }

            if (TypesUtils.isAnonymous(type)) {
                //TODO fine for all current use cases, but generally unsound
                p.replaceAnnotation(INITIALIZED);
            }

            return null;
        }
    }

    public boolean isMonotonicMethod(MethodTree tree) {
        return isMonotonicMethod(TreeUtils.elementFromDeclaration(tree));
    }

    public boolean isMonotonicMethod(Element el) {
        return !AnnotationUtils.containsSameByClass(getDeclAnnotations(el), NonMonotonic.class);
    }

    protected class PackingTypeAnnotator extends CommitmentTypeAnnotator {

        public PackingTypeAnnotator(InitializationParentAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> atypeFactory) {
            super(atypeFactory);
        }

        @Override
        public Void visitExecutable(AnnotatedTypeMirror.AnnotatedExecutableType t, Void p) {
            Element elem = t.getElement();
            if (elem.getKind() == ElementKind.CONSTRUCTOR) {
                AnnotatedTypeMirror.AnnotatedDeclaredType returnType = (AnnotatedTypeMirror.AnnotatedDeclaredType) t.getReturnType();
                DeclaredType underlyingType = returnType.getUnderlyingType();
                if (ElementUtils.isFinal(underlyingType.asElement())) {
                    returnType.addMissingAnnotation(
                            getInitialized());
                } else {
                    returnType.addMissingAnnotation(
                            createUnderInitializationAnnotation(underlyingType));
                }
            }
            return p;
        }
    }
}
