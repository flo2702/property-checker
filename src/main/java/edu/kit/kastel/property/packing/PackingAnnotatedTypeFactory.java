package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.qual.Dependable;
import edu.kit.kastel.property.packing.qual.NonMonotonic;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeSubchecker;
import org.checkerframework.checker.initialization.InitializationAbstractAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationChecker;
import org.checkerframework.checker.initialization.InitializationFieldAccessTreeAnnotator;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.ClassName;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.IrrelevantTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.PropagationTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.QualifierKind;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;

public class PackingAnnotatedTypeFactory
        extends InitializationAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    public PackingAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected @Nullable PackingFieldAccessAnnotatedTypeFactory getFieldAccessFactory() {
        return getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }

    @Override
    public PackingChecker getChecker() {
        return (PackingChecker) super.getChecker();
    }

    @Override
    protected QualifierHierarchy createQualifierHierarchy() {
        return new PackingQualifierHierarchy();
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore initStore,
            CFAbstractStore<?, ?> targetStore,
            TreePath path, boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = getFieldAccessFactory().isComputingUninitializedFields();

        List<VariableElement> uninitializedFields = getUninitializedFieldsForTarget(initStore, targetStore, path, isStatic, receiverAnnotations);

        getFieldAccessFactory().setComputingUninitializedFields(wasComputingUninitializedFields);
        return uninitializedFields;
    }

    private List<VariableElement> getUninitializedFieldsForTarget(
            PackingStore initStore,
            CFAbstractStore<?, ?> targetStore,
            TreePath path,
            boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        List<VariableElement> uninitializedFields =
                getUninitializedFields(initStore, path, isStatic, receiverAnnotations);
        ClassTree currentClass = TreePathUtil.enclosingClass(path);

        GenericAnnotatedTypeFactory<?,?,?,?> factory;
        if (targetStore instanceof PackingClientStore) {
            factory = ((PackingClientStore) targetStore).getFactory();
        } else {
            // Must be NullnessNoInitStore
            factory = getTypeFactoryOfSubchecker(NullnessLatticeSubchecker.class);
        }

        if (factory == null) {
            throw new BugInCF(
                    "Did not find target type factory for checker "
                            + ((InitializationChecker) checker).getTargetCheckerClass());
        }

        // Remove primitives
        if (!((InitializationChecker) checker).checkPrimitives() || factory instanceof NullnessLatticeAnnotatedTypeFactory) {
            uninitializedFields.removeIf(var -> getAnnotatedType(var).getKind().isPrimitive());
        }

        // Filter out fields which are initialized according to subchecker
        uninitializedFields.removeIf(
                field -> {
                    AnnotatedTypeMirror declType = factory.getAnnotatedType(field);
                    AnnotatedTypeMirror refType = getRefinedTypeInCurrentClass(factory, targetStore, currentClass, field);

                    // MonotonicNonNull fields may be null
                    if (declType.hasAnnotation(MonotonicNonNull.class) && refType.hasAnnotation(Nullable.class)) {
                        return true;
                    }

                    return factory.getTypeHierarchy().isSubtype(refType, declType);
                });

        return uninitializedFields;
    }

    private static CFAbstractValue<?> getFieldValueInCurrentClass(CFAbstractStore<?, ?> store, ClassTree currentClass, VariableElement field) {
        JavaExpression receiver;
        if (ElementUtils.isStatic(field)) {
            receiver = new ClassName(((JCTree) currentClass).type);
        } else {
            receiver = new ThisReference(((JCTree) currentClass).type);
        }
        FieldAccess fa = new FieldAccess(receiver, field);
        return store.getFieldValue(fa);
    }

    static AnnotatedTypeMirror getRefinedTypeInCurrentClass(
            GenericAnnotatedTypeFactory<?,?,?,?> factory,
            @Nullable CFAbstractStore<?, ?> store,
            ClassTree currentClass,
            VariableElement field) {
        AnnotatedTypeMirror declType = factory.getAnnotatedType(field);
        AnnotatedTypeMirror refType = declType.deepCopy();
        CFAbstractValue<?> value = store == null ? null : getFieldValueInCurrentClass(store, currentClass, field);

        if (value != null) {
            refType.replaceAnnotations(value.getAnnotations());
        } else {
            // Exclusivity checker considers unassigned fields with default value null unique
            if (factory instanceof ExclusivityAnnotatedTypeFactory exclFactory) {
                refType.replaceAnnotations(List.of(exclFactory.UNIQUE));
            } else if (factory instanceof NullnessLatticeAnnotatedTypeFactory nullnessFactory && refType.getKind().isPrimitive()) {
                refType.replaceAnnotations(List.of(nullnessFactory.getNonNull()));
            } else {
                refType.replaceAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
            }
        }
        if (refType instanceof AnnotatedTypeMirror.AnnotatedDeclaredType) {
            ((AnnotatedTypeMirror.AnnotatedDeclaredType) refType).getTypeArguments().forEach(arg -> factory.addDefaultAnnotations(arg));
        }
        if (refType instanceof AnnotatedTypeMirror.AnnotatedArrayType) {
            factory.addDefaultAnnotations(((AnnotatedTypeMirror.AnnotatedArrayType) refType).getComponentType());
        }

        return refType;
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore store,
            TreePath path,
            boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = getFieldAccessFactory().isComputingUninitializedFields();
        getFieldAccessFactory().setComputingUninitializedFields(true);

        List<VariableElement> uninitializedFields = super.getUninitializedFields(store, path, isStatic, receiverAnnotations);

        getFieldAccessFactory().setComputingUninitializedFields(wasComputingUninitializedFields);
        return uninitializedFields;
    }

    @Override
    protected List<VariableElement> getPossiblyUninitializedFields(TreePath path) {
        ClassTree currentClass = TreePathUtil.enclosingClass(path);
        return ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(((JCTree) currentClass).type), elements);
    }

    @Override
    public AnnotationMirrorSet getExplicitNewClassAnnos(NewClassTree newClassTree) {
        // Return empty set so that the type visitor adds the annotation from the return type.
        return AnnotationMirrorSet.emptySet();
    }

    @Override
    protected void setSelfTypeInInitializationCode(
            Tree tree, AnnotatedTypeMirror.AnnotatedDeclaredType selfType, TreePath path) {
        MethodTree method = TreePathUtil.enclosingMethod(path);
        if (method == null || isMonotonicMethod(method)) {
            ClassTree enclosingClass = TreePathUtil.enclosingClass(path);
            Type classType = ((JCTree) enclosingClass).type;
            AnnotationMirror annotation;

            // If all fields are initialized-only, and they are all initialized,
            // then:
            //  - if the class is final, this is @Initialized
            //  - otherwise, this is @UnderInitialization(CurrentClass) as
            //    there might still be subclasses that need initialization.
            if (areAllFieldsInitializedOnly(enclosingClass)) {
                PackingStore initStore = getStoreBefore(tree);
                List<CFAbstractStore<?, ?>> targetStores = new ArrayList<>();
                for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
                    CFAbstractStore<?, ?> store = targetChecker.getTypeFactory().getStoreBefore(tree);
                    if (store != null) {
                        targetStores.add(store);
                    }
                }
                if (initStore != null && !targetStores.isEmpty()) {
                    if (classType.isFinal()) {
                        annotation = INITIALIZED;
                    } else {
                        annotation = createUnderInitializationAnnotation(classType);
                    }
                    for (CFAbstractStore<?, ?> store : targetStores) {
                        if (!getUninitializedFields(initStore, store, path, false, Collections.emptyList()).isEmpty()) {
                            annotation = null;
                            break;
                        }
                    }
                } else if (initStore != null && getUninitializedFields(initStore, path, false, Collections.emptyList()).isEmpty()) {
                    if (classType.isFinal()) {
                        annotation = INITIALIZED;
                    } else {
                        annotation = createUnderInitializationAnnotation(classType);
                    }
                } else {
                    annotation = null;
                }
            } else {
                annotation = null;
            }

            if (annotation == null) {
                annotation = getUnderInitializationAnnotationOfSuperType(classType);
            }
            selfType.replaceAnnotation(annotation);
        } else {
            //TODO do something more exact
            selfType.replaceAnnotation(createUnknownInitializationAnnotation(Object.class));
        }
    }

    @Override
    public @Nullable CFValue getInferredValueFor(Tree tree) {
        final PackingStore store = flowResult.getStoreBefore(tree);
        Set<Node> nodes = flowResult.getNodesForTree(tree);

        if (store == null || nodes == null) {
            return null;
        }

        return nodes.stream()
                .map(node -> {
                    JavaExpression expr;
                    if (node instanceof ValueLiteralNode
                            || node instanceof BinaryOperationNode
                            || node instanceof UnaryOperationNode) {
                        return analysis.createAbstractValue(AnnotationMirrorSet.singleton(INITIALIZED), node.getType());
                    } else if (node instanceof MethodInvocationNode) {
                        return store.getValue((MethodInvocationNode) node);
                    } else if (node instanceof FieldAccessNode) {
                        return store.getValue((FieldAccessNode) node);
                    } else if (node instanceof ArrayAccessNode) {
                        return store.getValue((ArrayAccessNode) node);
                    } else if (node instanceof LocalVariableNode) {
                        return store.getValue((LocalVariableNode) node);
                    } else if (node instanceof ThisNode) {
                        return store.getValue((ThisNode) node);
                    } else {
                        return null;  // No refined value available
                    }})
                .filter(Objects::nonNull)
                .reduce(CFValue::leastUpperBound)
                .orElse(null);
    }

    @Override
    protected void applyInferredAnnotations(AnnotatedTypeMirror type, CFValue inferred) {
        type.replaceAnnotations(inferred.getAnnotations());
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
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(2);
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this, false));
        treeAnnotators.add(getFieldAccessFactory().new PackingTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected TypeAnnotator createTypeAnnotator() {
        List<TypeAnnotator> typeAnnotators = new ArrayList<>(1);
        if (relevantJavaTypes != null) {
            typeAnnotators.add(new IrrelevantTypeAnnotator(this));
        }
        typeAnnotators.add(new PropagationTypeAnnotator(this));
        typeAnnotators.add(getFieldAccessFactory().new PackingTypeAnnotator(this));
        return new ListTypeAnnotator(typeAnnotators);
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

    public static boolean isDependableField(ExpressionTree tree) {
        return isDependableField(TreeUtils.elementFromUse(tree));
    }

    public static boolean isDependableField(Element el) {
        return AnnotationUtils.containsSameByClass(el.asType().getAnnotationMirrors(), Dependable.class);
    }

    public boolean isMonotonicMethod(MethodTree tree) {
        return isMonotonicMethod(TreeUtils.elementFromDeclaration(tree));
    }

    public boolean isMonotonicMethod(Element el) {
        return !AnnotationUtils.containsSameByClass(getDeclAnnotations(el), NonMonotonic.class);
    }

    protected class PackingQualifierHierarchy extends InitializationQualifierHierarchy {

        /** Qualifier kind for the @{@link UnknownInitialization} annotation. */
        private final QualifierKind UNKNOWN_INIT;

        /** Qualifier kind for the @{@link UnderInitialization} annotation. */
        private final QualifierKind UNDER_INIT;

        /** Create an InitializationQualifierHierarchy. */
        protected PackingQualifierHierarchy() {
            UNKNOWN_INIT = getQualifierKind(UNKNOWN_INITIALIZATION);
            UNDER_INIT = getQualifierKind(UNDER_INITALIZATION);
        }

        @Override
        public boolean isSubtypeWithElements(
                AnnotationMirror subAnno,
                QualifierKind subKind,
                AnnotationMirror superAnno,
                QualifierKind superKind) {
            if (!subKind.isSubtypeOf(superKind)) {
                return false;
            } else if ((subKind == UNDER_INIT && superKind == UNDER_INIT)) {
                // TODO: Is it a good idea to redefine UNDER_INIT as invariant?
                // Probably better to define our own annotations.
                return AnnotationUtils.areSame(subAnno, superAnno);
            } else if ((subKind == UNDER_INIT && superKind == UNKNOWN_INIT)
                    || (subKind == UNKNOWN_INIT && superKind == UNKNOWN_INIT)) {
                TypeMirror frame1 = getTypeFrameFromAnnotation(subAnno);
                TypeMirror frame2 = getTypeFrameFromAnnotation(superAnno);
                return types.isSubtype(frame1, frame2);
            } else {
                return true;
            }
        }

        @Override
        protected AnnotationMirror leastUpperBoundWithElements(
                AnnotationMirror anno1,
                QualifierKind qual1,
                AnnotationMirror anno2,
                QualifierKind qual2,
                QualifierKind lubKind) {
            // Handle the case where one is a subtype of the other.
            if (isSubtypeWithElements(anno1, qual1, anno2, qual2)) {
                return anno2;
            } else if (isSubtypeWithElements(anno2, qual2, anno1, qual1)) {
                return anno1;
            }
            boolean unknowninit1 = isUnknownInitialization(anno1);
            boolean unknowninit2 = isUnknownInitialization(anno2);
            boolean underinit1 = isUnderInitialization(anno1);
            boolean underinit2 = isUnderInitialization(anno2);

            // Handle @Initialized.
            if (isInitialized(anno1)) {
                assert underinit2;
                return createUnknownInitializationAnnotation(getTypeFrameFromAnnotation(anno2));
            } else if (isInitialized(anno2)) {
                assert underinit1;
                return createUnknownInitializationAnnotation(getTypeFrameFromAnnotation(anno1));
            }

            if (underinit1 && underinit2) {
                return createUnknownInitializationAnnotation(
                        lubTypeFrame(
                                getTypeFrameFromAnnotation(anno1),
                                getTypeFrameFromAnnotation(anno2)));
            }

            assert (unknowninit1 || underinit1) && (unknowninit2 || underinit2);
            return createUnknownInitializationAnnotation(
                    lubTypeFrame(
                            getTypeFrameFromAnnotation(anno1), getTypeFrameFromAnnotation(anno2)));
        }
    }
}
