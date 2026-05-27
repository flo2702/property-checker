package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.TargetType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import edu.kit.kastel.property.subchecker.lattice.CooperativeAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.lattice.CooperativeChecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.util.Assert;
import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.util.Pair;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.initialization.InitializationAbstractVisitor;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.*;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.NoType;
import javax.lang.model.type.TypeMirror;
import java.lang.annotation.Annotation;
import java.util.*;
import java.util.stream.Collectors;

public class PackingVisitor
        extends InitializationAbstractVisitor<CFValue, PackingStore, PackingTransfer, PackingAnalysis, PackingAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    private final ExecutableElement unchangedFieldMethod;
    private final ExecutableElement equalFieldMethod;

    private Set<JavaExpression> paramsInContract = new HashSet<>();
    private MethodTree enclMethod = null;

    public PackingVisitor(BaseTypeChecker checker) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
        unchangedFieldMethod = TreeUtils.getMethod(Assert.class, "immutableFieldUnchanged", 2, atypeFactory.getProcessingEnv());
        equalFieldMethod = TreeUtils.getMethod(Assert.class, "immutableFieldEqual", 4, atypeFactory.getProcessingEnv());
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        // Don't load the factory reflexively based on checker class name.
        // Instead, always use the PackingAnnotatedTypeFactory.
        return new PackingAnnotatedTypeFactory(checker);
    }

    public PackingChecker getChecker() {
        return (PackingChecker) checker;
    }

    @Override
    protected void reportCommonAssignmentError(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        // Primitives are always initialized
        if (varType.getKind().isPrimitive()) {
            return;
        }

        // Try to infer a packing statement to avoid the error
        if (valueTree.toString().equals("this")
                && canInferPackingStatement(
                        valueTree,
                        enclosingStatement(valueTree),
                        varType.getAnnotationInHierarchy(atypeFactory.getInitialized()),
                        valueType.getAnnotationInHierarchy(atypeFactory.getInitialized()))) {
            return;
        }

        super.reportCommonAssignmentError(varType, valueType, valueTree, "packing." + errorKey, extraArgs);
    }

    @Override
    protected void reportMethodInvocabilityError(
            MethodInvocationTree tree, AnnotatedTypeMirror found, AnnotatedTypeMirror expected) {
        ExpressionTree recv = tree.getMethodSelect();
        @SuppressWarnings("deprecation")
        Element element = TreeUtils.elementFromTree(tree);
        if (recv instanceof MemberSelectTree && ((MemberSelectTree) recv).getExpression().toString().equals("this")
                && canInferPackingStatement(
                ((MemberSelectTree) recv).getExpression(),
                tree,
                expected.getAnnotationInHierarchy(atypeFactory.getInitialized()),
                found.getAnnotationInHierarchy(atypeFactory.getInitialized()))) {
            return;
        } else if (ElementUtils.hasReceiver(element)) {
            // Implicit this
            if (canInferPackingStatement(
                    atypeFactory.getReceiverType(tree),
                    tree,
                    expected.getAnnotationInHierarchy(atypeFactory.getInitialized()),
                    found.getAnnotationInHierarchy(atypeFactory.getInitialized()))) {
                return;
            }
        }

       checker.reportError(
                tree,
                "packing.method.invocation.invalid",
                TreeUtils.elementFromUse(tree),
                found.toString(),
                expected.toString());
    }

    protected final boolean canInferPackingStatement(
            MethodTree methodTree,
            AnnotationMirror varAnno,
            AnnotationMirror valAnno) {
        VariableTree receiver = methodTree.getReceiverParameter();
        boolean unique = receiver != null && receiver.getModifiers().getAnnotations().stream().anyMatch(anno -> anno.toString().equals("@Unique"));
        Type classType = ((JCTree.JCMethodDecl) methodTree).sym.owner.type;
        TypeMirror varFrame;
        if (atypeFactory.isInitialized(varAnno)) {
            // If an object is initialized up to its most specific known subclass and no function with a receiver type
            // @UnderInitialization was called and no dependable field assigned, the object is @Initialized
            if (!classType.isFinal() && (atypeFactory.getRegularExitStore(methodTree).isHelperFunctionCalled() || atypeFactory.getRegularExitStore(methodTree).isDependableFieldAssigned())) {
                return false;
            }
            if (TreeUtils.isConstructor(methodTree)) {
                if (!classType.isFinal()) {
                    return false;
                }
                varFrame = classType;
            } else {
                if (!unique) {
                    return false;
                }
                varFrame = ((JCTree) receiver).type;
            }
        } else {
            varFrame = atypeFactory.getTypeFrameFromAnnotation(varAnno);
        }
        TypeMirror valFrame = atypeFactory.getTypeFrameFromAnnotation(valAnno);

        // Infer unpack statement if possible
        if (getChecker().shouldInferUnpack()
                && types.isSubtype(valFrame, varFrame) && !atypeFactory.isUnknownInitialization(valAnno)) {
            inferUnpackStatement(methodTree, varFrame);
            return true;
        }

        // Infer pack statement if possible
        if (varFrame.equals(valFrame) && ((Type) valFrame).isFinal()) {
            inferPackStatement(enclosingStatement(methodTree), varFrame);
            return true;
        }
        if (types.isSubtype(varFrame, valFrame)) {
            // For monotonic methods or unique receivers,
            // we may treat @UnknownInitialization(A) as equivalent to @UnderInitialization(A)
            boolean monotonic = atypeFactory.isMonotonicMethod(methodTree);
            if (!monotonic && !unique && atypeFactory.isUnknownInitialization(valAnno)) {
                return false;
            }

            checkFieldsInitializedUpToFrame(methodTree, varFrame);
            // checkFieldsInitializedUpToFrame reports an error if necessary.
            // We return true to not report another error.
            inferPackStatement(enclosingStatement(methodTree), varFrame);
            return true;
        }

        return false;
    }

    protected final boolean canInferPackingStatement(
            Tree varTree,
            Tree stmtTree,
            AnnotationMirror varAnno,
            AnnotationMirror valAnno) {
        return canInferPackingStatement(
                atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class).getAnnotatedType(varTree),
                stmtTree == null ? varTree : stmtTree, varAnno, valAnno);
    }

    protected final boolean canInferPackingStatement(
            AnnotatedTypeMirror type,
            Tree stmtTree,
            AnnotationMirror varAnno,
            AnnotationMirror valAnno) {
        TypeMirror varFrame;
        if (atypeFactory.isInitialized(varAnno)) {
            // If an object is initialized up to its most specific known subclass and no function with a receiver type
            // @UnderInitialization was called, the object is @Initialized
            if (atypeFactory.getStoreBefore(stmtTree).isHelperFunctionCalled()) {
                return false;
            }
            varFrame = type.getUnderlyingType();
        } else {
            varFrame = atypeFactory.getTypeFrameFromAnnotation(varAnno);
            boolean unique = type.hasAnnotation(Unique.class);
            if (!unique) {
                return false;
            }
        }
        TypeMirror valFrame = atypeFactory.getTypeFrameFromAnnotation(valAnno);

        // Infer unpack statement if possible
        if (getChecker().shouldInferUnpack()
                && types.isSubtype(valFrame, varFrame) && !atypeFactory.isUnknownInitialization(valAnno)) {
            inferUnpackStatement(stmtTree, varFrame);
            return true;
        }

        // Infer pack statement if possible
        if (varFrame.equals(valFrame) && ((Type) valFrame).isFinal()) {
            inferPackStatement(stmtTree, varFrame);
            return true;
        }
        if (types.isSubtype(varFrame, valFrame) && !atypeFactory.isUnknownInitialization(valAnno)) {
            checkFieldsInitializedUpToFrame(stmtTree, varFrame);
            // checkFieldsInitializedUpToFrame reports an error if necessary.
            // We return true to not report another error.
            inferPackStatement(stmtTree, varFrame);
            return true;
        }

        return false;
    }

    protected void inferUnpackStatement(Tree tree, TypeMirror frame) {}
    protected void inferPackStatement(Tree tree, TypeMirror frame) {}

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(node);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();

        if (enclMethod == null) {
            // Don't check implicit constructors
            return null;
        }

        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            ExpressionTree objToPack = node.getArguments().get(0);

            if (!objToPack.toString().equals("this")) {
                checker.reportError(node, "initialization.packing.nonreceiver");
                return null;
            }

            TypeElement typeElement = (TypeElement) TreeUtils.elementFromUse(((MemberSelectTree) node.getArguments().get(1)).getExpression());

            CFValue oldValue = atypeFactory.getStoreBefore(node).getValue((ThisNode) null);
            AnnotationMirror oldAnnotation;
            if (oldValue != null) {
                oldAnnotation = atypeFactory.getQualifierHierarchy().findAnnotationInHierarchy(
                        oldValue.getAnnotations(), atypeFactory.getUnknownInitialization());
            } else {
                oldAnnotation = atypeFactory.getAnnotatedType(objToPack).getAnnotationInHierarchy(atypeFactory.getUnknownInitialization());
            }

            TypeElement thisTypeElement = TreeUtils.elementFromDeclaration(TreePathUtil.enclosingClass(getCurrentPath()));
            TypeMirror oldTypeFrame = getTypeFrame(oldAnnotation, thisTypeElement);

            TypeMirror newTypeFrame;
            if (ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
                // Type-check unpack statement: cannot unpack UnknownInitialization
                if (AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getUnknownInitialization())) {
                    checker.reportError(node, "initialization.unpacking.unknown");
                } else {
                    // Type-check unpack statement: new type frame must be supertype of old type frame.
                    newTypeFrame = typeElement.getSuperclass();
                    if (newTypeFrame instanceof NoType) {
                        checker.reportError(node, "initialization.unpacking.object.class");
                    } else if (oldTypeFrame != null && (!types.isSubtype(oldTypeFrame, newTypeFrame) || types.isSameType(oldTypeFrame, newTypeFrame))) {
                        checker.reportError(node, "initialization.already.unpacked");
                    }
                }
            } else {
                // Type-check pack statement:
                // New type frame must be subtype of old type frame.
                newTypeFrame = types.getDeclaredType(typeElement);
                if (oldTypeFrame == null || (!types.isSubtype(newTypeFrame, oldTypeFrame) || types.isSameType(oldTypeFrame, newTypeFrame))) {
                    checker.reportError(node, "initialization.already.packed");
                }

                //All fields in new frame must be initialized.
                checkFieldsInitializedUpToFrame(node, newTypeFrame);
            }

            return null;
        } else if (ElementUtils.isMethod(invokedMethod, unchangedFieldMethod, env)) {
            JCTree.JCLiteral immutableObject = (JCTree.JCLiteral) node.getArguments().get(0);
            JCTree.JCLiteral unchangedField = (JCTree.JCLiteral) node.getArguments().get(1);
            // TODO!
            return null;
        } else if (ElementUtils.isMethod(invokedMethod, equalFieldMethod, env)) {
            JCTree.JCLiteral immutableObject0 = (JCTree.JCLiteral) node.getArguments().get(0);
            JCTree.JCLiteral immutableObject1 = (JCTree.JCLiteral) node.getArguments().get(1);
            JCTree.JCLiteral equalField0 = (JCTree.JCLiteral) node.getArguments().get(2);
            JCTree.JCLiteral equalField1 = (JCTree.JCLiteral) node.getArguments().get(3);
            // TODO!
            return null;
        } else if (atypeFactory.isMonotonicMethod(enclMethod)
                && !atypeFactory.isMonotonicMethod(invokedMethod) && !atypeFactory.isSideEffectFree(invokedMethod)) {
            checker.reportError(node, "initialization.nonmonotonic.method.call");
            return null;
        } else {
            return super.visitMethodInvocation(node, p);
        }
    }

    protected TypeMirror getTypeFrame(AnnotatedTypeMirror type) {
        var annotation = type.getAnnotationInHierarchy(atypeFactory.getUnknownInitialization());
        return getTypeFrame(annotation, TypesUtils.getTypeElement(type.getUnderlyingType()));
    }

    protected TypeMirror getTypeFrame(AnnotationMirror annotation, TypeElement typeElement) {
        if (AnnotationUtils.areSameByName(annotation, atypeFactory.getUnknownInitialization())
                || AnnotationUtils.areSameByName(annotation, atypeFactory.getUnderInitialization())) {
            return atypeFactory.getTypeFrameFromAnnotation(annotation);
        } else /*if (AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getInitialized()))*/ {
            return ElementUtils.isFinal(typeElement) ? typeElement.asType() : null;
        }
    }

    /**
     * Checks that all fields up to a given frame are initialized at a given statement.
     *
     * @param tree a statement
     * @param frame the type frame up to which the fields should be initialized
     */
    protected final void checkFieldsInitializedUpToFrame(
            Tree tree,
            TypeMirror frame) {
        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();
            this.checkFieldsInitializedUpToFrame(tree, targetChecker, atypeFactory.getStoreBefore(tree), targetFactory.getStoreBefore(tree), frame);
        }
    }

    /**
     * Checks that all fields up to a given frame are initialized at the end of a given method.
     *
     * @param methodTree a method
     * @param frame the type frame up to which the fields should be initialized
     */
    protected final void checkFieldsInitializedUpToFrame(
            MethodTree methodTree,
            TypeMirror frame) {
        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();
            this.checkFieldsInitializedUpToFrame(methodTree, targetChecker, atypeFactory.getRegularExitStore(methodTree), targetFactory.getRegularExitStore(methodTree), frame);
        }
    }

    private void checkFieldsInitializedUpToFrame(
            Tree tree,
            BaseTypeChecker targetChecker,
            PackingStore packingStore,
            CFAbstractStore<?, ?> targetStore,
            TypeMirror frame) {
        if (packingStore == null || targetStore == null) {
            return;
        }

        List<VariableElement> uninitializedFields =
                atypeFactory.getUninitializedFields(
                        packingStore,
                        targetStore,
                        getCurrentPath(),
                        false,
                        List.of());
        // Remove fields below frame
        uninitializedFields.retainAll(ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), elements));

        // Remove fields with a relevant @SuppressWarnings annotation
        uninitializedFields.removeIf(
                f -> checker.shouldSuppressWarnings(f, "initialization.field.uninitialized"));

        if (!uninitializedFields.isEmpty()) {
            reportUninitializedFieldsError(tree, targetChecker, uninitializedFields);
        }
    }

    protected void reportUninitializedFieldsError(Tree tree, BaseTypeChecker targetChecker, List<VariableElement> uninitializedFields) {
        StringJoiner fieldsString = new StringJoiner(", ");
        for (VariableElement f : uninitializedFields) {
            fieldsString.add(f.getSimpleName());
        }

        targetChecker.reportError(tree, "initialization.fields.uninitialized", fieldsString);
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        paramsInContract.add(expression);
        CFAbstractStore<?, ?> exitStore = atypeFactory.getRegularExitStore(methodTree);
        if (exitStore == null) {
            // If there is no regular exitStore, then the method cannot reach the regular exit and
            // there is no need to check anything.
        } else {
            CFAbstractValue<?> value = exitStore.getValue(expression);
            AnnotationMirror inferredAnno = null;
            if (value != null) {
                AnnotationMirrorSet annos = value.getAnnotations();
                inferredAnno = qualHierarchy.findAnnotationInSameHierarchy(annos, annotation);
            }
            if (!checkContract(expression, annotation, inferredAnno, exitStore)) {
                if (expression.toString().equals("this") && canInferPackingStatement(methodTree, annotation, inferredAnno)) {
                    return;
                }

                checker.reportError(
                        methodTree,
                        "packing.postcondition.not.satisfied",
                        methodTree.getName(),
                        contractExpressionAndType(expression.toString(), inferredAnno),
                        contractExpressionAndType(expression.toString(), annotation));
            }
        }
    }

    @Override
    public Void visitMethod(MethodTree tree, Void p) {
        MethodTree prevEnclMethod = enclMethod;
        enclMethod = tree;

        super.visitMethod(tree, p);

        // check that params not covered by explicit contract fulfill their input type
        VariableTree receiver = tree.getReceiverParameter();
        if (receiver != null) {
            checkDefaultContract(receiver, tree, atypeFactory.getRegularExitStore(tree));
        }
        for (VariableTree param : tree.getParameters()) {
            checkDefaultContract(param, tree, atypeFactory.getRegularExitStore(tree));
        }

        // Constructor receivers need special treatment: we can't get at the receiver from the method tree;
        // instead, we compare the this value in the constructor's exit store to the declared
        // constructor type.
        // Implicit default constructors are instead treated by ::checkConstructorResult
        PackingStore exitStore = atypeFactory.getRegularExitStore(tree);
        if (TreeUtils.isConstructor(tree) && !TreeUtils.isSynthetic(tree) && exitStore != null) {
            CFValue thisValue = exitStore.getValue((ThisNode) null);
            AnnotationMirror declared = getDeclaredConstructorResult(tree);
            AnnotationMirror top = qualHierarchy.getTopAnnotations().first();

            if (thisValue == null) {
                if (!AnnotationUtils.areSame(top, declared) && !canInferPackingStatement(tree, declared, top)) {
                    checker.reportError(tree, "initialization.constructor.return.type.incompatible", tree);
                }
            } else {
                AnnotationMirror actual = qualHierarchy.findAnnotationInHierarchy(
                        thisValue.getAnnotations(), atypeFactory.getUnknownInitialization());
                if (!qualHierarchy.isSubtypeQualifiersOnly(actual, declared) && !canInferPackingStatement(tree, declared, actual)) {
                    checker.reportError(tree, "initialization.constructor.return.type.incompatible", tree);
                }
            }
        }

        enclMethod = prevEnclMethod;
        return p;
    }

    protected AnnotationMirror getDeclaredConstructorResult(MethodTree tree) {
        Type classType = ((JCTree.JCMethodDecl) tree).sym.owner.type;
        AnnotationMirror declared;
        // Default declared type if no explicit annotation is given
        if (classType.isFinal()) {
            declared = atypeFactory.getInitialized();
        } else {
            declared =
                    atypeFactory.createUnderInitializationAnnotation(((JCTree.JCMethodDecl) tree).sym.owner.type);
        }
        for (AnnotationMirror anno : getConstructorAnnotations(tree)) {
            if (atypeFactory.isSupportedQualifier(anno)) {
                declared = anno;
                break;
            }
        }
        return declared;
    }

    private AnnotationMirrorSet getConstructorAnnotations(MethodTree tree) {
        if (TreeUtils.isConstructor(tree)) {
            com.sun.tools.javac.code.Symbol meth =
                    (com.sun.tools.javac.code.Symbol) TreeUtils.elementFromDeclaration(tree);
            return new AnnotationMirrorSet(
                    meth.getRawTypeAttributes().stream().filter(anno -> anno.position.type.equals(TargetType.METHOD_RETURN))
                            .collect(Collectors.toList()));
        }
        return AnnotationMirrorSet.emptySet();
    }

    @Override
    protected void checkConstructorResult(AnnotatedTypeMirror.AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // Explicit constructurs are treated the same as any other method by visitMethod;
        // so there's nothing to do here.
        // For default constructors, we use the superclass implementation check that every field is initialized.
        if (TreeUtils.isSynthetic(methodTree)) {
            super.checkConstructorResult(constructorType, constructorElement);
        }
    }

    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingStore exitStore) {
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(((JCTree) param).type);
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }
        if (!paramsInContract.contains(paramExpr)) {
            Element paramElem = TreeUtils.elementFromDeclaration(param);

            AnnotatedTypeMirror currentType = atypeFactory.getAnnotatedType(param);
            if (exitStore != null) {
                CFValue valueAfterMethod = exitStore.getValue(paramExpr);
                if (valueAfterMethod != null) {
                    currentType.replaceAnnotations(valueAfterMethod.getAnnotations());
                }
            }

            AnnotatedTypeMirror declType = atypeFactory.getAnnotatedTypeLhs(param);

            if (!typeHierarchy.isSubtype(currentType, declType) &&
                    !canInferPackingStatement(
                            methodTree,
                            declType.getAnnotationInHierarchy(atypeFactory.getInitialized()),
                            currentType.getAnnotationInHierarchy(atypeFactory.getInitialized()))) {
                checker.reportError(
                        methodTree,
                        "packing.postcondition.not.satisfied",
                        methodTree.getName(),
                        contractExpressionAndType(paramElem.toString(), currentType.getAnnotationInHierarchy(atypeFactory.getInitialized())),
                        contractExpressionAndType(paramElem.toString(), declType.getAnnotationInHierarchy(atypeFactory.getInitialized())));
            }
        }
    }

    @Override
    public Void visitAnnotation(AnnotationTree tree, Void p) {
        return null;
    }

    protected List<Pair<GenericAnnotatedTypeFactory<?,?,?,?>, String>> isPreservingAssignment(ExpressionTree lhs, ExpressionTree valueExp) {
        List<Pair<GenericAnnotatedTypeFactory<?,?,?,?>, String>> errors = new ArrayList<>();
        ClassTree currentClass = TreePathUtil.enclosingClass(getCurrentPath());

        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            String err = "assignment.type.incompatible";
            if (targetChecker instanceof CooperativeChecker coop) {
                err = coop.getLattice().getIdent() + "." + err;
            } else if (targetChecker instanceof ExclusivityChecker excl) {
                err = "exclusivity." + err;
            } else {
                throw new AssertionError();
            }
            GenericAnnotatedTypeFactory<?,?,?,?> factory = targetChecker.getTypeFactory();

            if (lhs instanceof MemberSelectTree && ((MemberSelectTree) lhs).getExpression().toString().equals("this")) {
                VariableElement field = (VariableElement) TreeUtils.elementFromUse(lhs);
                CFAbstractStore<?, ?> store = targetChecker.getTypeFactory().getStoreAfter(getCurrentPath().getLeaf());

                AnnotatedTypeMirror declType = factory.getAnnotatedType(field);
                AnnotatedTypeMirror refType = factory.getAnnotatedType(valueExp);
                // MonotonicNonNull fields may be null
                if (declType.hasAnnotation(MonotonicNonNull.class) && refType.hasAnnotation(Nullable.class)) {
                    break;
                }

                if (!factory.getTypeHierarchy().isSubtype(refType, declType)) {
                    if ((TypesUtils.isPrimitive(refType.getUnderlyingType()) || valueExp instanceof LiteralTree) && !(factory instanceof NullnessLatticeAnnotatedTypeFactory)) {
                        Lattice lattice = ((LatticeAnnotatedTypeFactory) factory).getLattice();
                        PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(declType);
                        EvaluatedPropertyAnnotation epa = lattice.getEvaluatedPropertyAnnotation(declType);

                        if (pa.getAnnotationType().isInv() && pa.getAnnotationType().isNonNull()) {
                            break;
                        } else if (epa != null && epa.isCheckable() && valueExp instanceof LiteralTree literal) {
                            PropertyAnnotationType pat = epa.getAnnotationType();

                            if (types.isSameType(refType.getUnderlyingType(), pat.getSubjectType()) && epa.checkProperty(literal.getValue())) {
                                break;
                            } else if (literal.getKind() == Tree.Kind.NULL_LITERAL && !pat.getSubjectType().getKind().isPrimitive() && epa.checkProperty(null)) {
                                break;
                            }
                        }
                    }

                    if (targetChecker instanceof LatticeSubchecker latticeSubchecker) {
                        latticeSubchecker.getVisitor()
                                .amendSmtResultForValue(declType, refType, lhs, false, getCurrentPath());
                    }

                    errors.add(Pair.of(factory, err));
                    break;
                }
            } else {
                // Assignment is to a field of another object
                AnnotatedTypeMirror lhsType = targetChecker.getTypeFactory().getAnnotatedTypeLhs(lhs);
                AnnotatedTypeMirror rhsType = targetChecker.getTypeFactory().getAnnotatedType(valueExp);
                if (!targetChecker.getTypeFactory().getTypeHierarchy().isSubtype(rhsType, lhsType)) {
                    if (targetChecker instanceof LatticeSubchecker latticeSubchecker) {
                        latticeSubchecker.getVisitor().amendSmtResultForValue(lhsType, rhsType, lhs, false);
                    }
                    errors.add(Pair.of(factory, err));
                    break;
                }
            }
        }

        return errors;
    }

    @Override
    protected boolean commonAssignmentCheck(Tree varTree, ExpressionTree valueExp, @CompilerMessageKey String errorKey, Object... extraArgs) {
        // field write of the form x.f = y
        if (TreeUtils.isFieldAccess(varTree)) {
            // cast is safe: a field access can only be an IdentifierTree or MemberSelectTree
            ExpressionTree lhs = (ExpressionTree) varTree;
            AnnotatedTypeMirror xType = atypeFactory.getReceiverType(lhs);

            if (PackingAnnotatedTypeFactory.isDependableField(lhs)) {
                if (lhs instanceof MemberSelectTree && !((MemberSelectTree) lhs).getExpression().toString().equals("this")) {
                    checker.reportError(varTree, "initialization.write.unowned.dependable.field");
                    return false;
                }

                if (xType == null || atypeFactory.isUnknownInitialization(xType) || atypeFactory.isInitializedForFrame(xType, TreeInfo.symbol((JCTree) varTree).owner.type)) {
                    checker.reportError(varTree, "initialization.write.committed.dependable.field", varTree);
                    return false;
                }
            }

            List<Pair<GenericAnnotatedTypeFactory<?,?,?,?>, String>> assignmentErrs = isPreservingAssignment(lhs, valueExp);

            if (assignmentErrs.isEmpty()) {
                return true;
            }

            if (lhs instanceof MemberSelectTree && !((MemberSelectTree) lhs).getExpression().toString().equals("this")) {
                assignmentErrs.forEach(err -> {
                    if (err.first instanceof CooperativeAnnotatedTypeFactory factory) {
                        factory.getChecker().getResult().illTypedAssignments.add((AssignmentTree) TreePathUtil.getAssignmentContext(getCurrentPath()));
                    }
                    checker.reportError(varTree, err.second);
                });
                assignmentErrs.forEach(err -> checker.reportError(varTree, err.second));
                return false;
            }

            if (enclMethod != null && atypeFactory.isMonotonicMethod(enclMethod)) {
                assignmentErrs.forEach(err -> checker.reportError(varTree, err.second));
                return false;
            }

            if (xType == null || atypeFactory.isUnknownInitialization(xType) || atypeFactory.isInitializedForFrame(xType, TreeInfo.symbol((JCTree) varTree).owner.type)) {
                assignmentErrs.forEach(err -> checker.reportError(varTree, err.second));
                return false;
            }
        }
        return super.commonAssignmentCheck(varTree, valueExp, errorKey, extraArgs);
    }

    protected boolean commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueExpTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        commonAssignmentCheckStartDiagnostic(varType, valueType, valueExpTree);

        AnnotatedTypeMirror widenedValueType = atypeFactory.getWidenedType(valueType, varType);
        boolean result = typeHierarchy.isSubtype(widenedValueType, varType);

        if (result) {
            for (Class<? extends Annotation> mono :
                    atypeFactory.getSupportedMonotonicTypeQualifiers()) {
                if (valueType.hasAnnotation(mono) && varType.hasAnnotation(mono)) {
                    checker.reportError(
                            valueExpTree,
                            "monotonic.type.incompatible",
                            mono.getSimpleName(),
                            mono.getSimpleName(),
                            valueType.toString());
                    result = false;
                }
            }
        } else {
            // `result` is false.
            // Use an error key only if it's overridden by a checker.
            reportCommonAssignmentError(
                    varType, widenedValueType, valueExpTree, errorKey, extraArgs);
        }

        commonAssignmentCheckEndDiagnostic(result, null, varType, valueType, valueExpTree);

        return result;
    }

    @Override
    public Void visitVariable(VariableTree tree, Void p) {
        //warnAboutTypeAnnotationsTooEarly(tree, tree.getModifiers());

        // VariableTree#getType returns null for binding variables from a DeconstructionPatternTree.
        if (tree.getType() != null) {
            visitAnnotatedType(tree.getModifiers().getAnnotations(), tree.getType());
        }

        AnnotatedTypeMirror variableType;
        if (getCurrentPath().getParentPath() != null
                && getCurrentPath().getParentPath().getLeaf().getKind()
                == Tree.Kind.LAMBDA_EXPRESSION) {
            // Calling getAnnotatedTypeLhs on a lambda parameter tree is possibly expensive
            // because caching is turned off.  This should be fixed by #979.
            // See https://github.com/typetools/checker-framework/issues/2853 for an example.
            variableType = atypeFactory.getAnnotatedType(tree);
        } else {
            variableType = atypeFactory.getAnnotatedTypeLhs(tree);
        }

        atypeFactory.getDependentTypesHelper().checkTypeForErrorExpressions(variableType, tree);
        Element varEle = TreeUtils.elementFromDeclaration(tree);
        if (varEle.getKind() == ElementKind.ENUM_CONSTANT) {
            commonAssignmentCheck(
                    tree, tree.getInitializer(), "enum.declaration.type.incompatible");
        } else if (tree.getInitializer() != null) {
            if (!TreeUtils.isVariableTreeDeclaredUsingVar(tree)) {
                // If there is no assignment in this variable declaration or it is declared using
                // `var`, skip it.
                // For a `var` declaration, TypeFromMemberVisitor#visitVariable already uses the
                // type of the initializer for the variable type, so it would be redundant to check
                // for compatibility here.
                commonAssignmentCheck(tree, tree.getInitializer(), "packing.assignment.type.incompatible");
            }
        } else {
            // commonAssignmentCheck validates the type of `tree`,
            // so only validate if commonAssignmentCheck wasn't called
            validateTypeOf(tree);
        }

        // @ReadOnly fields must not be @Initialized
        ExclusivityAnnotatedTypeFactory exclFactory = getChecker().getTypeFactoryOfSubcheckerOrNull(ExclusivityChecker.class);
        AnnotatedTypeMirror exclType = exclFactory.getAnnotatedTypeLhs(tree);
        AnnotationMirror annotation = Objects.requireNonNullElse(variableType.getAnnotationInHierarchy(atypeFactory.getInitialized()), atypeFactory.getInitialized());
        AnnotationMirror exclAnnotation = exclFactory.getExclusivityAnnotation(exclType);
        if ((!atypeFactory.isUnknownInitialization(annotation) || !atypeFactory.getTypeFrameFromAnnotation(annotation).toString().equals("java.lang.Object"))
                && !TreeUtils.isFieldAccess(tree)
                && (exclAnnotation == null || AnnotationUtils.areSame(exclAnnotation, exclFactory.READ_ONLY))) {
            checker.reportError(tree, "type.invalid.readonly.init");
        }

        validateVariablesTargetLocation(tree, variableType);
        warnRedundantAnnotations(tree, variableType);
        return super.visitVariable(tree, p);
    }

    @Override
    protected void checkFieldsInitialized(
            Tree tree, boolean staticFields, PackingStore initExitStore, List<? extends AnnotationMirror> receiverAnnotations) {
        if (staticFields || TreeUtils.isSynthetic((MethodTree) tree)) {
            // If the store is null, then the constructor cannot terminate successfully
            if (initExitStore == null) {
                return;
            }

            // Compact canonical record constructors do not generate visible assignments in the source,
            // but by definition they assign to all the record's fields so we don't need to
            // check for uninitialized fields in them:
            if (tree.getKind() == Tree.Kind.METHOD
                    && TreeUtils.isCompactCanonicalRecordConstructor((MethodTree) tree)) {
                return;
            }

            for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
                GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();
                // The target checker's store corresponding to initExitStore
                CFAbstractStore<?, ?> targetExitStore = targetFactory.getRegularExitStore(tree);

                if (targetExitStore == null) {
                    return;
                }

                List<VariableElement> uninitializedFields =
                        atypeFactory.getUninitializedFields(
                                initExitStore,
                                targetExitStore,
                                getCurrentPath(),
                                staticFields,
                                receiverAnnotations);
                uninitializedFields.removeAll(initializedFields);

                // The FBC behavior is generally unsound in the packing type system;
                // a field may be been assigned, but the rhs may violate the field's declared type.
                // But if a field has been initialized by an inline initializer, that assignment respects the field's
                // declared type.
                uninitializedFields.removeIf(f -> initExitStore.isFieldAssigned(f));

                // Static fields of superclasses are checked elsewhere. Remove them
                if (staticFields) {
                    uninitializedFields.removeIf(f -> !f.getEnclosingElement().equals(TreeUtils.elementFromTree(tree)));
                }

                // If we are checking initialization of a class's static fields or of a default constructor,
                // we issue an error for every uninitialized field at the respective field declaration.
                // If we are checking a non-default constructor, we issue a single error at the constructor
                // declaration.
                boolean errorAtField = staticFields || TreeUtils.isSynthetic((MethodTree) tree);

                String errorMsg =
                        (staticFields
                                ? "initialization.static.field.uninitialized"
                                : errorAtField
                                ? "initialization.field.uninitialized"
                                : "initialization.fields.uninitialized");

                // Remove fields with a relevant @SuppressWarnings annotation
                uninitializedFields.removeIf(f -> checker.shouldSuppressWarnings(f, errorMsg));

                if (!uninitializedFields.isEmpty()) {
                    if (errorAtField) {
                        // Issue each error at the relevant field
                        for (VariableElement f : uninitializedFields) {
                            targetChecker.reportError(f, errorMsg, f.getSimpleName());
                        }
                    } else {
                        // Issue all the errors at the relevant constructor
                        reportUninitializedFieldsError(tree, targetChecker, uninitializedFields);
                    }
                }
            }
        }
    }
}
