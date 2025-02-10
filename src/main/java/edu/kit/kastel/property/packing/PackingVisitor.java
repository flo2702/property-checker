package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.TargetType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeInfo;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.Assert;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.initialization.InitializationAbstractVisitor;
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
import java.util.*;
import java.util.stream.Collectors;

public class PackingVisitor
        extends InitializationAbstractVisitor<CFValue, PackingStore, PackingTransfer, PackingAnalysis, PackingAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    private final ExecutableElement unchangedFieldMethod;
    private final ExecutableElement equalFieldMethod;

    private Set<JavaExpression> paramsInContract = new HashSet<>();

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
        super.reportCommonAssignmentError(varType, valueType, valueTree, "packing." + errorKey, extraArgs);
    }

    @Override
    protected void reportMethodInvocabilityError(
            MethodInvocationTree tree, AnnotatedTypeMirror found, AnnotatedTypeMirror expected) {
        checker.reportError(
                tree,
                "packing.method.invocation.invalid",
                TreeUtils.elementFromUse(tree),
                found.toString(),
                expected.toString());
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(node);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();

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
                // Type-check unpack statement: new type frame must be supertype of old type frame.
                newTypeFrame = typeElement.getSuperclass();
                if (newTypeFrame instanceof NoType) {
                    checker.reportError(node, "initialization.unpacking.object.class");
                } else if (oldTypeFrame != null && (!types.isSubtype(oldTypeFrame, newTypeFrame) || types.isSameType(oldTypeFrame, newTypeFrame))) {
                    checker.reportError(node, "initialization.already.unpacked");
                }

                // Type-check unpack statement: cannot unpack UnknownInitialization
                if (AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getUnknownInitialization())) {
                    checker.reportError(node, "initialization.unpacking.unknown");
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
        } else if (ElementUtils.isMethod(invokedMethod, unchangedFieldMethod, env) || ElementUtils.isMethod(invokedMethod, equalFieldMethod, env)) {
            // TODO!
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
     * Checks that all fields up to a given frame are initialized at a given pack statement.
     *
     * @param tree a pack statement
     * @param frame the type frame up to which the fields should be initialized
     */
    protected void checkFieldsInitializedUpToFrame(
            Tree tree,
            TypeMirror frame) {
        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();

            List<VariableElement> uninitializedFields =
                    atypeFactory.getUninitializedFields(
                            atypeFactory.getStoreBefore(tree),
                            targetFactory.getStoreBefore(tree),
                            getCurrentPath(),
                            false,
                            List.of());

            // Remove fields below frame
            uninitializedFields.retainAll(ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), elements));

            // Remove fields with a relevant @SuppressWarnings annotation
            uninitializedFields.removeIf(
                    f -> checker.shouldSuppressWarnings(f, "initialization.field.uninitialized"));

            if (!uninitializedFields.isEmpty()) {
                StringJoiner fieldsString = new StringJoiner(", ");
                for (VariableElement f : uninitializedFields) {
                    fieldsString.add(f.getSimpleName());
                }
                checker.reportError(tree, "initialization.fields.uninitialized", fieldsString);
            }
        }
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
        // FIXME: packing.return.type.incompatible for IntInitTest
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
        if (TreeUtils.isConstructor(tree) && ! TreeUtils.isSynthetic(tree)) {
            CFValue thisValue = atypeFactory.getRegularExitStore(tree).getValue((ThisNode) null);
            AnnotationMirror declared = getDeclaredConstructorResult(tree);
            AnnotationMirror top = qualHierarchy.getTopAnnotations().first();

            if (thisValue == null) {
                if (!AnnotationUtils.areSame(top, declared)) {
                    checker.reportError(tree, "initialization.constructor.return.type.incompatible", tree);
                }
            } else {
                AnnotationMirror actual = qualHierarchy.findAnnotationInHierarchy(
                        thisValue.getAnnotations(), atypeFactory.getUnknownInitialization());
                if (!qualHierarchy.isSubtypeQualifiersOnly(actual, declared)) {
                    checker.reportError(tree, "initialization.constructor.return.type.incompatible", tree);
                }
            }
        }

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

            if (!typeHierarchy.isSubtype(currentType, declType)) {
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

    @Override
    protected boolean commonAssignmentCheck(Tree varTree, ExpressionTree valueExp, @CompilerMessageKey String errorKey, Object... extraArgs) {
        // field write of the form x.f = y
        if (TreeUtils.isFieldAccess(varTree)) {
            // cast is safe: a field access can only be an IdentifierTree or MemberSelectTree
            ExpressionTree lhs = (ExpressionTree) varTree;
            ExpressionTree y = valueExp;
            VariableElement el = TreeUtils.variableElementFromUse(lhs);
            AnnotatedTypeMirror xType = atypeFactory.getReceiverType(lhs);
            AnnotatedTypeMirror yType = atypeFactory.getAnnotatedType(y);
            // the special FBC rules do not apply if there is an explicit
            // UnknownInitialization annotation
            AnnotationMirrorSet fieldAnnotations =
                    atypeFactory.getAnnotatedType(el).getAnnotations();
            if (atypeFactory.isInitializedForFrame(xType, TreeInfo.symbol((JCTree) varTree).owner.type)) {
                checker.reportError(varTree, "initialization.write.committed.field", varTree);
                return false;
            }
        }
        return super.commonAssignmentCheck(varTree, valueExp, errorKey, extraArgs);
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
                commonAssignmentCheck(tree, tree.getInitializer(), "assignment.type.incompatible");
            }
        } else {
            // commonAssignmentCheck validates the type of `tree`,
            // so only validate if commonAssignmentCheck wasn't called
            validateTypeOf(tree);
        }

        // @ReadOnly vars must not be @Initialized
        ExclusivityAnnotatedTypeFactory exclFactory = getChecker().getTypeFactoryOfSubcheckerOrNull(ExclusivityChecker.class);
        AnnotatedTypeMirror exclType = exclFactory.getAnnotatedTypeLhs(tree);
        AnnotationMirror annotation = variableType.getAnnotationInHierarchy(atypeFactory.getInitialized());
        AnnotationMirror exclAnnotation = exclType.getAnnotationInHierarchy(exclFactory.READ_ONLY);
        if ((!atypeFactory.isUnknownInitialization(annotation) || !atypeFactory.getTypeFrameFromAnnotation(annotation).toString().equals("java.lang.Object"))
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
        // TODO: For now, the packing checker only changes a reference's type for explicit (un-)pack statements,
        // the only exception being default constructors.
        // When implementing other kinds of implicit (un-)packing, change this override.

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
                List<VariableElement> uninitializedFields =
                        atypeFactory.getUninitializedFields(
                                initExitStore,
                                targetExitStore,
                                getCurrentPath(),
                                staticFields,
                                receiverAnnotations);
                uninitializedFields.removeAll(initializedFields);

                // The FBC behavior because it's generally unsound in the packing type system;
                // a field may be been assigned, but the rhs may violate the field's declared type.
                // But if a field has been initialized by an inline initializer, that assignment respects the field's
                // declared type.
                uninitializedFields.removeIf(f -> initExitStore.isFieldAssigned(f));

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
                            checker.reportError(f, errorMsg, f.getSimpleName());
                        }
                    } else {
                        // Issue all the errors at the relevant constructor
                        StringJoiner fieldsString = new StringJoiner(", ");
                        for (VariableElement f : uninitializedFields) {
                            fieldsString.add(f.getSimpleName());
                        }
                        checker.reportError(tree, errorMsg, fieldsString);
                    }
                }
            }
        }
    }
}
