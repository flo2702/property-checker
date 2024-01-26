package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import java.util.Set;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedPrimitiveType;

public final class ExclusivityVisitor extends BaseTypeVisitor<ExclusivityAnnotatedTypeFactory> {
    public ExclusivityVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    @Override
    public Void visitAnnotation(AnnotationTree tree, Void p) {
        // do nothing
        return null;
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        // TODO Not thread-safe :-)
        atypeFactory.useIFlowAfter(node);
        validateType(node, atypeFactory.getAnnotatedTypeLhs(node));
        if (node.getInitializer() != null) {
            validateTypeOf(node.getInitializer());
        }
        atypeFactory.useRegularIFlow();
        //return super.visitAssignment(node, p);
        return p;
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        try {
            MemberSelectTree lhs = (MemberSelectTree) node.getVariable();
            try {
                IdentifierTree ident = (IdentifierTree) lhs.getExpression();
                // Field access is only allowed to fields of this, not other objects
                if (!ident.getName().contentEquals("this")) {
                    checker.reportError(node, "assignment.invalid-lhs");
                }
                // Field access is only allowed if this is not ReadOnly
                if (atypeFactory.getAnnotatedType(ident).hasAnnotation(atypeFactory.READ_ONLY)) {
                    // T-Assign: lhs is local var OR this is modifiable
                    checker.reportError(node, "assignment.this-not-writable");
                }
            } catch (ClassCastException e) {
                // No field access to arbitrary expressions is allowed
                checker.reportError(node, "assignment.invalid-lhs");
            }
        } catch (ClassCastException ignored) {}

        // TODO Not thread-safe :-)
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node.getExpression());
        validateTypeOf(node.getVariable());
        atypeFactory.useRegularIFlow();

        //return super.visitAssignment(node, p);
        return p;
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node);
        ExpressionTree recv = node.getMethodSelect();
        validateTypeOf(recv);
        if (recv instanceof MemberSelectTree) {
            validateTypeOf(((MemberSelectTree) recv).getExpression());
        }
        for (ExpressionTree arg : node.getArguments()) {
            validateTypeOf(arg);
        }
        atypeFactory.useRegularIFlow();
        return p;
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        // Don't try to check return expressions for void methods.
        if (node.getExpression() == null) {
            return super.visitReturn(node, p);
        }
        
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node.getExpression());
        atypeFactory.useRegularIFlow();
        return p;
    }
    
    @Override
    public boolean isValidUse(AnnotatedPrimitiveType type, Tree tree) {
        return super.isValidUse(type, tree)
                // Primitives are always MaybeAliased
                && type.hasAnnotation(atypeFactory.MAYBE_ALIASED);
    }
    
    @SuppressWarnings("nls")
    @Override
    public boolean isValidUse(AnnotatedDeclaredType declarationType,
            AnnotatedDeclaredType useType, Tree tree) {
        if (declarationType.getUnderlyingType().asElement().toString().equals("java.lang.String")) {
            return super.isValidUse(declarationType, useType, tree)
                    // Strings should always be annotated as MaybeAliased.
                    // There's no point annotating them as Unique, since they're immutable.
                    && useType.hasAnnotation(atypeFactory.MAYBE_ALIASED);
        } else {
            return super.isValidUse(declarationType, useType, tree);
        }
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new ExclusivityValidator(checker, this, atypeFactory);
    }
    
    @SuppressWarnings("nls")
    @Override
    protected void checkConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // A constructor result can be refined to any type (see TRefNew),
        // so we return a warning if the user unnecessarily overwrites the default.
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        
        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, atypeFactory.UNIQUE);
        if (!qualifierHierarchy.isSubtypeQualifiersOnly(atypeFactory.UNIQUE, constructorAnno)) {
            checker.reportWarning(
                    constructorElement, "unnecessary.constructor.type", constructorAnno, atypeFactory.UNIQUE);
        }
    }
    
    @Override
    protected boolean commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        if (valueTree instanceof NewClassTree) {
            // A constructor result can be of any type, as this cannot be leaked
            // in the constructor except as ReadOnly,
            // so ignore any error here.
            return true;
        }
        
        return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
    }
}
