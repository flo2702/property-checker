package edu.kit.kastel.property.util;

import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public class JavaExpressionUtil {

    public static JavaExpression getReceiver(JavaExpression expr) {
        return switch (expr) {
            case MethodCall m -> m.getReceiver();
            case FieldAccess f -> f.getReceiver();
            default -> null;
        };
    }

    /**
     * Construct a pseudo method invocation from a constructor call tree that can be used to represent constructor calls
     * as a {@code JavaExpression} (where they are otherwise unsupported).
     * <p>
     * The resulting method call uses:
     * <ul>
     *     <li>the underlying constructor as its {@code ExecutableElement}</li>
     *     <li>a {@code ClassName} as the receiver</li>
     *     <li>the constructed class type as its return type</li>
     *     <li>the arguments as-is (converted to {@code JavaExpression}s)</li>
     * </ul>
     * <p>
     * Note that this method only creates such a pseudo-call for the given {@code NewClassTree}, not
     * for any {@code NewClassTree}s that are potentially nested in the arguments.
     * Thus, the resulting expression may contain {@code Unknown}s.
     *
     * @param tree the constructor invocation tree
     * @return a method call expression representing the constructor call
     */
    public static MethodCall constructorCall(NewClassTree tree) {
        ExecutableElement invokedConstructor = TreeUtils.getSuperConstructor(tree);
        TypeMirror type = invokedConstructor.getEnclosingElement().asType();
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        return new MethodCall(type, invokedConstructor,
                new ClassName(type), arguments);
    }


    /**
     * Tests whether a given {@code JavaExpression} could depend on the value of a specific field access.
     * "Could depend" means that the JavaExpression either references the exact same field or references the same field
     * on a different expression that could be an alias of the dependency. Whether two expressions can be
     * aliases is determined by the exclusivity type system.
     * <p>
     * {@code expr} is also considered dependent if it contains any method call, since we have no way of knowing
     * whether the called method uses the field in its implementation somehow.
     *
     * @param expr The expression to test.
     * @param dependency The field access to look for in {@code expr}.
     * @param tree the position in the code where this test is performed. This is relevant for the exclusivity analysis.
     * @param exclFactory the exclusivity factory
     * @return {@code true} if {@code expr} should be considered dependent on {@code dependency}.
     */
    public static boolean maybeDependent(
            JavaExpression expr,
            FieldAccess dependency,
            Tree tree,
            ExclusivityAnnotatedTypeFactory exclFactory
    ) {
        var scanner = new AliasScanner(exclFactory, tree, dependency);
        scanner.scan(expr, null);
        return scanner.found;
    }

    private static class AliasScanner extends JavaExpressionScanner<Void> {

        final ExclusivityStore store;
        final FieldAccess reference;
        final QualifierHierarchy exclHierarchy;
        final ExclusivityAnnotatedTypeFactory exclFactory;
        final AnnotationMirror ownerAnno;

        boolean found = false;

        AliasScanner(ExclusivityAnnotatedTypeFactory exclFactory, Tree tree, FieldAccess reference) {
            this.store = exclFactory.getStoreBefore(tree);
            this.reference = reference;
            this.exclFactory = exclFactory;
            this.exclHierarchy = exclFactory.getQualifierHierarchy();
            this.ownerAnno = store.deriveExclusivityValue(reference.getReceiver());
        }

        @Override
        protected Void visitFieldAccess(FieldAccess fieldAccessExpr, Void unused) {
            // could the visited FieldAccess point to the input field on the same object?
            if (possibleAlias(fieldAccessExpr)) {
                found = true;
                return null;
            }

            return super.visitFieldAccess(fieldAccessExpr, unused);
        }

        @Override
        protected Void visitMethodCall(MethodCall methodCallExpr, Void unused) {
            // if a method is called, we conservatively assume that the method implementation depends on the
            // value of the input field behind an owner alias somehow, and thus we consider it dependent.
            if (completelyPureMethod(methodCallExpr.getElement())) {
                return super.visitMethodCall(methodCallExpr, unused);
            }
            found = true;
            return null;
        }

        // Returns true if the method is pure, its return value only depends on its parameters,
        // and there are no field accesses
        private boolean completelyPureMethod(ExecutableElement method) {
            // currently only special handling for Math helpers - more known methods can be added here
            return TypesUtils.getClassFromType(method.getEnclosingElement().asType()) == Math.class;
        }

        private boolean possibleAlias(FieldAccess expr) {
            if (expr.equals(reference)) {
                return true;
            }

            if (expr.getField() != reference.getField()) {
                return false;
            }


            var anno = store.deriveExclusivityValue(expr.getReceiver());
            // references can't be aliases if both are unique, or one is unique and one is maybealiased
            boolean noAlias = (AnnotationUtils.areSame(ownerAnno, exclFactory.UNIQUE) && AnnotationUtils.areSame(anno, exclFactory.UNIQUE))
                    || (AnnotationUtils.areSame(ownerAnno, exclFactory.MAYBE_ALIASED) && AnnotationUtils.areSame(anno, exclFactory.UNIQUE))
                    || (AnnotationUtils.areSame(ownerAnno, exclFactory.UNIQUE) && AnnotationUtils.areSame(anno, exclFactory.MAYBE_ALIASED));
            return !noAlias;
        }
    }

    public static boolean isLiteral(String s) {
        return s.equals("null") || s.matches("-?(\\d+|(\\d*\\.\\d+))");
    }
}
