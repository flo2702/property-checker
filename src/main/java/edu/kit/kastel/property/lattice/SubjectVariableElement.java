package edu.kit.kastel.property.lattice;

import org.checkerframework.checker.nullness.qual.NonNull;

import javax.lang.model.element.*;
import javax.lang.model.type.TypeMirror;
import java.lang.annotation.Annotation;
import java.lang.reflect.Array;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * A custom {@code VariableElement} implementation to "simulate" the subject variable in property refinements.
 * <p>
 * This is essentially a workaround for the fact that all variables/parameters in the checker framework's
 * {@code JavaExpression} abstraction must be backed by a "real" variable from the program. Since there is no "real"
 * subject variable in code, we synthesise our own.
 */
public final class SubjectVariableElement implements VariableElement {
    private static final String NAME = "§subject§";

    private final TypeMirror type;

    public SubjectVariableElement(TypeMirror type) {
        this.type = type;
    }

    @Override
    public TypeMirror asType() {
        return type;
    }

    @Override
    public ElementKind getKind() {
        return ElementKind.OTHER;
    }

    @Override
    public Set<Modifier> getModifiers() {
        return Set.of();
    }

    @Override
    public Object getConstantValue() {
        return null;
    }

    @Override
    public Name getSimpleName() {
        return new Name() {

            @Override
            public boolean contentEquals(CharSequence cs) {
                return cs.toString().equals(NAME);
            }

            @Override
            public int length() {
                return NAME.length();
            }

            @Override
            public char charAt(int index) {
                return NAME.charAt(index);
            }

            @NonNull
            @Override
            public CharSequence subSequence(int start, int end) {
                return NAME.subSequence(start, end);
            }
        };
    }

    @Override
    public Element getEnclosingElement() {
        return null;
    }

    @Override
    public List<? extends Element> getEnclosedElements() {
        return List.of();
    }

    @Override
    public List<? extends AnnotationMirror> getAnnotationMirrors() {
        return List.of();
    }

    @Override
    public <A extends Annotation> A getAnnotation(Class<A> annotationType) {
        return null;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <A extends Annotation> A[] getAnnotationsByType(Class<A> annotationType) {
        return (A[]) Array.newInstance(annotationType, 0);
    }

    @Override
    public <R, P> R accept(ElementVisitor<R, P> v, P p) {
        return v.visitVariable(this, p);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SubjectVariableElement that = (SubjectVariableElement) o;
        return Objects.equals(type, that.type);
    }

    @Override
    public int hashCode() {
        return Objects.hashCode(type);
    }
}
