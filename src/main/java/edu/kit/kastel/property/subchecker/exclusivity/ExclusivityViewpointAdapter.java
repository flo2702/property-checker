package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.framework.type.AbstractViewpointAdapter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;

public class ExclusivityViewpointAdapter extends AbstractViewpointAdapter {

    protected ExclusivityAnnotatedTypeFactory atypeFactory;

    public ExclusivityViewpointAdapter(ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(atypeFactory);
        this.atypeFactory = atypeFactory;
    }

    @Override
    protected AnnotationMirror extractAnnotationMirror(AnnotatedTypeMirror atm) {
        return atypeFactory.getExclusivityAnnotation(atm);
    }

    @Override
    protected AnnotationMirror combineAnnotationWithAnnotation(
            AnnotationMirror receiverAnnotation, AnnotationMirror declaredAnnotation
    ) {
        if (AnnotationUtils.areSame(declaredAnnotation, atypeFactory.UNIQUE)) {
            return receiverAnnotation;
        } else {
            return declaredAnnotation;
        }
    }

    @Override
    protected AnnotatedTypeMirror combineAnnotationWithType(
            AnnotationMirror receiverAnnotation, AnnotatedTypeMirror declaredType) {
        AnnotatedTypeMirror result = AnnotatedTypeMirror.createType(
                declaredType.getUnderlyingType(), atypeFactory, declaredType.isDeclaration());
        if (declaredType.getPrimitiveKind() != null) {
            result.addAnnotation(atypeFactory.UNIQUE);
            return result;
        } else if (declaredType.hasAnnotation(atypeFactory.UNIQUE)) {
            result.addAnnotation(receiverAnnotation);
            return result;
        } else {
            result.addAnnotation(declaredType.getAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        }
    }

    @Override
    protected AnnotatedTypeMirror combineTypeWithType(
            AnnotatedTypeMirror receiverType, AnnotatedTypeMirror declaredType) {
        AnnotatedTypeMirror result = AnnotatedTypeMirror.createType(
                declaredType.getUnderlyingType(), atypeFactory, declaredType.isDeclaration());
        if (declaredType.getPrimitiveKind() != null) {
            result.addAnnotation(atypeFactory.UNIQUE);
            return result;
        } else if (declaredType.hasAnnotation(atypeFactory.UNIQUE)) {
            result.addAnnotation(receiverType.getAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        } else {
            result.addAnnotation(declaredType.getAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        }
    }
}
