package edu.kit.kastel.property.subchecker.lattice.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  InvUnknown.class)
@Repeatable(EnsuresInvUnknown.List.class)
public @interface EnsuresInvUnknown {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = InvUnknown.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresInvUnknown[] value();
    }
}
