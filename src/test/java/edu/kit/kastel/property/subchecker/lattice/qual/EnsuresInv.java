package edu.kit.kastel.property.subchecker.lattice.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  Inv.class)
@Repeatable(EnsuresInv.List.class)
public @interface EnsuresInv {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = Inv.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresInv[] value();
    }
}
