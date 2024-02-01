package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  MaybeAliased.class)
@Repeatable(EnsuresMaybeAliased.List.class)
public @interface EnsuresMaybeAliased {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = MaybeAliased.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresMaybeAliased[] value();
    }
}