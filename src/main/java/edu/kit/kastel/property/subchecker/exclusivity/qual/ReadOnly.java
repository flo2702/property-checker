package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@SubtypeOf({})
public @interface ReadOnly {}
