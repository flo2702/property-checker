/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.iti.checker.property.config;

import org.checkerframework.javacutil.Pair;

import edu.kit.iti.checker.property.lattice.Bound;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType.PropertyCheckable;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType.WellFormednessCheckable;
import edu.kit.iti.checker.property.lattice.SubAnnotationRelation;

@SuppressWarnings("nls")
public final class Config {

    public static final String LATTICES_FILE_OPTION = "lattices";
    public static final String QUAL_PKG_OPTION = "qualPkg";
    public static final String INPUT_DIR_OPTION = "inDir";
    public static final String OUTPUT_DIR_OPTION = "outDir";
    
    public static final String TRANSLATION_ONLY_OPTION = "translationOnly";
    
    public static final String TRANSLATION_JML_DIALECT_OPTION = "jmlDialect";
    public static final String TRANSLATION_JML_DIALECT_OPTION_KEY = "key";
    public static final String TRANSLATION_JML_DIALECT_OPTION_OPENJML = "openjml";

    public static final String CHECKERS_PACKAGE = "__checkers";

    public static final String CHECKERS_CLASS_PROPERTIES = "Properties";
    public static final String CHECKERS_CLASS_WELL_FORMEDNESS = "WellFormedness";
    public static final String CHECKERS_CLASS_RELATIONS = "Relations";
    public static final String CHECKERS_CLASS_JOINS = "Joins";
    public static final String CHECKERS_CLASS_MEETS = "Meets";

    public static final String SUBJECT_NAME = "subject";

    public static final String SPLIT = ",";
	public static final boolean TEMP_DIR_DELETE_ON_EXIT_DEFAULT = true;

    public static String methodWellFormedness(WellFormednessCheckable wf) {
        return String.format("wf%s", wf.getPropertyAnnotationType().getName());
    }

    public static String methodProperties(PropertyCheckable prop) {
        return String.format("prop%s", prop.getPropertyAnnotationType().getName());
    }

    public static String methodRelations(SubAnnotationRelation rel) {
        return String.format("rel%s", rel.getSubAnnotationName() + rel.getSuperAnnotationName());
    }

    public static String methodJoins(Bound join) {
        Pair<PropertyAnnotation, PropertyAnnotation> p = join.getOperands().toOrderedPair();
        return String.format("join%s", p.first.getName() + p.second.getName()) + join.getLine();
    }

    public static String methodMeets(Bound meet) {
        Pair<PropertyAnnotation, PropertyAnnotation> p = meet.getOperands().toOrderedPair();
        return String.format("meet%s", p.first.getName() + p.second.getName()) + meet.getLine();
    }

    private Config() { }
}
