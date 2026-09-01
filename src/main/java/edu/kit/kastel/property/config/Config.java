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
package edu.kit.kastel.property.config;

import edu.kit.kastel.property.lattice.Bound;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType.PropertyCheckable;
import edu.kit.kastel.property.lattice.PropertyAnnotationType.WellFormednessCheckable;
import edu.kit.kastel.property.lattice.SubAnnotationRelation;
import edu.kit.kastel.property.util.Pair;

@SuppressWarnings("nls")
public final class Config {

    public static final String LATTICES_FILE_OPTION = "lattices";
    public static final String QUAL_PKG_OPTION = "qualPkg";
    public static final String INPUT_DIR_OPTION = "inDir";
    public static final String OUTPUT_DIR_OPTION = "outDir";
    public static final String SHOULD_NOT_USE_TRAMPOLINE_OPTION = "shouldNotUseTrampoline";

    public static final String OUTPUT_LANG_OPTION = "outputLang";
    public static final String OUTPUT_LANG_JML = "jml";
    public static final String OUTPUT_LANG_VERIFAST = "verifast";

    public static final String TRANSLATION_ONLY_OPTION = "translationOnly";
    public static final String NO_EXCLUSITIVY_OPTION = "noExclusivity";
    public static final String NO_SMT_OPTION = "noSmt";
    public static final String NO_INFER_UNPACK_OPTION = "noInferUnpack";
    public static final String KEEP_GENERICS_OPTION = "keepGenerics";

    public static final String CHECKERS_PACKAGE = "__checkers";

    public static final String CHECKERS_CLASS_PROPERTIES = "Properties";
    public static final String CHECKERS_CLASS_WELL_FORMEDNESS = "WellFormedness";
    public static final String CHECKERS_CLASS_RELATIONS = "Relations";
    public static final String CHECKERS_CLASS_JOINS = "Joins";
    public static final String CHECKERS_CLASS_MEETS = "Meets";

    public static final String SUBJECT_NAME = "subject";

    public static final String SPLIT = ",";
	public static final boolean TEMP_DIR_DELETE_ON_EXIT_DEFAULT = false;

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
