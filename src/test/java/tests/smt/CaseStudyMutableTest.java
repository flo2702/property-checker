/* This file is part of the Property Checker.
 * Copyright (c) 2024 -- present. Property Checker developers.
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
package tests.smt;

import org.junit.runners.Parameterized.Parameters;
import tests.property.PropertyCheckerTest;

import java.io.File;
import java.util.List;

@SuppressWarnings("nls")
public class CaseStudyMutableTest extends PropertyCheckerTest {
    public CaseStudyMutableTest(List<File> testFiles) {
        super(
                testFiles,
                "tests/smt/_case_study_mutable/lattice_nullness"
                        + ",tests/smt/_case_study_mutable/lattice_agedover"
                		+ ",tests/smt/_case_study_mutable/lattice_allowedfor"
                        + ",tests/smt/_case_study_mutable/lattice_interval"
                        + ",tests/smt/_case_study_mutable/lattice_empty"
                        + ",tests/smt/_case_study_mutable/lattice_sign"
                        + ",tests/smt/_case_study_mutable/lattice_sorted"
                        + ",tests/smt/_case_study_mutable/lattice_inv",
                "tests/smt/_case_study_mutable/",
                "edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"smt/_case_study_mutable"};
    }
}
