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
package tests.case_study;

import org.junit.runners.Parameterized.Parameters;
import tests.property.PropertyCheckerTest;

import java.io.File;
import java.util.List;

@SuppressWarnings("nls")
public class CaseStudyMutableVerifastTest extends PropertyCheckerTest {
    public CaseStudyMutableVerifastTest(List<File> testFiles) {
        super(
                testFiles,
                        "tests/case_study/_case_study_mutable/lattice_agedover"
                		+ ",tests/case_study/_case_study_mutable/lattice_allowedfor"
                        + ",tests/case_study/_case_study_mutable/lattice_interval"
                        + ",tests/case_study/_case_study_mutable/lattice_empty"
                        + ",tests/case_study/_case_study_mutable/lattice_sign"
                        + ",tests/case_study/_case_study_mutable/lattice_sorted"
                        //+ ",tests/case_study/_case_study_mutable/lattice_inv",
                ,
                "tests/case_study/_case_study_mutable/",
                "edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual",
                "-APropertyChecker_outputLang=verifast");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"case_study/_case_study_mutable"};
    }
}
