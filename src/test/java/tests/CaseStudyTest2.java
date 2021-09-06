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
package tests;

import java.io.File;
import java.util.List;

import org.junit.runners.Parameterized.Parameters;

@SuppressWarnings("nls")
public class CaseStudyTest2 extends PropertyCheckerTest {
    public CaseStudyTest2(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/_case_study2/lattice_nullness"
                        + ",tests/property/_case_study2/lattice_agedover"
                		+ ",tests/property/_case_study2/lattice_allowedfor"
                        + ",tests/property/_case_study2/lattice_interval"
                        + ",tests/property/_case_study2/lattice_length"
                        + ",tests/property/_case_study2/lattice_okasaki"
                        + ",tests/property/_case_study2/lattice_sign",
                "tests/property/_case_study2/",
                "edu.kit.iti.checker.property.subchecker.lattice.case_study_qual");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/_case_study2"};
    }
}
