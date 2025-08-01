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
package tests.property;

import java.io.File;
import java.util.List;

import org.junit.Ignore;
import org.junit.runners.Parameterized.Parameters;

@Ignore
@SuppressWarnings("nls")
public class InterfaceTest extends PropertyCheckerTest {
    public InterfaceTest(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/lattice_length_custom_list",
                "tests/property/InterfaceTest/");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/InterfaceTest"};
    }
}
