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
package tests.oopsla2021;

import java.io.File;
import java.util.List;

import org.checkerframework.checker.nullness.NullnessChecker;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.Ignore;
import org.junit.runners.Parameterized.Parameters;

@Ignore
@SuppressWarnings("nls")
public class DaikonNullnessCheckerTest2 extends CheckerFrameworkPerDirectoryTest {
    public DaikonNullnessCheckerTest2(List<File> testFiles) {
        super(
                testFiles,
                NullnessChecker.class, "nullness");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"oopsla2021/_daikon2_nullness"};
    }
}
