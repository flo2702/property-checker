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

import edu.kit.kastel.property.checker.PropertyChecker;
import org.apache.commons.lang3.ObjectUtils;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;

import java.io.File;
import java.util.List;

@SuppressWarnings("nls")
public abstract class PropertyCheckerTest extends CheckerFrameworkPerDirectoryTest {

    public PropertyCheckerTest(List<File> testFiles, String latticeFile, String classesDir) {
        this(testFiles, latticeFile, classesDir, "edu.kit.kastel.property.subchecker.lattice.qual");
    }

    public PropertyCheckerTest(List<File> testFiles, String latticeFile, String classesDir, String qualPackage) {
        this(testFiles, latticeFile, classesDir, qualPackage, new String[0]);
    }

    public PropertyCheckerTest(List<File> testFiles, String latticeFile, String classesDir, String qualPackage, String... extraArgs) {
        super(
                testFiles,
                PropertyChecker.class,
                "property",
                getArgs(testFiles, latticeFile, classesDir, qualPackage, extraArgs)
                );
    }

    private static String[] getArgs(List<File> testFiles, String latticeFile, String classesDir, String qualPackage, String... extraArgs) {
        String[] defaultArgs = new String[]{
                "-Anomsgtext",
                "-Astubs=stubs/",
                "-nowarn",
                "-Aflowdotdir=../flowdot",
                "-APropertyChecker_inDir=" + classesDir,
                "-APropertyChecker_outDir=" + "../property-checker-out",
                "-APropertyChecker_lattices=" + latticeFile,
                "-APropertyChecker_qualPkg=" + qualPackage,
                "-APropertyChecker_translationOnly=" + ObjectUtils.defaultIfNull(System.getProperty("translationOnly"), "false")
        };
        String[] args = new String[defaultArgs.length + extraArgs.length];
        System.arraycopy(defaultArgs, 0, args, 0, defaultArgs.length);
        System.arraycopy(extraArgs, 0, args, defaultArgs.length, args.length);
        return args;
    }
}
