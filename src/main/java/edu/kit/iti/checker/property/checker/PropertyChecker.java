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
package edu.kit.iti.checker.property.checker;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.PriorityQueue;
import java.util.stream.Collectors;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.apache.commons.io.FileUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SupportedOptions;
import org.checkerframework.javacutil.InternalUtils;

import edu.kit.iti.checker.property.config.Config;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeVisitor;

@SupportedOptions({
    Config.LATTICES_FILE_OPTION,
    Config.INPUT_DIR_OPTION,
    Config.OUTPUT_DIR_OPTION,
    Config.QUAL_PKG_OPTION,
    Config.TRANSLATION_JML_DIALECT_OPTION,
    Config.TRANSLATION_ONLY_OPTION,
})
public class PropertyChecker extends BaseTypeChecker {

    private Map<String, PriorityQueue<LatticeVisitor.Result>> results = new HashMap<>();

    private boolean collectingSubcheckers = false;

    private URLClassLoader projectClassLoader;

    public PropertyChecker() { }

    @Override
    protected LinkedHashSet<BaseTypeChecker> getImmediateSubcheckers() {
        collectingSubcheckers = true;

        LinkedHashSet<BaseTypeChecker> checkers = super.getImmediateSubcheckers();

        String[] lattices = getLattices();
        String inputDir = getInputDir();
        String qualPackage = getQualPackage();

        int ident = 0;
        for (String lattice : lattices) {
            checkers.add(new LatticeSubchecker(this, new File(lattice.strip()), new File(inputDir), qualPackage, ident++));
        }

        collectingSubcheckers = false;
        return checkers;
    }
    
    public String getInputDir() {
    	return getOption(Config.INPUT_DIR_OPTION);
    }
    
    public String[] getLattices() {
    	return getOption(Config.LATTICES_FILE_OPTION).split(Config.SPLIT);
    }

    public String getOutputDir() {
    	return getOption(Config.OUTPUT_DIR_OPTION);
    }
    
    public String getQualPackage() {
    	return getOption(Config.QUAL_PKG_OPTION);
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        return collectingSubcheckers ? Collections.emptyList() : super.getSubcheckers();
    }

    @SuppressWarnings("nls")
    public URLClassLoader getProjectClassLoader() {
        if (projectClassLoader == null) {
            try {
                File projectClasses = new File(getInputDir());

                JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
                StandardJavaFileManager fileManager = compiler.getStandardFileManager(null, null, null);
                @SuppressWarnings({ "unchecked" })
                Iterable<? extends JavaFileObject> src = fileManager.getJavaFileObjectsFromFiles(
                        FileUtils.listFiles(projectClasses, new String[] {"java"}, true));

                ClassLoader currentClassLoader = InternalUtils.getClassLoaderForClass(getClass());
                String sep = System.getProperty("path.separator");
                String classPathStr = System.getProperty("java.class.path") + sep + projectClasses.toURI().toURL();
                
                if (currentClassLoader instanceof URLClassLoader) {
                    classPathStr +=
                            sep
                            + Arrays.stream(((URLClassLoader) currentClassLoader).getURLs()).map(URL::toString).collect(Collectors.joining(sep));
                }
                
                JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager, null,
                        Arrays.asList("-classpath", classPathStr),
                        null, src);
                task.call();
                
                projectClassLoader = new URLClassLoader(new URL[] {projectClasses.toURI().toURL()}, currentClassLoader);
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }

        return projectClassLoader;
    }

    public void addResult(String fileName, LatticeVisitor.Result result) {
        if (!results.containsKey(fileName)) {
            results.put(fileName, new PriorityQueue<>(
                        (r0, r1) -> r0.getChecker().getIdent() - r1.getChecker().getIdent()));

            results.get(fileName).add(result);
        } else {
            Optional<LatticeVisitor.Result> optional = results.get(fileName).stream().filter(r -> r.getChecker().equals(result.getChecker())).findAny();
            if (optional.isPresent()) {
                LatticeVisitor.Result r = optional.get();
                r.addAll(result);
            } else {
                results.get(fileName).add(result);
            }
        }
    }

    public List<LatticeVisitor.Result> getResults(String fileName) {
        PriorityQueue<LatticeVisitor.Result> q = results.get(fileName);
        return q != null ? Collections.unmodifiableList(new ArrayList<>(q)) : Collections.emptyList();
    }

    public PropertyAnnotatedTypeFactory getPropertyFactory() {
        return (PropertyAnnotatedTypeFactory) getTypeFactory();
    }
}
