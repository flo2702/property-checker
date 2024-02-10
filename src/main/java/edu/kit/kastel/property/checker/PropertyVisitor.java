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
package edu.kit.kastel.property.checker;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.List;
import java.util.StringJoiner;

import com.sun.source.tree.Tree;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree.JCCompilationUnit;

import edu.kit.kastel.property.printer.JavaJMLPrinter;
import edu.kit.kastel.property.printer.PrettyPrinter;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor.Result;
import edu.kit.kastel.property.util.FileUtils;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;

public final class PropertyVisitor extends PackingVisitor {

    protected PropertyVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    @SuppressWarnings("nls")
	@Override
    public void visit(TreePath path) {
        super.visit(path);

        File file = Paths.get(getPropertyChecker().getOutputDir(), getRelativeSourceFileName()).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);

        try (BufferedWriter out = new BufferedWriter(new FileWriter(file))) {
        	List<Result> results = getPropertyChecker().getResults(getAbsoluteSourceFileName());
        	if (results.isEmpty()) {
        		PrettyPrinter printer = new PrettyPrinter(out, true);
            	printer.printUnit((JCCompilationUnit) path.getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with no remaining proof obligations",
                        getRelativeSourceFileName()));
        	} else {
        		JavaJMLPrinter printer = new JavaJMLPrinter(getPropertyChecker().getResults(getAbsoluteSourceFileName()), getPropertyChecker(), out);
            	printer.printUnit((JCCompilationUnit) path.getCompilationUnit(), null);
            	System.out.println(String.format(
            			"Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)",
            			getRelativeSourceFileName(),
            			printer.getAssertions(), printer.getAssumptions(),
            			printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions()));
        	}
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    @Override
    protected void checkFieldsInitializedUpToFrame(
            Tree tree,
            TypeMirror frame) {
        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();

            List<VariableElement> uninitializedFields =
                    atypeFactory.getUninitializedFields(
                            atypeFactory.getStoreBefore(tree),
                            targetFactory.getStoreBefore(tree),
                            getCurrentPath(),
                            false,
                            List.of());

            // Remove fields below frame
            uninitializedFields.retainAll(ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), elements));

            // Remove fields with a relevant @SuppressWarnings annotation
            uninitializedFields.removeIf(
                    f -> checker.shouldSuppressWarnings(f, "initialization.field.uninitialized"));

            if (!uninitializedFields.isEmpty()) {
                StringJoiner fieldsString = new StringJoiner(", ");
                for (VariableElement f : uninitializedFields) {
                    fieldsString.add(f.getSimpleName());
                }
                checker.reportError(tree, "initialization.fields.uninitialized", fieldsString);

                // Add uninitialized fields to LatticeVisitor for JML printer to use
                if (targetChecker instanceof LatticeSubchecker) {
                    LatticeVisitor latticeVisitor = (LatticeVisitor) targetChecker.getVisitor();
                    latticeVisitor.addUninitializedFields(tree, uninitializedFields);
                }
            }
        }
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        return new PropertyAnnotatedTypeFactory(checker);
    }

    protected String getAbsoluteSourceFileName() {
        return Paths.get(root.getSourceFile().getName()).toAbsolutePath().toString();
    }

    protected String getRelativeSourceFileName() {
        String classesDir = Paths.get(getPropertyChecker().getInputDir()).toAbsolutePath().toString();
        return getAbsoluteSourceFileName().substring(classesDir.length());
    }

    public PropertyChecker getPropertyChecker() {
        return (PropertyChecker) checker;
    }
}
