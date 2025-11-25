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
package edu.kit.kastel.property.printer;

import com.google.common.collect.Streams;
import com.sun.source.tree.*;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeInfo;
import edu.kit.kastel.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.checker.qual.JMLClause;
import edu.kit.kastel.property.checker.qual.JMLClauseTranslationOnly;
import edu.kit.kastel.property.checker.qual.JMLClauses;
import edu.kit.kastel.property.checker.qual.JMLClausesTranslationOnly;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.lattice.Checkable;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.util.Union;
import org.apache.commons.lang3.StringUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.util.Contract;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.ElementFilter;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.sun.tools.javac.code.Flags.*;
import static com.sun.tools.javac.tree.JCTree.Tag.SELECT;

@SuppressWarnings("nls")
public class JavaJMLPrinter extends PropertyCheckerPrettyPrinter {

    public static String printCheckable(Checkable chk, PropertyAnnotation pa, String subject) {
        String cond = chk.getCondition();

        if (subject != null) {
            cond = cond.replace('§' + Config.SUBJECT_NAME + '§', subject);

            for (int i = 1; i < chk.getParameterNames().length; ++i) {
                String paramName = chk.getParameterNames()[i];
                cond = cond.replace('§' + paramName + '§', pa.getActualParameters().get(i - 1));
            }
        } else {
            for (int i = 0; i < chk.getParameterNames().length; ++i) {
                String paramName = chk.getParameterNames()[i];
                cond = cond.replace('§' + paramName + '§', pa.getActualParameters().get(i));
            }
        }

        return '(' + cond + ')';
    }

    public JavaJMLPrinter(
            List<LatticeVisitor.Result> results,
            PropertyChecker propertyChecker,
            BufferedWriter out) {
        super(results, propertyChecker, out);
    }

    @Override
    public void visitClassDef(JCClassDecl tree) {
        try {
            println();
            align();
            printDocComment(tree);
            printFlags(tree.mods.flags & ~INTERFACE);

            JCClassDecl enclClassPrev = enclClass;
            enclClass = tree;

            if (isInterface(tree)) {
                print("interface " + tree.name);
                printTypeParameters(tree.typarams);
                if (tree.implementing.nonEmpty()) {
                    print(" extends ");
                    printExprs(tree.implementing);
                }
            } else {
                if ((tree.mods.flags & ENUM) != 0) {
                    print("enum " + tree.name);
                } else {
                    print("class " + tree.name);
                }
                printTypeParameters(tree.typarams);
                if (tree.extending != null) {
                    print(" extends ");
                    printExpr(tree.extending);
                }
                if (tree.implementing.nonEmpty()) {
                    print(" implements ");
                    printExprs(tree.implementing);
                }
            }

            print(" ");

            if ((tree.mods.flags & ENUM) != 0) {
                printEnumBody(tree.defs);
            } else {
                println(" {");
                indent();

                // This is not added here, but to the Object class in KeY's JavaRedux
                /*println();
                printlnAligned("//@ public ghost Class packed = Object.class;");
                println();*/

                if (!isInterface(tree)) {
                    printStaticInitializers();
                }

                String containingClassName = enclClass.sym.getQualifiedName().toString();

                println();

                List<VariableElement> allFields = enclClass.type == null
                        ? List.of()
                        : ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());

                getJMLClauseValues(enclClass.sym).forEach(c -> printlnAligned("//@ " + c));
                if (TRANSLATION_RAW) {
                    getJMLClauseValuesTranslationOnly(enclClass.sym).forEach(c -> printlnAligned("//@ " + c));
                }

                for (VariableElement field : allFields) {
                    if (!field.asType().getKind().isPrimitive()) {
                        if (ElementUtils.isStatic(field)) {
                            //TODO
                            /*
                            printlnAligned(String.format(
                                    "//@ public static invariant_free packed <: %s ==> %s;",
                                    containingClassName,
                                    getPackedCondition(
                                            propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized()),
                                            field.getSimpleName().toString())));
                            printlnAligned(String.format(
                                    "//@ public static invariant_free \\invariant_free_for(%s);",
                                    field.getSimpleName().toString()));
                            */
                        } else {
                            printlnAligned(String.format(
                                    "//@ public invariant_free packed <: %s ==> %s;",
                                    containingClassName,
                                    getPackedCondition(
                                            propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized()),
                                            field.getSimpleName().toString())));
                            printlnAligned(String.format(
                                    "//@ public invariant_free \\invariant_free_for(%s);",
                                    field.getSimpleName().toString()));
                        }
                    }
                }

                for (VariableElement field : allFields) {
                    if (!field.asType().getKind().isPrimitive() && exclFactory.getAnnotatedType(field).hasAnnotation(Unique.class)) {
                        List<VariableElement> otherFields = allFields.stream()
                                .filter(f -> !f.asType().getKind().isPrimitive())
                                .filter(f -> ElementUtils.isStatic(f) || !ElementUtils.isStatic(field))
                                .filter(f -> !f.getSimpleName().equals(field.getSimpleName()))
                                .collect(Collectors.toList());

                        StringJoiner sj = new StringJoiner(" && ");
                        otherFields.forEach(f -> sj.add(String.format("%s != %s", field.getSimpleName(), f.getSimpleName())));

                        if (sj.length() != 0) {
                            if (ElementUtils.isStatic(field)) {
                                printlnAligned(String.format("//@ public static invariant_free %s;", sj));
                            } else {
                                printlnAligned(String.format(
                                        "//@ public invariant_free packed <: %s ==> %s;",
                                        containingClassName,
                                        sj));
                            }
                        }
                    }
                }

                for (LatticeVisitor.Result wellTypedness : results) {
                    Lattice lattice = wellTypedness.getLattice();

                    for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                        PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(invariant.getType());
                        if (!pa.getAnnotationType().isTrivial()) {
                            Condition inv = new Condition(
                                    true,
                                    ConditionLocation.INVARIANT_STATIC,
                                    pa,
                                    containingClassName + "." + invariant.getFieldName()
                            );
                            printlnAligned(inv);
                        }
                    }

                    for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                        PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(invariant.getType());
                        if (!pa.getAnnotationType().isTrivial()) {
                            Condition inv = new Condition(
                                    true,
                                    ConditionLocation.INVARIANT_INSTANCE,
                                    pa,
                                    invariant.getFieldName()
                            );
                            printlnAligned(inv.toStringOp("packed <: " + containingClassName, "==>"));
                        }
                    }
                }

                println();

                for (JCTree def : tree.defs) {
                    align();
                    def.accept(this);
                    println();
                }

                undent();
                printlnAligned("}");
            }

            enclClass = enclClassPrev;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        try {
            // omit anonymous constructors
            if (tree.name == tree.name.table.names.init && enclClass == null) {
                return;
            }
            println();
            if (docComments != null && docComments.getCommentText(tree) != null) {
                align();
                printDocComment(tree);
            }

            JCMethodDecl prevEnclMethod = enclMethod;
            enclMethod = tree;
            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

            JMLContract jmlContract = new JMLContract(Flags.asFlagSet(tree.mods.flags));
            //jmlContract.addClause("diverges true;");

            List<String> paramNames = tree.params.stream().map(JCVariableDecl::getName).map(Object::toString).collect(Collectors.toList());
            {
                List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
                List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);

                if (!inputPackingTypes.isEmpty() ) {
                    AnnotationMirror receiverInputType = inputPackingTypes.get(0);
                    if (receiverInputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                        receiverInputType = propertyFactory.getInitialized();
                    }
                    if (receiverInputType != null) {
                        jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(receiverInputType, "this")));
                    }

                    AnnotationMirror receiverOutputType = outputPackingTypes.get(0);
                    if (receiverOutputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                        receiverOutputType = propertyFactory.getInitialized();
                    }
                    if (receiverOutputType != null) {
                        jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(receiverOutputType, "this")));
                    }
                }

                for (int i = 0; i < paramNames.size(); ++i) {
                    if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                        jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(inputPackingTypes.get(i + 1), paramNames.get(i))));
                        jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(outputPackingTypes.get(i + 1), paramNames.get(i))));
                    }
                }
            }

            {
                AnnotatedExecutableType exclMethodType = exclFactory.getAnnotatedType(tree);

                {
                    AnnotatedTypeMirror recvType = exclMethodType.getReceiverType();
                    if (recvType != null && recvType.hasAnnotation(Unique.class)) {

                        List<String> otherParams = IntStream.range(0, paramNames.size())
                                .filter(j -> !exclMethodType.getParameterTypes().get(j).getKind().isPrimitive())
                                .mapToObj(j -> paramNames.get(j))
                                .collect(Collectors.toList());

                        StringJoiner sj = new StringJoiner(" && ");
                        otherParams.forEach(p -> sj.add(String.format("this != %s", p)));

                        if (sj.length() != 0) {
                            jmlContract.addClause(String.format("requires_free %s;", sj));
                        }
                    }
                }

                for (int i = 0; i < exclMethodType.getParameterTypes().size(); ++i) {
                    AnnotatedTypeMirror paramType = exclMethodType.getParameterTypes().get(i);
                    String paramName = paramNames.get(i);
                    if (!paramType.getKind().isPrimitive() && paramType.hasAnnotation(Unique.class)) {

                        List<String> otherParams = IntStream.range(0, paramNames.size())
                                .filter(j -> !exclMethodType.getParameterTypes().get(j).getKind().isPrimitive())
                                .filter(j -> !paramNames.get(j).equals(paramName))
                                .mapToObj(j -> paramNames.get(j))
                                .collect(Collectors.toList());

                        StringJoiner sj = new StringJoiner(" && ");
                        otherParams.forEach(p -> sj.add(String.format("%s != %s", paramName, p)));

                        if (sj.length() != 0) {
                            jmlContract.addClause(String.format("requires_free %s;", sj));
                        }
                    }
                }
            }

            for (CooperativeVisitor.Result wellTypedness : results) {
                GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                Lattice lattice = wellTypedness.getLattice();
                AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);

                if (method.getReceiverType() != null) {
                    AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(requiredReceiverType);
                    if (!pa.getAnnotationType().isInv()) {
                        jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this"));
                    }
                }

                for (int i = 0; i < method.getParameterTypes().size(); ++i) {
                    AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                    String paramName = paramNames.get(i);

                    if (!AnnotationUtils.areSame(paramType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                        jmlContract.addClause(
                                new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, lattice.getEffectivePropertyAnnotation(paramType), paramName));
                    }
                }
            }

            if (isConstructor(tree)) {
                for (LatticeVisitor.Result wellTypedness : results) {
                    GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                    AnnotatedTypeMirror receiverType = factory.getMethodReturnType(enclMethod);

                    if (AnnotationUtils.areSame(receiverType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                        continue;
                    }

                    Lattice lattice = wellTypedness.getLattice();
                    boolean wt = wellTypedness.isWellTypedConstructor(tree);

                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(receiverType);
                    if (!(pa.getAnnotationType().isInv() && !wt)) {
                        jmlContract.addClause(new Condition(wt, ConditionLocation.POSTCONDITION, pa, "this"));
                    }
                    if (!wt) {
                        ++methodCallPostconditions;
                    } else {
                        ++freeMethodCallPostconditions;
                    }
                }
            } else {
                for (LatticeVisitor.Result wellTypedness : results) {
                    Lattice lattice = wellTypedness.getLattice();
                    GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                    AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

                    if (!(returnType instanceof AnnotatedExecutableType)
                            && returnType.getKind() != TypeKind.VOID
                            && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                        boolean wt = wellTypedness.isWellTypedMethodResult(tree);
                        PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);
                        jmlContract.addClause(new Condition(wt, ConditionLocation.POSTCONDITION, pa, "\\result"));

                        if (!wt) {
                            ++methodCallPostconditions;
                        } else {
                            ++freeMethodCallPostconditions;
                        }
                    }
                }
            }

            for (CooperativeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);

                if (factory instanceof NullnessLatticeAnnotatedTypeFactory) {
                    // Nullness Checker
                    Set<Contract> contracts = factory.getContractsFromMethod().getContracts(TreeUtils.elementFromDeclaration(tree));
                    StringToJavaExpression stringToJavaExpr =
                            stringExpr -> StringToJavaExpression.atMethodBody(stringExpr, tree, factory.getChecker());

                    for (Contract contract : contracts) {
                        String exprStr = contract.expressionString;
                        AnnotationMirror anno = contract.viewpointAdaptDependentTypeAnnotation(
                                factory, stringToJavaExpr, tree);
                        JavaExpression exprJe;
                        try {
                            exprJe = StringToJavaExpression.atMethodBody(
                                    exprStr, tree, factory.getChecker());
                        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                            throw new UncheckedIOException("Cannot parse contract", new IOException(e));
                        }

                        if (contract.kind == Contract.Kind.POSTCONDITION) {
                            // @EnsuresNonNull(exprJe)
                            boolean wt = !wellTypedness.getNullnessPostconditions().get(tree).contains(Pair.of(anno, exprJe));
                            jmlContract.addClause(String.format(
                                    "%s %s != null;",
                                    wt ? "ensures_free" : "ensures",
                                    exprJe));
                        } else if (contract.kind == Contract.Kind.CONDITIONALPOSTCONDITION) {
                            // @EnsuresNonNullIf(exprJe, contractResult)
                            boolean contractResult = ((Contract.ConditionalPostcondition) contract).resultValue;
                            boolean wt = !wellTypedness.getNullnessCondPostconditions().get(tree).contains(Triple.of(anno, exprJe, contractResult));
                            jmlContract.addClause(String.format(
                                    "%s %s ==> %s != null;",
                                    wt ? "ensures_free" : "ensures",
                                    contractResult ? "\\result" : "!\\result",
                                    exprJe));
                        } else if (contract.kind == Contract.Kind.PRECONDITION) {
                            // @RequiresNonNull(exprJe)
                            jmlContract.addClause(String.format(
                                    "requires %s != null;",
                                    exprJe));
                        } else {
                            throw new AssertionError("unknown contract kind");
                        }
                    }
                } else {
                    // Lattice Subchecker
                    List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                    Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                    if (!methodOutputTypes.isEmpty()) {
                        AnnotationMirror paramOutputType = methodOutputTypes.get(0);
                        String paramName = "this";
                        boolean wt = !illTypedMethodOutputParams.contains(0);

                        if (paramOutputType != null && !AnnotationUtils.areSame(paramOutputType, getTop(factory))) {
                            PropertyAnnotation pa = lattice.getPropertyAnnotation(paramOutputType);
                            if (!(pa.getAnnotationType().isInv() && !wt)) {
                                jmlContract.addClause(
                                        new Condition(
                                                wt,
                                                ConditionLocation.POSTCONDITION,
                                                pa,
                                                paramName));
                            }

                            if (!wt) {
                                ++methodCallPostconditions;
                            } else {
                                ++freeMethodCallPostconditions;
                            }
                        }
                    }
                    for (int i = 0; i < method.getParameterTypes().size(); ++i) {
                        AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                        String paramName = paramNames.get(i);
                        boolean wt = !illTypedMethodOutputParams.contains(i + 1);

                        if (!AnnotationUtils.areSame(paramOutputType, getTop(factory))) {
                            jmlContract.addClause(
                                    new Condition(
                                            wt,
                                            ConditionLocation.POSTCONDITION,
                                            lattice.getPropertyAnnotation(paramOutputType),
                                            paramName));

                            if (!wt) {
                                ++methodCallPostconditions;
                            } else {
                                ++freeMethodCallPostconditions;
                            }
                        }
                    }
                }
            }

            if (!isConstructor(tree) && !ElementUtils.isStatic(element) && !results.stream().anyMatch(wt -> wt.getLattice().getIdent().equals("inv"))) {
                jmlContract.addClause("requires_free \\invariant_free_for(this);");
                jmlContract.addClause("ensures_free \\invariant_free_for(this);");
            }
            if (propertyFactory.isSideEffectFree(element)) {
                jmlContract.addClause("assignable \\nothing;");
            }

            getJMLClauseValues(element).forEach(jmlContract::addClause);
            if (TRANSLATION_RAW) {
                getJMLClauseValuesTranslationOnly(element).forEach(jmlContract::addClause);
            }
            
            printlnAligned(jmlContract.toString());

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                if (!results.stream().anyMatch(wt -> wt.getLattice().getIdent().equals("inv"))) {
                    print("/*@helper@*/ ");
                }
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
            } else {
                TypeKind k = propertyFactory.getAnnotatedType(tree).getReturnType().getKind();
                if (k != TypeKind.VOID && !k.isPrimitive()) {
                    print("/*@nullable@*/ ");
                }
                if (!results.stream().anyMatch(wt -> wt.getLattice().getIdent().equals("inv"))) {
                    print("/*@helper@*/ ");
                }
                if (tree.restype.type instanceof Type.TypeVar && !propertyFactory.getChecker().shouldKeepGenerics()) {
                    print("Object");
                } else {
                    printExpr(tree.restype);
                }
                print(" " + tree.name);
            }

            print("(");

            StringJoiner paramsStr = new StringJoiner(", ");
            for (JCVariableDecl param : tree.params) {
                paramsStr.add(unannotatedNullableTypeName(param) + " " + param.getName());
            }
            print(paramsStr);


            print(")");

            if (tree.thrown.nonEmpty()) {
                print(" throws ");
                printExprs(tree.thrown);
            }

            if (tree.defaultValue != null) {
                print(" default ");
                printExpr(tree.defaultValue);
            }

            if (tree.body != null) {
                println(" {");
                indent();

                if (isConstructor(tree)) {
                    // super constructor call
                    align();
                    printStat(tree.body.stats.get(0));
                    println();

                    printInstanceInitializers();
                    println();

                    for (int i = 1; i < tree.body.stats.size(); ++i) {
                        JCStatement statement = tree.body.stats.get(i);

                        align();
                        printStat(statement);
                        println();
                    }
                } else {
                    for (JCStatement statement : tree.body.stats) {
                        align();
                        printStat(statement);
                        println();
                    }
                }

                // Print inferred packing statements
                try {
                    TypeMirror unpackFrame = propertyFactory.getInferredUnpackFrame(enclMethod);
                    TypeMirror packFrame = propertyFactory.getInferredPackFrame(enclMethod);
                    if (unpackFrame != null) {
                        printUnpackStatement(enclMethod, unpackFrame.toString());
                    } else if (packFrame != null) {
                        printPackStatement(enclMethod, packFrame.toString());
                    }
                } catch (IOException e) {
                    throw new java.io.UncheckedIOException(e);
                }

                undent();
                printlnAligned("}");
            } else {
                print(";");
            }

            enclMethod = prevEnclMethod;

            if (!isInterface(enclClass) && !(isAbstract(enclClass) && isConstructor(tree))) {
                println();
                printTrampoline(tree);
            } else if (isInterface(enclClass)) {
                printTrampoline(tree, false);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitReturn(JCReturn tree) {
        // Print inferred packing statements
        try {
            TypeMirror unpackFrame = propertyFactory.getInferredUnpackFrame(enclMethod);
            TypeMirror packFrame = propertyFactory.getInferredPackFrame(enclMethod);
            if (unpackFrame != null) {
                printUnpackStatement(enclMethod, unpackFrame.toString());
            } else if (packFrame != null) {
                printPackStatement(enclMethod, packFrame.toString());
            }
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }

        super.visitReturn(tree);
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        try {
            if (propertyFactory.getChecker().shouldNotUseTrampoline(tree.type.toString())) {
                super.visitNewClass(tree);
                return;
            }

            if (tree.encl != null) {
                printExpr(tree.encl);
                print(".");
            }

            if (tree.def != null && tree.def.mods.annotations.nonEmpty()) {
                printTypeAnnotations(tree.def.mods.annotations);
            }
            printExpr(tree.clazz);
            print(".");
            print(trampolineName("<init>"));
            print("(");

            AnnotatedExecutableType invokedMethod = propertyFactory.constructorFromUse(tree).executableType;
            StringJoiner args = new StringJoiner(", ");
            args.add(tree.args.toString());

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().constructorFromUse(tree).executableType;

                for (int i = 0; i < invokedMethod.getParameterTypes().size(); ++i) {
                    PropertyAnnotationType pat = wellTypedness.getLattice().getEffectivePropertyAnnotation(methodType.getParameterTypes().get(i)).getAnnotationType();
                    if (!pat.isTrivial()) {
                        args.add(wellTypedness.getIllTypedConstructorParams(tree).contains(i) || TRANSLATION_RAW ? "false" : "true");
                    }
                }
            }

            print(args);

            print(")");
            if (tree.def != null) {
                com.sun.tools.javac.util.Name enclClassNamePrev = enclClassName;
                enclClassName =
                        tree.def.name != null ? tree.def.name :
                            tree.type != null && tree.type.tsym.name != tree.type.tsym.name.table.names.empty
                                ? tree.type.tsym.name : null;
                if ((tree.def.mods.flags & Flags.ENUM) != 0) {
                    print("/*enum*/");
                }
                printBlock(tree.def.defs);
                enclClassName = enclClassNamePrev;
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void printPackStatement(Tree tree, String frame) throws IOException {
        AssertionSequence assertionsSeq = new AssertionSequence();

        println();

        List<VariableElement> allFields = enclClass.type == null
                ? List.of()
                : ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());
        for (VariableElement field : allFields) {
            if (!field.asType().getKind().isPrimitive()) {
                printlnAligned(String.format(
                        "//@ assume \\invariant_free_for(%s);",
                        field.getSimpleName()));
            }
        }
        for (LatticeVisitor.Result result : results) {
            List<VariableElement> uninitFields = result.getUninitializedFields(tree);
            for (VariableElement field : allFields) {
                if (!field.asType().getKind().isPrimitive()) {
                    printlnAligned(String.format(
                            "//@ assume %s;",
                            getPackedCondition(
                                    propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized()),
                                    field.getSimpleName().toString())));
                }

                AnnotatedTypeMirror type = result.getTypeFactory().getAnnotatedType(field);
                PropertyAnnotation pa = result.getLattice().getEffectivePropertyAnnotation(type);
                if (!pa.getAnnotationType().isTrivial()) {
                    Condition cond = new Condition(
                            !uninitFields.contains(field),
                            ConditionLocation.ASSERTION,
                            pa,
                            field.toString());
                    assertionsSeq.addClause(cond);
                }
            }
        }

        printlnAligned(assertionsSeq.toString());
        assertions += assertionsSeq.assertions.size();
        align();
        //TODO Workaround for KeY not supporting set statement for \TYPE variable because Recoder is terrible
        //print(String.format("//@ set packed = \\type(%s)", typeElement));
        println(String.format("havocPacked(); //@ assume packed == \\type(%s);", frame));
        align();
    }

    protected void printUnpackStatement(Tree tree, String frame) throws IOException {
        //TODO Workaround for KeY not supporting set statement for \TYPE variable because Recoder is terrible
        //print(String.format("//@ set packed = \\type(%s)", typeElement.getSuperclass()));
        println(String.format("havocPacked(); //@ assume packed == \\type(%s);", frame));
        align();
    }

    protected void printInferredPackingStatements(Tree tree) {
        try {
            TypeMirror unpackFrame = propertyFactory.getInferredUnpackFrame(tree);
            TypeMirror packFrame = propertyFactory.getInferredPackFrame(tree);
            if (unpackFrame != null) {
                printUnpackStatement(tree, unpackFrame.toString());
            } else if (packFrame != null) {
                printPackStatement(tree, packFrame.toString());
            }
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }
    }

    @Override
    public void visitApply(JCMethodInvocation tree) {
        if (tree.meth.toString().equals("super") || tree.meth.toString().equals("this")) {
            super.visitApply(tree);
            return;
        }

        try {
            printInferredPackingStatements(tree);

            // Explicit packing statement
            if (tree.meth.toString().equals("Packing.pack")) {
                printPackStatement(tree, TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression()).toString());
            } else if (tree.meth.toString().equals("Packing.unpack")) {
                printUnpackStatement(tree, ((TypeElement) TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression())).getSuperclass().toString());
            } else if (tree.meth.toString().equals("Ghost.ghost")) {
                JCLiteral type = (JCLiteral) tree.args.get(0);
                JCLiteral name = (JCLiteral) tree.args.get(1);
                JCLiteral value = (JCLiteral) tree.args.get(2);
                print(String.format("//@ ghost %s %s = %s", type.getValue(), name.getValue(), value.getValue()));
                return;
            } else if (tree.meth.toString().equals("Ghost.set")) {
                JCLiteral name = (JCLiteral) tree.args.get(0);
                JCLiteral value = (JCLiteral) tree.args.get(1);
                print(String.format("//@ set %s = %s", name.getValue(), value.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert.immutableFieldUnchanged") ||
                    (tree.meth.toString().equals("Assert.immutableFieldUnchanged_TranslationOnly") && TRANSLATION_RAW)) {
                JCLiteral immutableObject = (JCLiteral) tree.args.get(0);
                JCLiteral unchangedField = (JCLiteral) tree.args.get(1);
                print(String.format("//@ assume %s == \\old(%s) ==> %s == \\old(%s)",
                        immutableObject.getValue(), immutableObject.getValue(),
                        unchangedField.getValue(), unchangedField.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert.immutableFieldEqual") ||
                    (tree.meth.toString().equals("Assert.immutableFieldEqual_TranslationOnly") && TRANSLATION_RAW)) {
                JCLiteral immutableObject0 = (JCLiteral) tree.args.get(0);
                JCLiteral immutableObject1 = (JCLiteral) tree.args.get(1);
                JCLiteral equalField0 = (JCLiteral) tree.args.get(2);
                JCLiteral equalField1 = (JCLiteral) tree.args.get(3);
                print(String.format("//@ assume %s == \\old(%s) ==> %s == \\old(%s)",
                        immutableObject0.getValue(), immutableObject1.getValue(),
                        equalField0.getValue(), equalField1.getValue()));
                return;
            } else if ((tree.meth.toString().equals("Assert.immutableFieldUnchanged_TranslationOnly") && !TRANSLATION_RAW) ||
                    (tree.meth.toString().equals("Assert.immutableFieldEqual_TranslationOnly") && !TRANSLATION_RAW)) {
                return;
            } else if (tree.meth.toString().equals("Assert._assert")) {
                JCLiteral assertion = (JCLiteral) tree.args.get(0);
                print(String.format("//@ assert %s", assertion.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._assume")) {
                JCLiteral assertion = (JCLiteral) tree.args.get(0);
                print(String.format("//@ assume %s", assertion.getValue()));
                return;
            }

            AnnotatedExecutableType invokedMethod = propertyFactory.methodFromUse(tree).executableType;
            StringJoiner booleanArgs = new StringJoiner(", ");

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().methodFromUse(tree).executableType;

                if (!ElementUtils.isStatic(invokedMethod.getElement())) {
                    PropertyAnnotationType pat = wellTypedness.getLattice().getEffectivePropertyAnnotation(methodType.getReceiverType()).getAnnotationType();
                    if (!pat.isTrivial() && !pat.isInv()) {
                    	if (wellTypedness.getIllTypedMethodReceivers().contains(tree) || TRANSLATION_RAW) {
                    		booleanArgs.add("false");
                    		++methodCallPreconditions;
                    	} else {
                    		booleanArgs.add("true");
                    		++freeMethodCallPreconditions;
                    	}
                    }
                }

                for (int i = 0; i < invokedMethod.getParameterTypes().size(); ++i) {
                    AnnotatedTypeMirror paramType = methodType.getParameterTypes().get(i);
                    // TODO Don't add argument for type variable
                    // to be consistent with the (non-generic) declaration of the trampoline method
                    if (!(paramType instanceof AnnotatedTypeMirror.AnnotatedTypeVariable) &&
                            !wellTypedness.getLattice().getPropertyAnnotation(paramType).getAnnotationType().isTrivial()) {
                    	if (wellTypedness.getIllTypedMethodParams(tree).contains(i) || TRANSLATION_RAW) {
                    		booleanArgs.add("false");
                    		++methodCallPreconditions;
                    	} else {
                    		booleanArgs.add("true");
                    		++freeMethodCallPreconditions;
                    	}
                    }
                }
            }

            if (propertyFactory.getChecker().shouldNotUseTrampoline(((Symbol.MethodSymbol) invokedMethod.getElement()).owner.toString())) {
                super.visitApply(tree);
                return;
            }

            if (booleanArgs.length() == 0) {
                super.visitApply(tree);
                return;
            }
            
            if (tree.meth.hasTag(SELECT)) {
                JCFieldAccess left = (JCFieldAccess)tree.meth;
                printExpr(left.selected);
                print(".");
                print(trampolineName(left.name));
            } else {
                print(trampolineName(tree.meth.toString()));
            }

            print("(");
            printExprs(tree.args);

            if (!tree.args.isEmpty() && booleanArgs.length() != 0) {
                print(", ");
            }
            print(booleanArgs);
            print(")");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private boolean inForLoopInit = false;

    @Override
    public void visitForLoop(JCForLoop tree) {
        try {
            this.print("for (");
            inForLoopInit = true;
            if (tree.init.nonEmpty()) {
                if (tree.init.head.hasTag(Tag.VARDEF)) {
                    this.printExpr((JCTree)tree.init.head);

                    for(com.sun.tools.javac.util.List<JCTree.JCStatement> l = tree.init.tail; l.nonEmpty(); l = l.tail) {
                        JCTree.JCVariableDecl vdef = (JCTree.JCVariableDecl)l.head;
                        this.print(", ");
                        this.print(vdef.name);
                        if (vdef.init != null) {
                            this.print(" = ");
                            this.printExpr(vdef.init);
                        }
                    }
                } else {
                    this.printExprs(tree.init);
                }
            }

            this.print("; ");
            if (tree.cond != null) {
                this.printExpr(tree.cond);
            }

            this.print("; ");
            this.printExprs(tree.step);
            this.print(") ");
            inForLoopInit = false;
            this.printStat(tree.body);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitAssign(JCAssign tree) {
        printInferredPackingStatements(tree);

        String tempVar = tempVarName();
        List<Condition> conditions = getConditions(tree, tempVar, ConditionLocation.ASSERTION);

        // For readability, skip field assignments if they are not ill-typed (which can only happen with assignments
        // to committed fields).
        if (tree.getVariable() instanceof MemberSelectTree && !conditions.stream().anyMatch(cond -> cond.conditionType.equals(ConditionType.ASSERTION))) {
            super.visitAssign(tree);
            return;
        }

        //TODO This only works if the for loop's index var has top type; otherwise we must transform the for loop
        // into a while loop
        if (inForLoopInit) {
            super.visitAssign(tree);
            return;
        }


        visitAssignOrDef(
                tree.getVariable().toString(),
                unannotatedTypeNameLhs(tree.getVariable()),
                tree.getExpression(),
                getConditions(tree, tempVar, ConditionLocation.ASSERTION),
                tempVar);
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        printInferredPackingStatements(tree);

        if (enclMethod == null) {
            try {
                print("public ");
                if (tree.getModifiers().getFlags().contains(Modifier.STATIC)) {
                    print("static ");
                }
                println(String.format("%s %s;", unannotatedNullableTypeNameLhs(tree), tree.getName()));
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
            return;
        }

        //TODO This only works if the for loop's index var has top type; otherwise we must transform the for loop
        // into a while loop
        if (inForLoopInit) {
            super.visitVarDef(tree);
            return;
        }

        try {
            String tempVar = tempVarName();

            print(String.format("%s %s", unannotatedTypeNameLhs(tree), tree.getName()));
            if (prec == TreeInfo.notExpression) {
                println(";");
                align();
            }

            if (tree.getInitializer() != null) {
                visitAssignOrDef(
                        tree.getName().toString(),
                        unannotatedTypeNameLhs(tree),
                        tree.getInitializer(),
                        getConditions(tree, tempVar, ConditionLocation.ASSERTION),
                        tempVar);
                print(";");
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void visitAssignNoConditions(String varName, JCTree expression) {
        try {
            print(String.format("%s = ", varName));
            expression.accept(this);
            println(";");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void visitAssignOrDef(String varName, String unannotatedTypeName, JCTree expression, List<Condition> conditions, String tempVar) {
        try {
            print(String.format("%s %s = ", unannotatedTypeName, tempVar));
            expression.accept(this);
            println(";");

            for (Condition condition : conditions) {
                printlnAligned(condition);
                
                if (!condition.pa.getAnnotationType().isTrivial()) {
                    if (condition.conditionType == ConditionType.ASSERTION || TRANSLATION_RAW) {
                    	++assertions;
                    } else {
                    	++assumptions;
                    }
                }
            }

            align();
            print(String.format("%s = %s", varName, tempVar));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void printStaticInitializers() throws IOException {
        List<Union<StatementTree, VariableTree, BlockTree>> inits =
                results.get(0).getStaticInitializers(enclClass.sym.getQualifiedName().toString());
        
        if (inits.isEmpty()) {
            return;
        }
        
        printlnAligned("static {");
        indent();
        enclBlock = true;
        
        for (Union<StatementTree, VariableTree, BlockTree> init : inits) {
            align();
            init.consume(
                    var -> {
                        if (var.getInitializer() != null) {
                            String tempVar = tempVarName();

                            visitAssignOrDef(
                                    var.getName().toString(),
                                    unannotatedTypeNameLhs((JCVariableDecl) var),
                                    (JCTree) var.getInitializer(),
                                    getConditions((JCVariableDecl) var, tempVar, ConditionLocation.ASSERTION),
                                    tempVar);
                            try {
                                println(";");
                            } catch (IOException e) {
                                throw new AssertionError();
                            }
                        }
                    },
                    block -> {
                        ((JCBlock) block).accept(this);
                    });
            println();
        }

        enclBlock = false;
        undent();
        printlnAligned("}");
        println();
    }

    protected void printInstanceInitializers() throws IOException {
        List<Union<StatementTree, VariableTree, BlockTree>> inits =
                results.get(0).getInstanceInitializers(enclClass.sym.getQualifiedName().toString());
        for (Union<StatementTree, VariableTree, BlockTree> init : inits) {
            align();
            init.consume(
                    var -> {
                        visitAssignNoConditions(
                                var.getName().toString(),
                                (JCTree) var.getInitializer());
                    },
                    block -> {
                        ((JCBlock) block).accept(this);
                    });
            println();
        }
    }

    protected void printTrampoline(JCMethodDecl tree) {
        printTrampoline(tree, true);
    }
    
    protected void printTrampoline(JCMethodDecl tree, boolean printBody) {
        List<String> paramNames = tree.getParameters().stream().map(JCVariableDecl::getName).map(Object::toString).collect(Collectors.toList());

        StringJoiner paramStr = new StringJoiner(", ");
        for (int i = 0; i < paramNames.size(); ++i) {
            paramStr.add(String.format("%s %s", unannotatedNullableTypeNameLhs(tree.getParameters().get(i)), paramNames.get(i)));
        }
        for (LatticeVisitor.Result wellTypedness : results) {
            AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().getAnnotatedType(tree);
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
            List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

            if (requiredReceiverType != null) {
                PropertyAnnotationType pat = lattice.getEffectivePropertyAnnotation(requiredReceiverType).getAnnotationType();
                if (!pat.isTrivial() && !pat.isInv()) {
                    paramStr.add(String.format("boolean %s", trampolineBooleanParamName("this", wellTypedness)));
                }
            }

            for (int i = 0; i < paramNames.size(); ++i) {
                if (!lattice.getEffectivePropertyAnnotation(requiredParamTypes.get(i)).getAnnotationType().isTrivial()) {
                    paramStr.add(String.format("boolean %s", trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                }
            }
        }

        AnnotatedExecutableType propertyMethodType = propertyFactory.getAnnotatedType(tree);

        JMLContract jmlContract = new JMLContract(EnumSet.of(Flag.PUBLIC));
        //jmlContract.addClause("diverges true;");

        {
            List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
            List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);
            AnnotationMirror receiverInputType = inputPackingTypes.get(0);
            AnnotationMirror receiverOutputType = outputPackingTypes.get(0);

            if (receiverInputType != null && !isConstructor(tree)) {
                jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(receiverInputType, "this")));
            }

            if (receiverOutputType != null) {
                jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(receiverOutputType, "this")));
            }

            for (int i = 0; i < paramNames.size(); ++i) {
                if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                    jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(inputPackingTypes.get(i + 1), paramNames.get(i))));
                    jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(outputPackingTypes.get(i + 1), paramNames.get(i))));
                }
            }
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);
            List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

            if (methodType.getReceiverType() != null) {
                AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
                PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(requiredReceiverType);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial() && !pat.isInv()) {
                    jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this")
                            .toStringOr(trampolineBooleanParamName("this", wellTypedness)));
                    jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, "this")
                            .toStringOr("!" + trampolineBooleanParamName("this", wellTypedness)));
                }
            }

            for (int i = 0; i < requiredParamTypes.size(); ++i) {
                PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(requiredParamTypes.get(i));
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial()
                        && !AnnotationUtils.areSame(requiredParamTypes.get(i).getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                    jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                            .toStringOr(trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                    jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                            .toStringOr("!" + trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                }
            }
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID && !isConstructor(tree)) {
                AnnotatedTypeMirror returnType = wellTypedness.getTypeFactory().getMethodReturnType(tree);
                AnnotationMirror anno = returnType.getEffectiveAnnotationInHierarchy(getTop(wellTypedness.getTypeFactory()));

                if (anno != null && !AnnotationUtils.areSame(
                        anno,
                        getTop(wellTypedness.getTypeFactory()))) {
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if (!pat.isTrivial()) {
                        jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, "\\result").toString());
                    }
                }
            }

            if (factory instanceof NullnessLatticeAnnotatedTypeFactory) {
                // Nullness Checker
                Set<Contract> contracts = factory.getContractsFromMethod().getContracts(TreeUtils.elementFromDeclaration(tree));

                for (Contract contract : contracts) {
                    String exprStr = contract.expressionString;
                    JavaExpression exprJe;
                    try {
                        exprJe = StringToJavaExpression.atMethodBody(
                                exprStr, tree, factory.getChecker());
                    } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                        throw new UncheckedIOException("Cannot parse contract", new IOException(e));
                    }

                    if (contract.kind == Contract.Kind.POSTCONDITION) {
                        // @EnsuresNonNull(exprJe)
                        jmlContract.addClause(String.format(
                                "ensures_free %s != null;",
                                exprJe));
                    } else if (contract.kind == Contract.Kind.CONDITIONALPOSTCONDITION) {
                        // @EnsuresNonNullIf(exprJe, contractResult)
                        boolean contractResult = ((Contract.ConditionalPostcondition) contract).resultValue;
                        jmlContract.addClause(String.format(
                                "ensures_free %s ==> %s != null;",
                                contractResult ? "\\result" : "!\\result",
                                exprJe));
                    } else if (contract.kind == Contract.Kind.PRECONDITION) {
                        // @RequiresNonNull(exprJe)
                        jmlContract.addClause(String.format(
                                "requires %s != null;",
                                exprJe));
                    } else {
                        throw new AssertionError("unknown contract kind");
                    }
                }
            } else {
                // Lattice Subchecker
                List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                {
                    AnnotationMirror paramOutputType = methodOutputTypes.get(0);

                    if (paramOutputType != null && !AnnotationUtils.areSame(paramOutputType, getTop(factory))) {
                        jmlContract.addClause(
                                new Condition(
                                        true,
                                        ConditionLocation.POSTCONDITION,
                                        lattice.getPropertyAnnotation(paramOutputType),
                                        "this"));
                    }
                }
                for (int i = 0; i < methodType.getParameterTypes().size(); ++i) {
                    AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                    String paramName = paramNames.get(i);

                    if (!AnnotationUtils.areSame(paramOutputType, getTop(factory))) {
                        jmlContract.addClause(
                                new Condition(
                                        true,
                                        ConditionLocation.POSTCONDITION,
                                        lattice.getPropertyAnnotation(paramOutputType),
                                        paramName));
                    }
                }
            }
        }

        ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

        if (isConstructor(tree)) {
            jmlContract.addClause("ensures \\result != null && \\fresh(\\result) && \\invariant_free_for(\\result) && \\invariant_for(\\result);");
        } else if (!ElementUtils.isStatic(element)){
            jmlContract.addClause("ensures \\invariant_free_for(this);");
        }

        if (propertyFactory.isSideEffectFree(element)) {
            jmlContract.addClause("assignable \\nothing;");
        }

        for (String clause : getJMLClauseValues(element)) {
            if (isConstructor(tree) && clause.startsWith("assignable")) {
                jmlContract.addClause(clause.replace("this.*", "\\nothing"));
            } else {
                jmlContract.addClause(clause);
            }
        }

        if (TRANSLATION_RAW) {
            for (String clause : getJMLClauseValuesTranslationOnly(element)) {
                if (isConstructor(tree) && clause.startsWith("assignable")) {
                    jmlContract.addClause(clause.replace("this.*", "\\nothing"));
                } else {
                    jmlContract.addClause(clause);
                }
            }
        }

        if (isConstructor(tree)) {
            printlnAligned(jmlContract.toString().replace("this", "\\result"));
        } else {
            printlnAligned(jmlContract.toString());
        }

        if (printBody) {
            printlnAligned(String.format("public %s %s%s%s %s(%s) {",
                    ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                            propertyMethodType.getReturnType().getKind() == TypeKind.VOID || propertyMethodType.getReturnType().getKind().isPrimitive()
                                ? "" : "/*@nullable@*/ ",
                            isConstructor(tree) || results.stream().anyMatch(wt -> wt.getLattice().getIdent().equals("inv"))
                                ? "" : "/*@helper@*/ ",
                            unannotatedTypeName(propertyMethodType.getReturnType()),
                            trampolineName(tree.getName()),
                            paramStr));

            indent();

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID) {
                printlnAligned(String.format(
                        "return %s(%s);",
                        tree.getName().toString().equals("<init>") ? ("new " + getEnclClassName()) : tree.getName(),
                                String.join(", ", paramNames)
                        ));
            } else {
                printlnAligned(String.format("%s(%s);", tree.getName(), String.join(", ", paramNames)));
            }

            undent();
            printlnAligned("}");
        } else {
            printlnAligned(String.format("public %s %s%s%s %s(%s);",
                    ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                            propertyMethodType.getReturnType().getKind() == TypeKind.VOID || propertyMethodType.getReturnType().getKind().isPrimitive()
                                ? "" : "/*@nullable@*/ ",
                            isConstructor(tree) || results.stream().anyMatch(wt -> wt.getLattice().getIdent().equals("inv"))
                                ? "" : "/*@helper@*/ ",
                            unannotatedTypeName(propertyMethodType.getReturnType()),
                            trampolineName(tree.getName()),
                            paramStr));
        }
    }

    protected String trampolineName(String methodName) {
        if (methodName.equals("<init>")) {
            methodName = "INIT";
        }

        return String.format("__%s_trampoline", methodName.replace('.', '_'));
    }

    protected String trampolineName(Name methodName) {
        return trampolineName(methodName.toString());
    }

    protected String trampolineBooleanParamName(String paramName, LatticeVisitor.Result wellTypedness) {
        return String.format("%s_%s", paramName, wellTypedness.getLattice().getIdent());
    }

    protected String tempVarName() {
        return String.format("temp%d", tempVarNum++);
    }

    @SuppressWarnings("unchecked")
    protected List<String> getJMLClauseValues(Element element) {
        AnnotationMirror jmlClauses = propertyFactory.getDeclAnnotation(element, JMLClauses.class);
        AnnotationMirror jmlClause = propertyFactory.getDeclAnnotation(element, JMLClause.class);
        
        if (jmlClauses == null && jmlClause == null) {
            return Collections.emptyList();
        } else if (jmlClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(jmlClauses, "value", List.class, true).stream()
                .map(o -> {
                    String s = ((Attribute.Compound) o).values.head.snd.toString();
                    return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                })
                .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(jmlClause, "value", String.class, true));
        }
    }
    
    @SuppressWarnings("unchecked")
    protected List<String> getJMLClauseValuesTranslationOnly(Element element) {
        AnnotationMirror jmlClauses = propertyFactory.getDeclAnnotation(element, JMLClausesTranslationOnly.class);
        AnnotationMirror jmlClause = propertyFactory.getDeclAnnotation(element, JMLClauseTranslationOnly.class);
        
        if (jmlClauses == null && jmlClause == null) {
            return Collections.emptyList();
        } else if (jmlClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(jmlClauses, "value", List.class, true).stream()
                .map(o -> {
                    String s = ((Attribute.Compound) o).values.head.snd.toString();
                    return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                })
                .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(jmlClause, "value", String.class, true));
        }
    }

    protected String getPackedCondition(AnnotationMirror packingType, String varName) {
        if (propertyFactory.isInitialized(packingType)) {
            return String.format("%s.packed == \\typeof(%s)", varName, varName);
        } else if (propertyFactory.isUnderInitialization(packingType)) {
            return String.format("%s.packed == %s", varName, propertyFactory.getTypeFrameFromAnnotation(packingType));
        } else {
            return String.format("%s.packed <: %s", varName, propertyFactory.getTypeFrameFromAnnotation(packingType));
        }
    }

    protected void printlnAligned(JavaJMLPrinter.Condition cond) {
        PropertyAnnotationType pat = cond.pa.getAnnotationType();

        if (pat.isTrivial()) {
            return;
        }

        printlnAligned(cond.toString());
    }

    protected void println(JavaJMLPrinter.Condition cond) throws IOException {
        PropertyAnnotationType pat = cond.pa.getAnnotationType();

        if (pat.isTrivial()) {
            return;
        }

        println(cond.toString());
    }

    protected List<Condition> getConditions(JCAssign tree, String subject, ConditionLocation conditionLocation) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree.getVariable());

            if (type instanceof AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(type);
            (wt ? wellTyped : malTyped).add(new Condition(wt, conditionLocation, pa, subject));
        }

        return Streams.concat(wellTyped.stream(), malTyped.stream()).collect(Collectors.toList());
    }

    protected List<Condition> getConditions(JCVariableDecl tree, String subject, ConditionLocation conditionLocation) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree);

            if (type instanceof AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(factory.getAnnotatedTypeLhs(tree));
            (wt ? wellTyped : malTyped).add(new Condition(wt, conditionLocation, pa, subject));
        }

        return Streams.concat(wellTyped.stream(), malTyped.stream()).collect(Collectors.toList());
    }

    public enum ConditionLocation {
        ASSERTION, PRECONDITION, POSTCONDITION, INVARIANT_INSTANCE, INVARIANT_STATIC;
    }

    public enum ConditionType {
        ASSERTION, ASSUMPTION;
    }

    public static class Condition {

        protected ConditionLocation conditionLocation;
        protected ConditionType conditionType;
        protected PropertyAnnotation pa;
        protected String subject;
        
        public Condition(boolean wt, ConditionLocation conditionLocation, PropertyAnnotation pa, String subject) {
            this(wt ? ConditionType.ASSUMPTION : ConditionType.ASSERTION, conditionLocation, pa, subject);
        }

        public Condition(ConditionType conditionType, ConditionLocation conditionLocation, PropertyAnnotation pa, String subject) {
            this.conditionType = conditionType;
            this.conditionLocation = conditionLocation;
            this.pa = pa;
            this.subject = subject;
        }

        @Override
        public String toString() {
            return toStringAnd(null);
        }

        public String toStringAnd(String additionalCondition) {
            return toStringOp(additionalCondition, "&&");
        }

        public String toStringOr(String additionalCondition) {
            return toStringOp(additionalCondition, "||");
        }

        protected String toStringOp(String additionalCondition, String op) {
            PropertyAnnotationType pat = pa.getAnnotationType();

            StringBuilder sb = new StringBuilder();

            switch(conditionLocation) {
            case ASSERTION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ assert ");
                    break;
                case ASSUMPTION:
                    sb.append(TRANSLATION_RAW ? "//@ assert " :"//@ assume ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case PRECONDITION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("requires ");
                    break;
                case ASSUMPTION:
                    sb.append("requires_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case POSTCONDITION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("ensures ");
                    break;
                case ASSUMPTION:
                    sb.append(TRANSLATION_RAW ? "ensures " : "ensures_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case INVARIANT_INSTANCE:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ public invariant ");
                    break;
                case ASSUMPTION:
                    sb.append("//@ public invariant_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case INVARIANT_STATIC:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ public static invariant ");
                    break;
                case ASSUMPTION:
                    sb.append("//@ public static invariant_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            }

            if (additionalCondition != null) {
                sb.append(additionalCondition);
                sb.append(" ");
                sb.append(op);
                sb.append(" (");
            }

            sb.append(JavaJMLPrinter.printCheckable(pat.getWellFormednessCheckable(), pa, null));
            sb.append(" && ");

            sb.append(JavaJMLPrinter.printCheckable(pat.getPropertyCheckable(), pa, subject));

            if (additionalCondition != null) {
                sb.append(")");
            }

            sb.append(";");

            return sb.toString();
        }
    }

    public static class AssertionSequence {

        private List<String> assertions = new ArrayList<>();
        private List<String> assumptions = new ArrayList<>();

        public void addClause(Condition condition) {
            if (condition.pa.getAnnotationType().isTrivial()) {
                return;
            }

            switch (condition.conditionLocation) {
                case PRECONDITION:
                case POSTCONDITION:
                    throw new IllegalArgumentException("condition");
                case ASSERTION:
                    switch (condition.conditionType) {
                        case ASSERTION:
                            assertions.add(condition.toString());
                            break;
                        case ASSUMPTION:
                            assumptions.add(condition.toString());
                            break;
                    }
                    break;
            }
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            assumptions.forEach(c -> sb.append(String.format("%s\n", c)));
            assertions.forEach(c -> sb.append(String.format("%s\n", c)));
            return sb.toString();
        }
    }
    
    public static class JMLContract {
        
        private EnumSet<Flag> flags;

        private List<String> requiresClauses = new ArrayList<>();
        private List<String> requiresFreeClauses = new ArrayList<>();
        private List<String> ensuresClauses = new ArrayList<>();
        private List<String> ensuresFreeClauses = new ArrayList<>();
        private List<String> otherClauses = new ArrayList<>();
        
        public JMLContract(EnumSet<Flag> flags) {
            this.flags = flags;
        }

        public void addClause(Condition condition) {
            if (condition.pa.getAnnotationType().isTrivial()) {
                return;
            }
            
            switch (condition.conditionLocation) {
            case PRECONDITION:
                switch (condition.conditionType) {
                case ASSERTION:
                    requiresClauses.add(condition.toString());
                    break;
                case ASSUMPTION:
                    requiresFreeClauses.add(condition.toString());
                    break;
                }
                break;
            case POSTCONDITION:
                switch (condition.conditionType) {
                case ASSERTION:
                    ensuresClauses.add(condition.toString());
                    break;
                case ASSUMPTION:
                    ensuresFreeClauses.add(condition.toString());
                    break;
                }
                break;
            case ASSERTION:
                throw new IllegalArgumentException("condition");
            }
        }
        
        public void addClause(String clause) {
            String clauseKind = clause.strip().split("\\s+")[0];
            switch (clauseKind) {
            case "requires":
                requiresClauses.add(clause);
                break;
            case "requires_free":
                requiresFreeClauses.add(clause);
                break;
            case "ensures":
                ensuresClauses.add(clause);
                break;
            case "ensures_free":
                ensuresFreeClauses.add(clause);
                break;
            default:
                otherClauses.add(clause);
                break;
            }
        }
        
        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append(String.format("/*@ %s normal_behavior\n", getVisibilityString(flags)));
            
            requiresClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            requiresFreeClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            ensuresClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            ensuresFreeClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            otherClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));

            sb.append("  @*/");
            return sb.toString();
        }
    }
}
