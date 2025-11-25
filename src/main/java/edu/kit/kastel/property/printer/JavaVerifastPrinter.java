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

import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.checker.qual.VerifastClause;
import edu.kit.kastel.property.checker.qual.VerifastClauseTranslationOnly;
import edu.kit.kastel.property.checker.qual.VerifastClauses;
import edu.kit.kastel.property.checker.qual.VerifastClausesTranslationOnly;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.subchecker.nullness.NullnessLatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.util.FileUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.util.Contract;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.io.*;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.sun.tools.javac.code.Flags.ENUM;
import static com.sun.tools.javac.code.Flags.INTERFACE;

@SuppressWarnings("nls")
public class JavaVerifastPrinter extends PropertyCheckerPrettyPrinter {

    public JavaVerifastPrinter(
            List<LatticeVisitor.Result> results,
            PropertyChecker propertyChecker,
            BufferedWriter out) {
        super(results, propertyChecker, out);
    }

    private PredicateDef enclClassOwnFieldsPred;
    private PredicateDef enclClassFieldTypesPred;

    protected static String getOwnFieldsPredicateName(TypeMirror typeMirror) {
        return typeMirror.toString() + "_OwnFields";
    }

    protected static String getFieldTypesPredicateName(TypeMirror typeMirror) {
        return typeMirror.toString() + "_FieldTypes";
    }

    protected TypeMirror getTypeFrame(AnnotationMirror packingType, TypeMirror varType) {
        TypeMirror frame;
        if (propertyFactory.isInitialized(packingType)) {
            frame = varType;
        } else {
            frame = propertyFactory.getTypeFrameFromAnnotation(packingType);
        }
        return frame;
    }

    protected PredicateUse getOwnFieldsPredicateUse(AnnotationMirror packingType, TypeMirror varType, String varName, Function<VariableElement, String> fieldNamer) {
        TypeMirror frame = getTypeFrame(packingType, varType);
        List<String> args = new ArrayList<>();
        args.add(varName);
        nonStaticFieldsInFrame(frame).stream().filter(Predicate.not(ElementUtils::isStatic)).map(fieldNamer).forEach(args::add);
        return new PredicateUse(getOwnFieldsPredicateName(frame), args);
    }

    protected PredicateUse getOwnFieldsPredicateUse(AnnotationMirror packingType, VariableElement var, Function<VariableElement, String> fieldNamer) {
        return getOwnFieldsPredicateUse(packingType, var.asType(), var.getSimpleName().toString(), fieldNamer);
    }

    protected PredicateUse getFieldTypesPredicateUse(AnnotationMirror packingType, TypeMirror varType, String varName, Function<VariableElement, String> fieldNamer) {
        TypeMirror frame = getTypeFrame(packingType, varType);

        return new PredicateUse(
                getFieldTypesPredicateName(frame),
                nonStaticFieldsInFrame(frame).stream()
                        .filter(Predicate.not(ElementUtils::isStatic))
                        .map(fieldNamer).toList());
    }

    protected PredicateUse getFieldTypesPredicateUse(AnnotationMirror packingType, VariableElement var, Function<VariableElement, String> fieldNamer) {
        return getFieldTypesPredicateUse(packingType, var.asType(), var.getSimpleName().toString(), fieldNamer);
    }

    protected void printPredicatesForClass(JCClassDecl tree) {
        String containingClassName = tree.sym.getQualifiedName().toString();
        if (tree.type != null) {
            //TODO support static fields in Verifast
            List<VariableElement> allFields = nonStaticFieldsInFrame(tree.type);

            StringJoiner fieldTypesPredBody = new StringJoiner(" &*& ");

            for (VariableElement field : allFields) {
                if (!field.asType().getKind().isPrimitive()) {
                    AnnotationMirror packingType = propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
                    String fieldName = field.getSimpleName().toString();
                    fieldTypesPredBody.add(getOwnFieldsPredicateUse(packingType, field, f -> "?" + fieldName + "_" + f.getSimpleName()).toString());
                    fieldTypesPredBody.add(getFieldTypesPredicateUse(packingType, field, f -> fieldName + "_" + f.getSimpleName()).toString());
                }
            }

            for (LatticeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();

                for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                    //TODO support static invariants in Verifast
                }

                for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(invariant.getType());
                    String fieldName = invariant.getFieldName();
                    fieldTypesPredBody.add(new PredicateUse(pa, fieldName, f -> fieldName + "_" + f.getSimpleName()).toString());
                }
            }

            List<PredicateParameter> fieldParameters = allFields.stream().map(PredicateParameter::new).toList();

            StringJoiner ownFieldsPredBody = new StringJoiner(" &*& ");
            fieldParameters.forEach(f -> ownFieldsPredBody.add(String.format("subject.%s |-> %s", f.paramName, f.paramName)));

            enclClassOwnFieldsPred = new PredicateDef(
                    getOwnFieldsPredicateName(tree.type),
                    List.of(new PredicateParameter(tree.name.toString(), "subject")),
                    fieldParameters,
                    ownFieldsPredBody.toString()
            );
            enclClassFieldTypesPred = new PredicateDef(
                    getFieldTypesPredicateName(tree.type),
                    fieldParameters,
                    List.of(),
                    fieldTypesPredBody.toString()
            );

            printlnAligned(enclClassOwnFieldsPred.toString());
            printlnAligned(enclClassFieldTypesPred.toString());
        }
    }

    @Override
    public void visitClassDef(JCClassDecl tree) {
        try {
            println();
            align();

            printPredicatesForClass(tree);
            println();

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

                if (!isInterface(tree)) {
                    //TODO support static initialiters in Verifast
                    //printStaticInitializers();
                }

                println();
                getVerifastClauseValues(enclClass.sym).forEach(c -> printlnAligned("//@ " + c));
                if (TRANSLATION_RAW) {
                    getVerifastClauseValuesTranslationOnly(enclClass.sym).forEach(c -> printlnAligned("//@ " + c));
                }

                println();

                for (JCTree def : tree.defs) {
                    align();
                    def.accept(this);
                    println();
                }

                TODO
                //print generated methods here

                undent();
                printlnAligned("}");
            }

            enclClass = enclClassPrev;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitMethodDef(JCTree.JCMethodDecl tree) {
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

            JCTree.JCMethodDecl prevEnclMethod = enclMethod;
            enclMethod = tree;
            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

            VerifastContract verifastContract = new VerifastContract(true, false);

            {
                List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
                List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);

                if (!inputPackingTypes.isEmpty() ) {
                    {
                        AnnotationMirror receiverInputType = inputPackingTypes.get(0);
                        if (receiverInputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                            receiverInputType = propertyFactory.getInitialized();
                        }
                        if (receiverInputType != null) {
                            VariableElement el = TreeUtils.elementFromDeclaration(tree.getReceiverParameter());
                            verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                                    receiverInputType, el, f -> "?this_" + f.getSimpleName() + "_r"));
                            verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                                    receiverInputType, el, f -> "this_" + f.getSimpleName() + "_r"));
                        }
                    }

                    {

                        AnnotationMirror receiverOutputType = outputPackingTypes.get(0);
                        if (receiverOutputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                            receiverOutputType = propertyFactory.getInitialized();
                        }
                        if (receiverOutputType != null) {
                            VariableElement el = TreeUtils.elementFromDeclaration(tree.getReceiverParameter());
                            verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                    receiverOutputType, el, f -> "?this_" + f.getSimpleName() + "_e"));
                            verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                    receiverOutputType, el, f -> "this_" + f.getSimpleName() + "_e"));
                        }
                    }

                    for (CooperativeVisitor.Result wellTypedness : results) {
                        GenericAnnotatedTypeFactory<?, ?, ?, ?> factory = wellTypedness.getTypeFactory();
                        Lattice lattice = wellTypedness.getLattice();
                        AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                        AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();
                        List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                        AnnotationMirror receiverOutputType = methodOutputTypes.get(0);
                        Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                        boolean outputWt = !illTypedMethodOutputParams.contains(0);

                        verifastContract.addRequiresPred(new PredicateUse(lattice.getEffectivePropertyAnnotation(requiredReceiverType), f -> "this_" + f.getSimpleName() + "_r"));

                        if (!outputWt && !AnnotationUtils.areSame(receiverOutputType, getTop(factory))) {
                            verifastContract.addEnsuresPred(new PredicateUse(lattice.getPropertyAnnotation(receiverOutputType), f -> "this_" + f.getSimpleName() + "_r"));
                        }
                        if (!outputWt) {
                            ++methodCallPostconditions;
                        } else {
                            ++freeMethodCallPostconditions;
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

                        if (!wt) {
                            verifastContract.addEnsuresPred(new PredicateUse(pa, f -> "this_" + f.getSimpleName() + "_e"));
                            ++methodCallPostconditions;
                        }
                    }
                } else {
                    {
                        AnnotatedTypeMirror returnType = propertyFactory.getMethodReturnType(enclMethod);
                        if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                                && returnType.getKind() != TypeKind.VOID
                                && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)), getTop(propertyFactory))) {
                            verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                    returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                    returnType.getUnderlyingType(), "result",
                                    f -> "?result_" + f.getSimpleName() + "_e"));
                            verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                    returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                    returnType.getUnderlyingType(), "result",
                                    f -> "result_" + f.getSimpleName() + "_e"));
                        }
                    }

                    for (LatticeVisitor.Result wellTypedness : results) {
                        Lattice lattice = wellTypedness.getLattice();
                        GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                        AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

                        if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                                && returnType.getKind() != TypeKind.VOID
                                && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                            boolean wt = wellTypedness.isWellTypedMethodResult(tree);
                            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);

                            if (!wt) {
                                verifastContract.addEnsuresPred(new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                                ++methodCallPostconditions;
                            } else {
                                ++freeMethodCallPostconditions;
                            }
                        }
                    }
                }

                for (int i = 0; i < tree.getParameters().size(); ++i) {
                    if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                        VariableTree param = tree.getParameters().get(i);
                        String paramName = param.getName().toString();
                        VariableElement el = TreeUtils.elementFromDeclaration(param);

                        verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_r"
                        ));
                        verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                        ));
                        verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                outputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_e"
                        ));
                        verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                outputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_e"
                        ));

                        for (CooperativeVisitor.Result wellTypedness : results) {
                            GenericAnnotatedTypeFactory<?, ?, ?, ?> factory = wellTypedness.getTypeFactory();
                            Lattice lattice = wellTypedness.getLattice();
                            AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                            AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                            List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                            AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                            Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                            boolean outputWt = !illTypedMethodOutputParams.contains(i + 1);

                            if (!AnnotationUtils.areSame(paramType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                                verifastContract.addRequiresPred(new PredicateUse(lattice.getEffectivePropertyAnnotation(paramType), paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));

                                if (!outputWt && !AnnotationUtils.areSame(paramOutputType, getTop(factory))) {
                                    verifastContract.addEnsuresPred(new PredicateUse(lattice.getPropertyAnnotation(paramOutputType), paramName, f -> paramName + "_" + f.getSimpleName() + "_e"));
                                }
                                if (!outputWt) {
                                    ++methodCallPostconditions;
                                } else {
                                    ++freeMethodCallPostconditions;
                                }
                            }
                        }
                    }
                }
            }

            //TODO
            //support for Nullness Checker contract annotations in Verifast

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
            } else {
                TypeKind k = propertyFactory.getAnnotatedType(tree).getReturnType().getKind();
                if (tree.restype.type instanceof Type.TypeVar && !propertyFactory.getChecker().shouldKeepGenerics()) {
                    print("Object");
                } else {
                    printExpr(tree.restype);
                }
                print(" " + tree.name);
            }

            print("(");

            StringJoiner paramsStr = new StringJoiner(", ");
            for (JCTree.JCVariableDecl param : tree.params) {
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

            indent();
            printlnAligned(verifastContract.toString());
            getVerifastClauseValues(element).forEach(this::printlnAligned);
            if (TRANSLATION_RAW) {
                getVerifastClauseValuesTranslationOnly(element).forEach(this::printlnAligned);
            }
            undent();

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
                        JCTree.JCStatement statement = tree.body.stats.get(i);

                        align();
                        printStat(statement);
                        println();
                    }
                } else {
                    for (JCTree.JCStatement statement : tree.body.stats) {
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

    protected void printTrampoline(JCTree.JCMethodDecl tree) {
        printTrampoline(tree, true);
    }

    protected void printTrampoline(JCTree.JCMethodDecl tree, boolean printBody) {
        try {
            VerifastContract verifastContract = new VerifastContract(true, true);
            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

            {
                List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
                List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);

                if (!inputPackingTypes.isEmpty() ) {
                    {
                        AnnotationMirror receiverInputType = inputPackingTypes.get(0);
                        if (receiverInputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                            receiverInputType = propertyFactory.getInitialized();
                        }
                        if (receiverInputType != null) {
                            VariableElement el = TreeUtils.elementFromDeclaration(tree.getReceiverParameter());
                            verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                                    receiverInputType, el, f -> "?this_" + f.getSimpleName() + "_r"));
                            verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                                    receiverInputType, el, f -> "this_" + f.getSimpleName() + "_r"));
                        }
                    }

                    {

                        AnnotationMirror receiverOutputType = outputPackingTypes.get(0);
                        if (receiverOutputType == null && !ElementUtils.isStatic(element) && !isConstructor(tree)) {
                            receiverOutputType = propertyFactory.getInitialized();
                        }
                        if (receiverOutputType != null) {
                            VariableElement el = TreeUtils.elementFromDeclaration(tree.getReceiverParameter());
                            verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                    receiverOutputType, el, f -> "?this_" + f.getSimpleName() + "_e"));
                            verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                    receiverOutputType, el, f -> "this_" + f.getSimpleName() + "_e"));
                        }
                    }

                    for (CooperativeVisitor.Result wellTypedness : results) {
                        GenericAnnotatedTypeFactory<?, ?, ?, ?> factory = wellTypedness.getTypeFactory();
                        Lattice lattice = wellTypedness.getLattice();
                        AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                        AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();
                        List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                        AnnotationMirror receiverOutputType = methodOutputTypes.get(0);
                        Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);

                        verifastContract.addRequiresPred(new PredicateUse(lattice.getEffectivePropertyAnnotation(requiredReceiverType), f -> "this_" + f.getSimpleName() + "_r"));
                        verifastContract.addEnsuresPred(new PredicateUse(lattice.getPropertyAnnotation(receiverOutputType), f -> "this_" + f.getSimpleName() + "_r"));
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
                        PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(receiverType);
                        verifastContract.addEnsuresPred(new PredicateUse(pa, f -> "this_" + f.getSimpleName() + "_e"));
                    }
                } else {
                    {
                        AnnotatedTypeMirror returnType = propertyFactory.getMethodReturnType(enclMethod);
                        if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                                && returnType.getKind() != TypeKind.VOID
                                && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)), getTop(propertyFactory))) {
                            verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                    returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                    returnType.getUnderlyingType(), "result",
                                    f -> "?result_" + f.getSimpleName() + "_e"));
                            verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                    returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                    returnType.getUnderlyingType(), "result",
                                    f -> "result_" + f.getSimpleName() + "_e"));
                        }
                    }

                    for (LatticeVisitor.Result wellTypedness : results) {
                        Lattice lattice = wellTypedness.getLattice();
                        GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                        AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

                        if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                                && returnType.getKind() != TypeKind.VOID
                                && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);
                            verifastContract.addEnsuresPred(new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                        }
                    }
                }

                for (int i = 0; i < tree.getParameters().size(); ++i) {
                    if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                        VariableTree param = tree.getParameters().get(i);
                        String paramName = param.getName().toString();
                        VariableElement el = TreeUtils.elementFromDeclaration(param);

                        verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_r"
                        ));
                        verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                        ));
                        verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                                outputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_e"
                        ));
                        verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                                outputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_e"
                        ));

                        for (CooperativeVisitor.Result wellTypedness : results) {
                            GenericAnnotatedTypeFactory<?, ?, ?, ?> factory = wellTypedness.getTypeFactory();
                            Lattice lattice = wellTypedness.getLattice();
                            AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                            AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                            List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                            AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                            Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);

                            if (!AnnotationUtils.areSame(paramType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                                verifastContract.addRequiresPred(new PredicateUse(lattice.getEffectivePropertyAnnotation(paramType), paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                                verifastContract.addEnsuresPred(new PredicateUse(lattice.getPropertyAnnotation(paramOutputType), paramName, f -> paramName + "_" + f.getSimpleName() + "_e"));
                            }
                        }
                    }
                }
            }

            //TODO
            //support for Nullness Checker contract annotations in Verifast

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
            } else {
                TypeKind k = propertyFactory.getAnnotatedType(tree).getReturnType().getKind();
                if (tree.restype.type instanceof Type.TypeVar && !propertyFactory.getChecker().shouldKeepGenerics()) {
                    print("Object");
                } else {
                    printExpr(tree.restype);
                }
                print(" " + tree.name);
            }

            print("(");

            StringJoiner paramsStr = new StringJoiner(", ");
            for (JCTree.JCVariableDecl param : tree.params) {
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

            indent();
            printlnAligned(verifastContract.toString());
            getVerifastClauseValues(element).forEach(this::printlnAligned);
            if (TRANSLATION_RAW) {
                getVerifastClauseValuesTranslationOnly(element).forEach(this::printlnAligned);
            }
            undent();

            if (printBody) {
                println("{}");
            } else {
                println(";");
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @SuppressWarnings("unchecked")
    protected List<String> getVerifastClauseValues(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastClauses.class);
        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastClause.class);

        if (verifastClauses == null && verifastClause == null) {
            return Collections.emptyList();
        } else if (verifastClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(verifastClauses, "value", List.class, true).stream()
                    .map(o -> {
                        String s = ((Attribute.Compound) o).values.head.snd.toString();
                        return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                    })
                    .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(verifastClause, "value", String.class, true));
        }
    }

    @SuppressWarnings("unchecked")
    protected List<String> getVerifastClauseValuesTranslationOnly(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastClausesTranslationOnly.class);

        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastClauseTranslationOnly.class);

        if (verifastClauses == null && verifastClause == null) {
            return Collections.emptyList();
        } else if (verifastClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(verifastClauses, "value", List.class, true).stream()
                    .map(o -> {
                        String s = ((Attribute.Compound) o).values.head.snd.toString();
                        return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                    })
                    .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(verifastClause, "value", String.class, true));
        }
    }

    public static final String PREDICATE_PKG_NAME = "_predicates";
    public static final String PREDICATE_CLASS_NAME = "_Predicates";

    public static class PredicatePrinter {

        private List<Lattice> lattices;
        String outputDir;

        public PredicatePrinter(List<Lattice> lattices, String outputDir) throws IOException {
            this.lattices = lattices;
            this.outputDir = outputDir;
        }

        public void printPredicates() throws IOException {
            File file = Paths.get(outputDir, PREDICATE_PKG_NAME, PREDICATE_CLASS_NAME + ".java").toFile();
            file.getParentFile().mkdirs();
            FileUtils.createFile(file);

            try(BufferedWriter out = new BufferedWriter(new FileWriter(file))) {
                out.write("package " + PREDICATE_PKG_NAME + ";\n\n");

                for (Lattice lattice : lattices) {
                    for (PropertyAnnotationType pat : lattice.getAnnotationTypes().values()) {
                        String name = pat.getName();
                        String args = pat.getParameters().stream().reduce(
                                new StringJoiner(", " + pat.getSubjectType().toString() + " subject, "),
                                (sj, param) -> sj.add(param.getType().toString() + " " + param.getName()),
                                StringJoiner::merge).toString();
                        String body = pat.getWFCondition() + "&*&" + pat.getProperty();
                        out.write(String.format("//@ predicate %s(%s) = %s;", name, args, body));
                    }
                }
            } catch (IOException e) {
                throw e;
            }
        }

        public void printJarsrc() {
            //TODO
        }
    }

    public static class VerifastContract {

        private VerifastClause requiresClause;
        private VerifastClause ensuresClause;

        public VerifastContract(boolean requiresPermission, boolean ensuresPermission) {
            this.requiresClause = new VerifastClause("requires", requiresPermission);
            this.ensuresClause = new VerifastClause("ensures", ensuresPermission);
        }

        public void addRequiresPred(PredicateUse req) {
            requiresClause.add(req);
        }

        public void addEnsuresPred(PredicateUse ens) {
            ensuresClause.add(ens);
        }

        public void addRequiresPreds(Collection<PredicateUse> reqs) {
            requiresClause.addAll(reqs);
        }

        public void addEnsuresPreds(Collection<PredicateUse> enss) {
            ensuresClause.addAll(enss);
        }

        @Override
        public String toString() {
            return requiresClause.toString() + "\n" + ensuresClause.toString();
        }
    }

    public static class VerifastClause {

        private String clauseType;
        private boolean permission;
        private List<PredicateUse> preds = new ArrayList<>();

        public VerifastClause(String clauseType) {
            this(clauseType, true);
        }

        public VerifastClause(String clauseType, boolean permission) {
            this.clauseType = clauseType;
            this.permission = permission;
        }

        public void add(PredicateUse pred) {
            this.preds.add(pred);
        }

        public void addAll(Collection<PredicateUse> preds) {
            this.preds.addAll(preds);
        }

        @Override
        public String toString() {
            StringJoiner sj = new StringJoiner(" &*& ");
            if (permission) {
                preds.stream().map(PredicateUse::toString).forEach(sj::add);
            } else {
                preds.stream().forEach(p -> sj.add("[_](" + p + ")"));
            }
            return "//@ " + clauseType + " " + sj + ";";
        }
    }

    public static class PredicateParameter {

        protected String typeName;
        protected String paramName;

        public PredicateParameter(PropertyAnnotationType.Parameter param) {
            this.typeName = param.getType().toString();
            this.paramName = param.getName();
        }

        public PredicateParameter(String typeName, String paramName) {
            this.typeName = typeName;
            this.paramName = paramName;
        }

        public PredicateParameter(VariableElement f) {
            this.typeName = f.asType().toString();
            this.paramName = f.getSimpleName().toString();
        }

        public String getTypeName() {
            return typeName;
        }

        public String getParamName() {
            return paramName;
        }
    }

    public static class PredicateUse {

        protected String name;
        protected List<String> args;

        /**
         * Constructs a predicate use with the given predicate names and arguments.
         *
         * @param name
         * @param args
         */
        public PredicateUse(String name, List<String> args) {
            this.name = name;
            this.args = args;
        }

        /**
         * Constructs a predicate use from the given property annotation and arguments.
         *
         * @param pa the property annotation corresponding to the predicate use
         * @param subject the subject argument; only used if {@code pa}'s subject type is primitive
         * @param fieldNamer a function supplying a name for every field argument; only used if {@code pa}'s subject
         *                     type is not primitive
         */
        public PredicateUse(PropertyAnnotation pa, String subject, Function<VariableElement, String> fieldNamer) {
            PropertyAnnotationType pat = pa.getAnnotationType();
            this.name = pat.getName();
            this.args = new ArrayList<>();

            if (pat.getSubjectType().getKind().isPrimitive()) {
                args.add(subject);
            } else {
                List<VariableElement> fields = nonStaticFieldsInFrame(pat.getSubjectType());
                fields.stream().map(fieldNamer).forEach(this.args::add);
            }
            pa.getActualParameters().forEach(this.args::add);
        }

        /**
         * Constructs a predicate use for a predicate with primitive subject type.
         *
         * @param pa the property annotation corresponding to the predicate use
         * @param subject the subject argument
         */
        public PredicateUse(PropertyAnnotation pa, String subject) {
            this(pa, subject, null);
        }

        /**
         * Constructs a predicate use for a predicate with reference subject type.
         *
         * @param pa the property annotation corresponding to the predicate use
         * @param fieldNamer a function supplying a name for every field argument
         */
        public PredicateUse(PropertyAnnotation pa, Function<VariableElement, String> fieldNamer) {
            this(pa, null, fieldNamer);
        }

        @Override
        public String toString() {
            StringJoiner sj = new StringJoiner(", ", name + "(", ")");
            args.forEach(sj::add);
            return sj.toString();
        }
    }

    public static class PredicateDef {

        protected String name;
        protected List<PredicateParameter> inParams;
        protected List<PredicateParameter> outParams;
        protected String body;

        protected static List<PredicateParameter> inParams(PropertyAnnotationType pat) {
            List<PredicateParameter> res = new ArrayList<>();
            if (pat.getSubjectType().getKind().isPrimitive()) {
                res.add(new PredicateParameter(pat.getSubjectType().toString(), "subject"));
            } else {
                List<VariableElement> fields = nonStaticFieldsInFrame(pat.getSubjectType());
                fields.removeIf(ElementUtils::isStatic);
                fields.forEach(f -> res.add(new PredicateParameter(f)));
            }
            pat.getParameters().forEach(p -> res.add(new PredicateParameter(p)));
            return res;
        }

        public PredicateDef(String name, PropertyAnnotationType pat) {
            this(
                    name,
                    inParams(pat),
                    List.of(),
                    pat.getWFCondition() + "&*&" + pat.getProperty()
            );
        }

        public PredicateDef(String name, List<PredicateParameter> inParams, List<PredicateParameter> outParams, String body) {
            this.name = name;
            this.inParams = inParams;
            this.outParams = outParams;
            this.body = body;
        }

        @Override
        public String toString() {
            String res = "//@ predicate ";
            res += name;
            StringJoiner inParamsStr = new StringJoiner(", ");
            for (PredicateParameter param : inParams) {
                inParamsStr.add(param.getTypeName() + " " + param.getParamName());
            }
            StringJoiner outParamsStr = new StringJoiner(", ");
            for (PredicateParameter param : outParams) {
                outParamsStr.add(param.getTypeName() + " " + param.getParamName());
            }
            res += "(" + inParamsStr.toString() + "; " + outParamsStr.toString() + ")";
            res += " = ";
            res += body;
            res += ";";
            return res;
        }
    }
}
