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

import com.sun.source.tree.*;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.TreeInfo;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.subchecker.lattice.CooperativeVisitor;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import edu.kit.kastel.property.util.Pair;
import edu.kit.kastel.property.util.Union;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
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
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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

    protected int enclClassAssertionSequenceCounter;
    protected int enclClassAssumptionCounter;

    private List<JCTree.JCMethodDecl> enclClassTrampolinesToGenerate;
    private List<Pair<TypeMirror, VerifastContract>> enclClassAssumptionsToGenerate;

    protected String getOwnFieldsPredicateName(TypeMirror typeMirror) {
        return unannotatedSimpleTypeName(typeMirror, false).toString() + "_OwnFields";
    }

    protected String getFieldTypesPredicateName(TypeMirror typeMirror) {
        return unannotatedSimpleTypeName(typeMirror, false).toString() + "_FieldTypes";
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

    protected String fieldTypesPredBody(
            JCClassDecl tree,
            Function<VariableElement, String> fieldNamer,
            BiFunction<VariableElement, VariableElement, String> fieldOfFieldNamer,
            Function<String, String> typeArgTransformer) {
        String containingClassName = tree.sym.getQualifiedName().toString();
        if (tree.type == null) {
            return null;
        }
        //TODO support static fields in Verifast
        List<VariableElement> allFields = nonStaticFieldsInFrame(tree.type);

        VerifastClause fieldTypesPredBody = new VerifastClause(null, true);

        for (VariableElement field : allFields) {
            String name = fieldNamer.apply(field);
            if (field.asType().getKind().isPrimitive()) {
                fieldTypesPredBody.addVar(name, null);
                continue;
            }

            fieldTypesPredBody.addVar(name, name + " != null");

            if (unannotatedTypeName(field.asType(), false).startsWith("java.")) {
                // Don't create OwnFields and FieldTypes predicates for library types
                // TODO add cmd option to customize this behavior
                continue;
            }

            if (field.asType().getKind().equals(TypeKind.TYPEVAR)) {
                // Don't create OwnFields and FieldTypes predicates for type variables
                // TODO is this always right?
                continue;
            }

            AnnotationMirror packingType = propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
            PredicateUse ownFields = getOwnFieldsPredicateUse(packingType, field.asType(), name, f -> "?" + fieldOfFieldNamer.apply(field, f));
            PredicateUse fieldsOfFieldTypes = getFieldTypesPredicateUse(packingType, field.asType(), name, f -> fieldOfFieldNamer.apply(field, f));
            fieldTypesPredBody.addVarPred(name, ownFields);
            fieldTypesPredBody.addVarPred(name, fieldsOfFieldTypes);
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            Lattice lattice = wellTypedness.getLattice();

            for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                //TODO support static invariants in Verifast
            }

            for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(invariant.getType());
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isInv() && !pat.isTrivial()) {
                    VariableElement field = invariant.getField();
                    String name = fieldNamer.apply(field);

                    if (pat.isNonNull()) {
                        if (!field.asType().getKind().isPrimitive()) {
                            fieldTypesPredBody.setGuard(name, null);
                            fieldTypesPredBody.addBefore(new PredicateUse(pa, name, f -> fieldOfFieldNamer.apply(field, f), typeArgTransformer));
                        }
                    } else {
                        fieldTypesPredBody.addVarPred(name, new PredicateUse(pa, name, f -> fieldOfFieldNamer.apply(field, f), typeArgTransformer));
                    }
                }
            }
        }

        return fieldTypesPredBody.toString(false);
    }

    protected String ownFieldsPredBody(JCClassDecl tree, String subject, Function<VariableElement, String> fieldNamer) {
        if (tree.type == null) {
            return null;
        }
        List<VariableElement> allFields = nonStaticFieldsInFrame(tree.type);
        StringJoiner ownFieldsPredBody = new StringJoiner(" &*& ");
        allFields.forEach(f -> ownFieldsPredBody.add(String.format("%s.%s |-> %s", subject, f.getSimpleName(), fieldNamer.apply(f))));
        return ownFieldsPredBody.toString();
    }

    protected void printPredicatesForClass(JCClassDecl tree) {
        if (tree.type != null) {
            //TODO support static fields in Verifast
            List<VariableElement> allFields = nonStaticFieldsInFrame(tree.type);
            List<PredicateParameter> fieldParameters = allFields.stream().map(PredicateParameter::new).toList();
            String fieldTypesPredBody = fieldTypesPredBody(tree, f -> f.getSimpleName().toString(), (f,ff) -> f.getSimpleName() + "_" + ff.getSimpleName(), Function.identity());
            String ownFieldsPredBody = ownFieldsPredBody(tree, "subject", f -> f.getSimpleName().toString());

            enclClassOwnFieldsPred = new PredicateDef(
                    getOwnFieldsPredicateName(tree.type),
                    List.of(new PredicateParameter(tree.name.toString(), "subject")),
                    fieldParameters,
                    ownFieldsPredBody.length() == 0 ? "true" : ownFieldsPredBody.toString()
            );
            enclClassFieldTypesPred = new PredicateDef(
                    getFieldTypesPredicateName(tree.type),
                    fieldParameters,
                    List.of(),
                    fieldTypesPredBody.length() == 0 ? "true" : fieldTypesPredBody.toString()
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
            printFlags(tree.mods.flags & ~Flags.INTERFACE);

            JCClassDecl enclClassPrev = enclClass;
            enclClass = tree;

            enclClassTrampolinesToGenerate = new ArrayList<>();
            enclClassAssumptionsToGenerate = new ArrayList<>();
            enclClassAssertionSequenceCounter = 0;
            enclClassAssumptionCounter = 0;

            if (isInterface(tree)) {
                print("interface " + tree.name);
                printTypeParameters(tree.typarams);
                if (tree.implementing.nonEmpty()) {
                    print(" extends ");
                    printExprs(tree.implementing);
                }
            } else {
                if ((tree.mods.flags & Flags.ENUM) != 0) {
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

            if ((tree.mods.flags & Flags.ENUM) != 0) {
                printEnumBody(tree.defs);
            } else {
                println(" {");
                indent();

                if (!isInterface(tree)) {
                    //TODO support static initialiters in Verifast
                    //printStaticInitializers();
                }

                println();

                for (JCTree def : tree.defs) {
                    align();
                    def.accept(this);
                    println();
                }

                println();
                println("// GENERATED METHODS; UNPROVABLE");
                println();

                if (isInterface(enclClass)) {
                    for (JCTree.JCMethodDecl method : enclClassTrampolinesToGenerate) {
                        println();
                        printTrampoline(method, false);
                    }
                } else {
                    for (JCTree.JCMethodDecl method : enclClassTrampolinesToGenerate) {
                        println();
                        printTrampoline(method, true);
                    }
                }
                for (int i = 0; i < enclClassAssumptionCounter; ++i) {
                    Pair<TypeMirror, VerifastContract> assumption = enclClassAssumptionsToGenerate.get(i);

                    if (assumption.second == null) {
                        continue;
                    }

                    println();
                    printlnAligned(String.format("public static void assume%s(%s arg)", i, unannotatedSimpleTypeName(assumption.first, false)));
                    indent();
                    printlnAligned(assumption.second.toString());
                    undent();
                    if (isInterface(enclClass)) {
                        printlnAligned(";");
                    } else {
                        printlnAligned("{}");
                    }
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

            VerifastContract verifastContract = contractForMethod(tree, false);

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
                paramsStr.add(unannotatedSimpleTypeName(param) + " " + param.getName());
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

            println();
            indent();
            printlnAligned(verifastContract.toString());
            undent();

            if (tree.body != null) {
                printlnAligned("{");
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
                        printUnpackStatement(enclMethod, unannotatedSimpleTypeName(unpackFrame, false));
                    } else if (packFrame != null) {
                        printPackStatement(enclMethod, unannotatedSimpleTypeName(packFrame, false));
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
                enclClassTrampolinesToGenerate.add(tree);
            } else if (isInterface(enclClass)) {
                enclClassTrampolinesToGenerate.add(tree);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void addTypesToContract(VerifastContract verifastContract, JCTree.JCMethodDecl tree, boolean trampoline) {
        ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();
        List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
        List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);

        if (!ElementUtils.isStatic(element) && !isConstructor(tree) && !inputPackingTypes.isEmpty()) {
            AnnotationMirror receiverInputType = inputPackingTypes.get(0);
            if (receiverInputType == null) {
                receiverInputType = propertyFactory.getInitialized();
            }

            if (receiverInputType != null) {
                AnnotatedTypeMirror receiverType;
                if (isConstructor(tree)) {
                    receiverType = propertyFactory.getMethodReturnType(tree);
                } else {
                    receiverType = propertyFactory.getAnnotatedType(tree).getReceiverType();
                }

                // Open OwnFields and FieldTypes predicates of receiver directly to avoid errors when verifying the
                // method body.
                // But leave them closed in trampoline methods to avoid missing heap chunks in callers.
                if (trampoline) {
                    verifastContract.getRequiresClause().addBefore(getOwnFieldsPredicateUse(
                            receiverInputType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_r"));
                    verifastContract.getRequiresClause().addBefore(getFieldTypesPredicateUse(
                            receiverInputType, receiverType.getUnderlyingType(), "this", f -> "this_" + f.getSimpleName() + "_r"));
                } else {
                    verifastContract.getRequiresClause().addBefore(ownFieldsPredBody(enclClass, "this", f -> "?this_" + f.getSimpleName() + "_r"));
                    verifastContract.getRequiresClause().addBefore(fieldTypesPredBody(
                            enclClass,
                            f -> "this_" + f.getSimpleName() + "_r",
                            (f, ff) -> "this_" + f.getSimpleName() + "_" + ff.getSimpleName() + "_r",
                            // TODO the below only works for simple field accesses, not for more complex type arguments
                            a -> JavaExpressionUtil.isLiteral(a) ? a : ("this_" + a + "_r")));
                }
            }
        }

        if (isConstructor(tree)) {
            AnnotatedTypeMirror receiverType = propertyFactory.getMethodReturnType(tree);
            AnnotationMirror receiverOutputType = propertyFactory.getInitialized();
            if (trampoline) {
                verifastContract.getEnsuresClause().addBefore("result != null");
                verifastContract.getEnsuresClause().addBefore(getOwnFieldsPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "result", f -> "?result_" + f.getSimpleName() + "_e"));
                verifastContract.getEnsuresClause().addBefore(getFieldTypesPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "result", f -> "result_" + f.getSimpleName() + "_e"));
            } else {
                verifastContract.getEnsuresClause().addBefore(getOwnFieldsPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_e"));
                verifastContract.getEnsuresClause().addBefore(getFieldTypesPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "this", f -> "this_" + f.getSimpleName() + "_e"));
            }
        } else if (!outputPackingTypes.isEmpty()) {
            AnnotationMirror receiverOutputType = outputPackingTypes.get(0);
            if (receiverOutputType == null && !ElementUtils.isStatic(element)) {
                receiverOutputType = propertyFactory.getInitialized();
            }
            if (receiverOutputType != null) {
                TypeMirror receiverType = propertyFactory.getAnnotatedType(tree).getReceiverType().getUnderlyingType();
                if (propertyFactory.isSideEffectFree(element)) {
                    // Side-effect free methods reuse the precondition variables instead of
                    // defining new ones.
                    verifastContract.getEnsuresClause().addBefore(getOwnFieldsPredicateUse(
                            receiverOutputType, receiverType, "this", f -> "this_" + f.getSimpleName() + "_r"));
                    verifastContract.getEnsuresClause().addBefore(getFieldTypesPredicateUse(
                            receiverOutputType, receiverType, "this", f -> "this_" + f.getSimpleName() + "_r"));
                } else {
                    verifastContract.getEnsuresClause().addBefore(getOwnFieldsPredicateUse(
                            receiverOutputType, receiverType, "this", f -> "?this_" + f.getSimpleName() + "_e"));
                    verifastContract.getEnsuresClause().addBefore(getFieldTypesPredicateUse(
                            receiverOutputType, receiverType, "this", f -> "this_" + f.getSimpleName() + "_e"));
                }
            }
        }

        if (!ElementUtils.isStatic(element) && !isConstructor(tree)) {
            for (CooperativeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                AnnotationMirror receiverOutputType = methodOutputTypes.get(0);
                Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                boolean outputWt = !illTypedMethodOutputParams.contains(0);
                AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();

                if (requiredReceiverType != null) {
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(requiredReceiverType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if (!pat.isTrivial() && !pat.isInv()) {
                        verifastContract.getRequiresClause().addBefore(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_r"));
                    }
                }

                if (receiverOutputType != null) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(receiverOutputType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if ((!outputWt || trampoline || TRANSLATION_RAW) && !pat.isTrivial() && !pat.isInv() && !pat.isNonNull()) {
                        if (propertyFactory.isSideEffectFree(element)) {
                            // Side-effect free methods reuse the precondition variables instead of
                            // defining new ones.
                            verifastContract.getEnsuresClause().addBefore(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_r"));
                        } else {
                            verifastContract.getEnsuresClause().addBefore(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_e"));
                        }
                    }
                }
                if (!trampoline) {
                    if (!outputWt || TRANSLATION_RAW) {
                        ++methodCallPostconditions;
                    } else {
                        ++freeMethodCallPostconditions;
                    }
                }
            }
        }

        if (isConstructor(tree)) {
            for (LatticeVisitor.Result wellTypedness : results) {
                GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                AnnotatedTypeMirror receiverType = factory.getMethodReturnType(tree);

                Lattice lattice = wellTypedness.getLattice();
                boolean wt = wellTypedness.isWellTypedConstructor(tree);

                PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(receiverType);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if ((!wt || trampoline || TRANSLATION_RAW) && !pat.isTrivial() && !pat.isInv()) {
                    if (trampoline) {
                        verifastContract.getEnsuresClause().addBefore(new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                    } else if (!pat.isNonNull()) {
                        verifastContract.getEnsuresClause().addBefore(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_e"));
                    }
                }
                if (!trampoline) {
                    if (!wt || TRANSLATION_RAW) {
                        if (!pat.isTrivial() && !pat.isInv()) {
                            ++methodCallPostconditions;
                        }
                    } else {
                        ++freeMethodCallPostconditions;
                    }
                }
            }
        } else {
            {
                AnnotatedTypeMirror returnType = propertyFactory.getMethodReturnType(tree);
                if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                        && returnType.getKind() != TypeKind.VOID
                        && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)), getTop(propertyFactory))) {
                    if (returnType.getKind().isPrimitive() || returnType.toString().startsWith("java.") || returnType.getKind().equals(TypeKind.TYPEVAR)) {
                        verifastContract.getEnsuresClause().addVar("result", null);
                    } else {
                        verifastContract.getEnsuresClause().addVar("result", "result != null");
                        verifastContract.getEnsuresClause().addVarPred("result", getOwnFieldsPredicateUse(
                                returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                returnType.getUnderlyingType(), "result",
                                f -> "?result_" + f.getSimpleName() + "_e"));
                        verifastContract.getEnsuresClause().addVarPred("result", getFieldTypesPredicateUse(
                                returnType.getEffectiveAnnotationInHierarchy(getTop(propertyFactory)),
                                returnType.getUnderlyingType(), "result",
                                f -> "result_" + f.getSimpleName() + "_e"));
                    }
                }
            }

            for (LatticeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
                AnnotatedTypeMirror returnType = factory.getMethodReturnType(tree);

                if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                        && returnType.getKind() != TypeKind.VOID
                        && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                    boolean wt = wellTypedness.isWellTypedMethodResult(tree);
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if ((!wt || trampoline || TRANSLATION_RAW) && !pat.isTrivial() && !pat.isInv()) {
                        if (pat.isNonNull()) {
                            if (!returnType.getKind().isPrimitive()) {
                                verifastContract.getEnsuresClause().setGuard("result", null);
                                verifastContract.getEnsuresClause().addVarPred("result", new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                            }
                        } else {
                            verifastContract.getEnsuresClause().addVarPred("result", new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                        }
                    }
                    if (!trampoline) {
                        if (!wt || TRANSLATION_RAW) {
                            if (!pat.isTrivial() && !pat.isInv()) {
                                ++methodCallPostconditions;
                            }
                        } else {
                            ++freeMethodCallPostconditions;
                        }
                    }
                }
            }
        }

        for (int i = 0; i < tree.getParameters().size(); ++i) {
            Type javacType = tree.getParameters().get(i).type;
            if (javacType.toString().endsWith("[]")) {
                // TODO
                // array types in Verifast
            }

            VariableTree param = tree.getParameters().get(i);
            String paramName = param.getName().toString();
            VariableElement el = TreeUtils.elementFromDeclaration(param);

            if (javacType.getKind().isPrimitive()) {
                verifastContract.getRequiresClause().addVar(paramName, null);
                verifastContract.getEnsuresClause().addVar(paramName, null);
            } else {
                verifastContract.getRequiresClause().addVar(paramName, paramName + " != null");
                verifastContract.getEnsuresClause().addVar(paramName, paramName + " != null");
                if (!javacType.toString().startsWith("java.") && ! javacType.getKind().equals(TypeKind.TYPEVAR)) {
                    // Don't create OwnFields and FieldTypes predicates for library types or type variables; see above

                    verifastContract.getRequiresClause().addVarPred(paramName, getOwnFieldsPredicateUse(
                            inputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_r"
                    ));
                    verifastContract.getRequiresClause().addVarPred(paramName, getFieldTypesPredicateUse(
                            inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                    ));

                    if (propertyFactory.isSideEffectFree(element)) {
                        // Side-effect free methods reuse the precondition variables instead of
                        // defining new ones.
                        if (trampoline) {
                            verifastContract.getEnsuresClause().addVarPred(paramName, getOwnFieldsPredicateUse(
                                    inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                            ));
                            verifastContract.getEnsuresClause().addVarPred(paramName, getFieldTypesPredicateUse(
                                    inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                            ));
                        }
                    } else {
                        verifastContract.getEnsuresClause().addVarPred(paramName, getOwnFieldsPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_e"
                        ));
                        verifastContract.getEnsuresClause().addVarPred(paramName, getFieldTypesPredicateUse(
                                inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_e"
                        ));
                    }
                }
            }

            for (CooperativeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                boolean outputWt = !illTypedMethodOutputParams.contains(i + 1);
                PropertyAnnotation inputPa = lattice.getEffectivePropertyAnnotation(paramType);
                PropertyAnnotationType inputPat = inputPa.getAnnotationType();
                PropertyAnnotation outputPa = lattice.getPropertyAnnotation(paramOutputType);
                PropertyAnnotationType outputPat = outputPa.getAnnotationType();

                if (inputPat.isNonNull()) {
                    if (!paramType.getKind().isPrimitive()) {
                        verifastContract.getRequiresClause().setGuard(paramName, null);
                        verifastContract.getRequiresClause().addBefore(new PredicateUse(inputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                    }
                } else if (!inputPat.isTrivial() && !inputPat.isInv()) {
                    verifastContract.getRequiresClause().addVarPred(paramName, new PredicateUse(inputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                }

                if (outputPat.isNonNull()) {
                    if (!paramType.getKind().isPrimitive()) {
                        verifastContract.getEnsuresClause().setGuard(paramName, null);
                        if (propertyFactory.isSideEffectFree(element)) {
                            // Side-effect free methods reuse the precondition variables instead of
                            // defining new ones.
                            verifastContract.getEnsuresClause().addBefore(new PredicateUse(outputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                        } else {
                            verifastContract.getEnsuresClause().addBefore(new PredicateUse(outputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_e"));
                        }
                    }
                } else if ((!outputWt || trampoline || TRANSLATION_RAW) && !outputPat.isTrivial() && !outputPat.isInv()) {
                    if (propertyFactory.isSideEffectFree(element)) {
                        // Side-effect free methods reuse the precondition variables instead of
                        // defining new ones.
                        verifastContract.getEnsuresClause().addBefore(new PredicateUse(outputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                    } else {
                        verifastContract.getEnsuresClause().addBefore(new PredicateUse(outputPa, paramName, f -> paramName + "_" + f.getSimpleName() + "_e"));
                    }
                }

                if (!trampoline) {
                    if (!outputWt || TRANSLATION_RAW) {
                        ++methodCallPostconditions;
                    } else {
                        ++freeMethodCallPostconditions;
                    }
                }
            }
        }
    }

    protected VerifastContract contractForMethod(JCTree.JCMethodDecl tree, boolean trampoline) {
        ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();
        VerifastContract verifastContract = new VerifastContract(!trampoline, trampoline);

        if (propertyFactory.getDeclAnnotation(element, VerifastSuppressTranslatedContract.class) == null) {
            addTypesToContract(verifastContract, tree, trampoline);
        };

        Function<String, String> clauseTransformer = trampoline && isConstructor(tree) ? clause -> clause.replace("this", "result") : Function.identity();
        getVerifastRequiresClauseValues(element).stream().map(clauseTransformer).forEach(verifastContract.getRequiresClause()::addAfter);
        getVerifastEnsuresClauseValues(element).stream().map(clauseTransformer).forEach(verifastContract.getEnsuresClause()::addAfter);
        if (TRANSLATION_RAW) {
            getVerifastRequiresClauseValuesTranslationOnly(element).stream().map(clauseTransformer).forEach(verifastContract.getRequiresClause()::addAfter);
            getVerifastEnsuresClauseValuesTranslationOnly(element).stream().map(clauseTransformer).forEach(verifastContract.getEnsuresClause()::addAfter);
        }

        //TODO
        //support for Nullness Checker contract annotations in Verifast

        return verifastContract;
    }

    protected void printTrampoline(JCTree.JCMethodDecl tree, boolean printBody) {
        try {
            VerifastContract verifastContract = contractForMethod(tree, true);

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                print("static ");
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
                print(" ");
                print(trampolineName(tree.name));
            } else {
                if (tree.restype.type instanceof Type.TypeVar && !propertyFactory.getChecker().shouldKeepGenerics()) {
                    print("Object");
                } else {
                    printExpr(tree.restype);
                }
                print(" ");
                print(trampolineName(tree.name));
            }

            print("(");

            StringJoiner paramsStr = new StringJoiner(", ");
            for (JCTree.JCVariableDecl param : tree.params) {
                paramsStr.add(unannotatedSimpleTypeName(param) + " " + param.getName());
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

            println();
            indent();
            printlnAligned(verifastContract.toString());
            undent();

            if (printBody) {
                printlnAligned("{}");
            } else {
                printlnAligned(";");
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
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
                        ((JCTree.JCBlock) block).accept(this);
                    });
            println();
        }
    }

    @Override
    public void visitNewClass(JCTree.JCNewClass tree) {
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
            StringJoiner args = new StringJoiner(", ");
            args.add(tree.args.toString());
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

    @Override
    protected void printPackStatement(Tree tree, String frame) throws IOException {
        if (frame.equals("Object") || frame.equals("java.lang.Object")) {
            return;
        }

        List<VerifastClause> assertions = new ArrayList<>();
        List<VerifastContract> assumptions = new ArrayList<>();

        println();

        {
            VerifastClause receiverPacked = new VerifastClause("assert", false);
            AnnotationMirror receiverPackingType =
                    propertyFactory.getInputPackingTypes(enclMethod).get(0);

            AnnotatedTypeMirror receiverType;
            if (isConstructor(enclMethod)) {
                receiverType = propertyFactory.getMethodReturnType(enclMethod);
            } else {
                receiverType = propertyFactory.getAnnotatedType(enclMethod).getReceiverType();
            }

            receiverPacked.addBefore(getOwnFieldsPredicateUse(receiverPackingType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
            printlnAligned(receiverPacked.toString());
        }

        List<VariableElement> allFields = enclClass.type == null
                ? List.of()
                : ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());
        for (VariableElement field : allFields) {
            VerifastClause fieldAssertion = new VerifastClause("assert", false);
            VerifastContract fieldAssumption = new VerifastContract(false, false);
            String name = field.getSimpleName().toString();

            // For variables that are not syntactically typed NonNull, we do not generate any assumptions,
            // since the nullness check makes it awkward to reference variables defined in the assumption's precondition
            boolean nonNull = nullnessFactory.getAnnotatedType(field).hasEffectiveAnnotation(nullnessFactory.getNonNull())
                    && !nullnessResult.getUninitializedFields(tree).contains(field);

            if (field.asType().getKind().isPrimitive()) {
                fieldAssertion.addVar(name, null);
                fieldAssumption.getRequiresClause().addVar("arg", null);
                fieldAssumption.getEnsuresClause().addVar("arg", null);
            } else {
                fieldAssertion.addVar(name, "this_" + name + "_a" + enclClassAssertionSequenceCounter + " != null");
                fieldAssumption.getRequiresClause().addVar("arg", null);
                fieldAssumption.getEnsuresClause().addVar("arg", null);

                AnnotationMirror packingType =
                        propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
                fieldAssertion.addVarPred(name, getOwnFieldsPredicateUse(
                        packingType,
                        field.asType(), "this_" + name + "_a" + enclClassAssertionSequenceCounter,
                        f -> "?" + name + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                fieldAssumption.getRequiresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, field.asType(), "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
                fieldAssumption.getEnsuresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, field.asType(), "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                fieldAssumption.getEnsuresClause().addVarPred("arg", getFieldTypesPredicateUse(packingType, field.asType(), "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            }

            for (LatticeVisitor.Result result : results) {
                List<VariableElement> uninitFields = result.getUninitializedFields(tree);
                AnnotatedTypeMirror type = result.getTypeFactory().getAnnotatedType(field);
                PropertyAnnotation pa = result.getLattice().getEffectivePropertyAnnotation(type);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial() && !pat.isInv()) {
                    boolean wt = !uninitFields.contains(field);

                    if (pat.isNonNull()) {
                        if (!type.getKind().isPrimitive()) {
                            fieldAssertion.setGuard(name, null);
                            fieldAssertion.addBefore(new PredicateUse(
                                    pa,
                                    "this_" + name + "_a" + enclClassAssertionSequenceCounter,
                                    f -> name + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                            fieldAssumption.getEnsuresClause().addBefore(new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                        }
                    } else if (nonNull && wt && !TRANSLATION_RAW) {
                        fieldAssumption.getEnsuresClause().addVarPred("arg", new PredicateUse(pa, name, f -> "arg_" + f.getSimpleName() + "_a"));
                    } else {
                        fieldAssertion.addVarPred(name, new PredicateUse(
                                pa,
                                "this_" + name + "_a" + enclClassAssertionSequenceCounter,
                                f -> name + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                    }
                }
            }

            if (nonNull && !TRANSLATION_RAW) {
                assumptions.add(fieldAssumption);
                assertions.add(fieldAssertion);
                enclClassAssumptionsToGenerate.add(Pair.of(field.asType(), fieldAssumption));
                printlnAligned(String.format("assume%s(this.%s);", enclClassAssumptionCounter++, field.getSimpleName()));
            } else {
                assertions.add(fieldAssertion);
            }
        }

        assertions.stream().map(VerifastClause::toString).forEach(this::printlnAligned);

        this.assertions += assertions.size();
        this.assumptions += assumptions.size();
        ++enclClassAssertionSequenceCounter;
        align();
    }

    @Override
    public void visitApply(JCTree.JCMethodInvocation tree) {
        if (tree.meth.toString().equals("super") || tree.meth.toString().equals("this")) {
            super.visitApply(tree);
            return;
        }

        try {
            // Explicit packing statement
            if (tree.meth.toString().equals("Packing.pack")) {
                printPackStatement(tree, TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression()).toString());
            } else if (tree.meth.toString().equals("Packing.unpack")) {
                printUnpackStatement(tree, ((TypeElement) TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression())).getSuperclass().toString());
            } else if (tree.meth.toString().startsWith("Ghost.")) {
                //TODO ghost variables in Verifast
                return;
            } else if (tree.meth.toString().startsWith("Assert.immutable") ||
                    (tree.meth.toString().equals("Assert.immutableFieldUnchanged_TranslationOnly") && TRANSLATION_RAW)) {
                //TODO Additional uniqueness type information in Verifast?
                // Probably unneeded in separation logic
                return;
            } else if (tree.meth.toString().equals("Assert._assert")) {
                // Assert._assert and Assert._assume take JML expression as argument; ignored in Verifast
                return;
            } else if (tree.meth.toString().equals("Assert._assume")) {
                // Assert._assert and Assert._assume take JML expression as argument; ignored in Verifast
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_assert")) {
                JCTree.JCLiteral assertion = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ assert %s", assertion.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_open")) {
                JCTree.JCLiteral pred = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ open %s", pred.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_close")) {
                JCTree.JCLiteral pred = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ close %s", pred.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_assert_translationOnly")) {
                if (!TRANSLATION_RAW) {
                    return;
                }
                JCTree.JCLiteral assertion = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ assert %s", assertion.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_open_translationOnly")) {
                if (!TRANSLATION_RAW) {
                    return;
                }
                JCTree.JCLiteral pred = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ open %s", pred.getValue()));
                return;
            } else if (tree.meth.toString().equals("Assert._verifast_close_translationOnly")) {
                if (!TRANSLATION_RAW) {
                    return;
                }
                JCTree.JCLiteral pred = (JCTree.JCLiteral) tree.args.get(0);
                print(String.format("//@ close %s", pred.getValue()));
                return;
            }

            AnnotatedTypeMirror.AnnotatedExecutableType invokedMethod = propertyFactory.methodFromUse(tree).executableType;

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedTypeMirror.AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().methodFromUse(tree).executableType;

                if (!ElementUtils.isStatic(invokedMethod.getElement())) {
                    PropertyAnnotationType pat = wellTypedness.getLattice().getEffectivePropertyAnnotation(methodType.getReceiverType()).getAnnotationType();
                    if (!pat.isTrivial() && !pat.isInv()) {
                        if (wellTypedness.getIllTypedMethodReceivers().contains(tree) || TRANSLATION_RAW) {
                            ++methodCallPreconditions;
                        } else {
                            //TODO add assumptions for free preconditions?
                            ++freeMethodCallPreconditions;
                        }
                    }
                }

                for (int i = 0; i < invokedMethod.getParameterTypes().size(); ++i) {
                    AnnotatedTypeMirror paramType = methodType.getParameterTypes().get(i);
                    PropertyAnnotationType pat = wellTypedness.getLattice().getPropertyAnnotation(paramType).getAnnotationType();
                    // TODO Don't add argument for type variable
                    // to be consistent with the (non-generic) declaration of the trampoline method
                    if (!(paramType instanceof AnnotatedTypeMirror.AnnotatedTypeVariable) &&
                            !pat.isTrivial() && !pat.isInv()) {
                        if (wellTypedness.getIllTypedMethodParams(tree).contains(i) || TRANSLATION_RAW) {
                            ++methodCallPreconditions;
                        } else {
                            //TODO add assumptions for free preconditions?
                            ++freeMethodCallPreconditions;
                        }
                    }
                }
            }

            if (propertyFactory.getChecker().shouldNotUseTrampoline(((Symbol.MethodSymbol) invokedMethod.getElement()).owner.toString())) {
                super.visitApply(tree);
                return;
            }

            if (tree.meth.hasTag(com.sun.tools.javac.tree.JCTree.Tag.SELECT)) {
                JCTree.JCFieldAccess left = (JCTree.JCFieldAccess)tree.meth;
                printExpr(left.selected);
                print(".");
                print(trampolineName(left.name));
            } else {
                print(trampolineName(tree.meth.toString()));
            }

            print("(");
            printExprs(tree.args);
            print(")");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private boolean inForLoopInit = false;

    @Override
    public void visitForLoop(JCTree.JCForLoop tree) {
        try {
            this.print("for (");
            inForLoopInit = true;
            if (tree.init.nonEmpty()) {
                if (tree.init.head.hasTag(JCTree.Tag.VARDEF)) {
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

    protected Pair<VerifastClause, VerifastContract> getConditions(JCTree.JCAssign tree, String subject) {
        VerifastClause assertion = new VerifastClause("assert", false);
        VerifastContract assumption = new VerifastContract(false, false);

        AnnotatedTypeMirror packingTypeMirror = propertyFactory.getAnnotatedTypeLhs(tree.lhs);
        AnnotationMirror packingType = packingTypeMirror.getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
        TypeMirror underlyingType = packingTypeMirror.getUnderlyingType();

        // For variables that are not syntactically typed NonNull, we do not generate any assumptions,
        // since the nullness check makes it awkward to reference variables defined in the assumption's precondition
        boolean nonNull = nullnessFactory.getAnnotatedTypeLhs(tree.lhs).hasEffectiveAnnotation(nullnessFactory.getNonNull())
                && !nullnessResult.isWellTyped(tree);

        if (underlyingType.getKind().isPrimitive()) {
            assertion.addVar(subject, null);
            assumption.getRequiresClause().addVar("arg", null);
            assumption.getEnsuresClause().addVar("arg", null);
        } else {
            assertion.addVar(subject, subject + " != null");
            assumption.getRequiresClause().addVar("arg", null);
            assumption.getEnsuresClause().addVar("arg", null);

            assertion.addVarPred(subject, getOwnFieldsPredicateUse(
                    packingType,
                    underlyingType, subject,
                    f -> "?" + subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter
            ));

            assumption.getRequiresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
            assumption.getEnsuresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            assumption.getEnsuresClause().addVarPred("arg", getFieldTypesPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree.lhs);

            if (type instanceof AnnotatedTypeMirror.AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(type);
            if (pa.getAnnotationType().isNonNull()) {
                if (!type.getKind().isPrimitive()) {
                    assertion.setGuard(subject, null);
                    assertion.addBefore(new PredicateUse(
                            pa,
                            subject,
                            f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                    assumption.getEnsuresClause().addBefore(new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                }
            } else if (nonNull && wt && !TRANSLATION_RAW) {
                assumption.getEnsuresClause().addVarPred("arg", new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                ++assumptions;
            } else if (!pa.getAnnotationType().isTrivial() && !pa.getAnnotationType().isInv()) {
                assertion.addVarPred(subject, new PredicateUse(
                        pa,
                        subject,
                        f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                ++assertions;
            }
        }

        int predNum = assertion.getPredNum();
        if (underlyingType.getKind().isPrimitive() && predNum == 0) {
            assertion = null;
        } else if (!underlyingType.getKind().isPrimitive() && predNum == 1) {
            assertion = null;
        }

        if (!nonNull || TRANSLATION_RAW) {
            assumption = null;
        }

        enclClassAssumptionsToGenerate.add(Pair.of(underlyingType, assumption));
        return Pair.of(assertion, assumption);
    }

    protected Pair<VerifastClause, VerifastContract> getConditions(JCTree.JCVariableDecl tree, String subject) {
        VerifastClause assertion = new VerifastClause("assert", false);
        VerifastContract assumption = new VerifastContract(false, false);

        AnnotatedTypeMirror packingTypeMirror = propertyFactory.getAnnotatedTypeLhs(tree);
        AnnotationMirror packingType = packingTypeMirror.getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
        TypeMirror underlyingType = packingTypeMirror.getUnderlyingType();
        String frame = unannotatedSimpleTypeName(getTypeFrame(packingType, underlyingType), false);

        if (frame.equals("Object") && tree.getInitializer() != null && !tree.getInitializer().type.getKind().equals(TypeKind.NULL)) {
            packingTypeMirror = propertyFactory.getAnnotatedType(tree.getInitializer());
            packingType = packingTypeMirror.getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
            underlyingType = packingTypeMirror.getUnderlyingType();
            frame = unannotatedSimpleTypeName(getTypeFrame(packingType, underlyingType), false);
        }

        // For variables that are not syntactically typed NonNull, we do not generate any assumptions,
        // since the nullness check makes it awkward to reference variables defined in the assumption's precondition
        boolean nonNull = nullnessFactory.getAnnotatedTypeLhs(tree).hasEffectiveAnnotation(nullnessFactory.getNonNull())
                && !nullnessResult.isWellTyped(tree);

        if (underlyingType.getKind().isPrimitive()) {
            assertion.addVar(subject, null);
            assumption.getRequiresClause().addVar("arg", null);
            assumption.getEnsuresClause().addVar("arg", null);
        } else {
            assertion.addVar(subject, subject + " != null");
            assumption.getRequiresClause().addVar("arg", null);
            assumption.getEnsuresClause().addVar("arg", null);
        }

        if (!underlyingType.getKind().isPrimitive() && !frame.equals("Object")) {
            assertion.addVarPred(subject, getOwnFieldsPredicateUse(
                    packingType,
                    underlyingType, subject,
                    f -> "?" + subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter
            ));

            assumption.getRequiresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
            assumption.getEnsuresClause().addVarPred("arg", getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            assumption.getEnsuresClause().addVarPred("arg", getFieldTypesPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            GenericAnnotatedTypeFactory<?,?,?,?> factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree);

            if (type instanceof AnnotatedTypeMirror.AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(factory.getAnnotatedTypeLhs(tree));
            if (pa.getAnnotationType().isNonNull()) {
                if (!type.getKind().isPrimitive()) {
                    assertion.setGuard(subject, null);
                    assertion.addBefore(new PredicateUse(
                            pa,
                            subject,
                            f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                    assumption.getEnsuresClause().addBefore(new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                }
            } else if (nonNull && wt && !TRANSLATION_RAW) {
                assumption.getEnsuresClause().addVarPred("arg", new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                ++assumptions;
            } else if (!pa.getAnnotationType().isTrivial() && !pa.getAnnotationType().isInv()) {
                assertion.addVarPred(subject, new PredicateUse(
                        pa,
                        subject,
                        f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                ++assertions;
            }
        }

        int predNum = assertion.getPredNum();
        if (underlyingType.getKind().isPrimitive() && predNum == 0) {
            assertion = null;
        } else if (!underlyingType.getKind().isPrimitive() && predNum == 1) {
            assertion = null;
        }

        if (!nonNull || TRANSLATION_RAW) {
            assumption = null;
        }

        enclClassAssumptionsToGenerate.add(Pair.of(underlyingType, assumption));
        return Pair.of(assertion, assumption);
    }

    @Override
    public void visitAssign(JCTree.JCAssign tree) {
        printInferredPackingStatements(tree);

        String tempVar = tempVarName();
        Pair<VerifastClause, VerifastContract> conditions = getConditions(tree, tempVar);

        // For readability, skip field assignments if they are not ill-typed (which can only happen with assignments
        // to committed fields).
        if (tree.getVariable() instanceof MemberSelectTree && conditions.first == null) {
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
                conditions,
                tempVar);
    }

    @Override
    public void visitVarDef(JCTree.JCVariableDecl tree) {
        printInferredPackingStatements(tree);

        if (enclMethod == null) {
            try {
                print("public ");
                if (tree.getModifiers().getFlags().contains(Modifier.STATIC)) {
                    print("static ");
                }
                println(String.format("%s %s;", unannotatedTypeNameLhs(tree), tree.getName()));
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
                        getConditions(tree, tempVar),
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

    protected void visitAssignOrDef(String varName, String unannotatedTypeName, JCTree expression, Pair<VerifastClause, VerifastContract> conditions, String tempVar) {
        try {
            print(String.format("%s %s = ", unannotatedTypeName, tempVar));
            expression.accept(this);
            println(";");

            if (conditions.second != null) {
                printlnAligned(String.format("assume%s(%s);", enclClassAssumptionCounter++, tempVar));
            }
            if (conditions.first != null) {
                printlnAligned(conditions.first.toString());
                ++enclClassAssertionSequenceCounter;
            }

            align();
            print(String.format("%s = %s", varName, tempVar));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitReturn(JCTree.JCReturn tree) {
        try {
            TypeMirror unpackFrame = propertyFactory.getInferredUnpackFrame(enclMethod);
            TypeMirror packFrame = propertyFactory.getInferredPackFrame(enclMethod);
            if (unpackFrame != null) {
                printUnpackStatement(enclMethod, unannotatedSimpleTypeName(unpackFrame, false));
            } else if (packFrame != null) {
                printPackStatement(enclMethod, unannotatedSimpleTypeName(packFrame, false));
            }
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }

        super.visitReturn(tree);
    }

    @Override
    protected void printUnpackStatement(Tree tree, String frame) throws IOException {
        // do nothing
    }

    protected String trampolineName(String methodName) {
        if (methodName.equals("<init>")) {
            methodName = "INIT";
        }

        return String.format("__%s_restorePermissions", methodName.replace('.', '_'));
    }

    protected String trampolineName(Name methodName) {
        return trampolineName(methodName.toString());
    }

    @SuppressWarnings("unchecked")
    protected List<String> getVerifastRequiresClauseValues(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastRequiresClauses.class);
        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastRequiresClause.class);

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
    protected List<String> getVerifastEnsuresClauseValues(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastEnsuresClauses.class);
        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastEnsuresClause.class);

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
    protected List<String> getVerifastRequiresClauseValuesTranslationOnly(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastRequiresClausesTranslationOnly.class);
        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastRequiresClauseTranslationOnly.class);

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
    protected List<String> getVerifastEnsuresClauseValuesTranslationOnly(Element element) {
        AnnotationMirror verifastClauses = propertyFactory.getDeclAnnotation(element, VerifastEnsuresClausesTranslationOnly.class);
        AnnotationMirror verifastClause = propertyFactory.getDeclAnnotation(element, VerifastEnsuresClauseTranslationOnly.class);

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

    public static class VerifastContract {

        private VerifastClause requiresClause;
        private VerifastClause ensuresClause;

        public VerifastContract(boolean requiresPermission, boolean ensuresPermission) {
            this.requiresClause = new VerifastClause("requires", requiresPermission);
            this.ensuresClause = new VerifastClause("ensures", ensuresPermission);
        }

        public VerifastClause getRequiresClause() {
            return requiresClause;
        }

        public VerifastClause getEnsuresClause() {
            return ensuresClause;
        }

        @Override
        public String toString() {
            String reqStr = requiresClause.toString(false);
            String ensStr = ensuresClause.toString(false);
            return "//@ requires " + reqStr + ";\n//@ ensures " + ensStr + ";";
        }
    }

    public static class PredicateUseCollection {

        private boolean permission;
        private String guard;
        private List<PredicateUse> preds = new ArrayList<>();


        public PredicateUseCollection(boolean permission) {
            this(permission, null);
        }

        public PredicateUseCollection(boolean permission, String guard) {
            this.permission = permission;
            this.guard = guard;
        }

        public void add(PredicateUse pred) {
            this.preds.add(pred);
        }

        @Override
        public String toString() {
            StringJoiner sj = new StringJoiner(" &*& ");
            if (permission) {
                preds.stream().map(PredicateUse::toString).forEach(sj::add);
            } else {
                preds.stream().forEach(p -> { if (p.name.equals("NonNull")) sj.add(p.toString()); else sj.add("[_](" + p + ")"); });
            }
            if (sj.length() == 0) {
                return "true";
            } else if (guard != null) {
                return String.format("(%s ? (%s) : true)", guard, sj);
            } else {
                return "(" + sj + ")";
            }
        }
    }

    public static class VerifastClause {

        private String clauseType;
        private boolean permission;
        private Map<String, PredicateUseCollection> varPreds = new TreeMap<>();
        private List<String> additionalPredsBefore = new ArrayList<>();
        private List<String> additionalPredsAfter = new ArrayList<>();
        private int predNum;

        public VerifastClause(String clauseType) {
            this(clauseType, true);
        }

        public VerifastClause(String clauseType, boolean permission) {
            this.clauseType = clauseType;
            this.permission = permission;
        }

        public void addVar(String varName, String precondition) {
            assert !varPreds.containsKey(varName);
            varPreds.put(varName, new PredicateUseCollection(permission, precondition));
        }

        public void setGuard(String varName, String guard) {
            assert varPreds.containsKey(varName);
            varPreds.get(varName).guard = guard;
        }

        public void addVarPred(String varName, PredicateUse pred) {
            assert varPreds.containsKey(varName);
            varPreds.get(varName).add(pred);
            ++predNum;
        }

        public void addBefore(PredicateUse pred) {
            if (permission || pred.name.equals("NonNull")) {
                addBefore(pred.toString());
            } else {
                addBefore("[_]" + pred);
            }
        }

        public void addBefore(String pred) {
            this.additionalPredsBefore.add(pred);
            ++predNum;
        }

        public void addAfter(PredicateUse pred) {
            if (permission || pred.name.equals("NonNull")) {
                addAfter(pred.toString());
            } else {
                addBefore("[_]" + pred);
            }
        }

        public void addAfter(String pred) {
            this.additionalPredsAfter.add(pred);
            ++predNum;
        }

        @Override
        public String toString() {
            return toString(true);
        }

        public String toString(boolean withClauseType) {
            StringJoiner sj = new StringJoiner(" &*& ");

            if (permission) {
                additionalPredsBefore.forEach(sj::add);
                varPreds.values().stream().map(PredicateUseCollection::toString).forEach(sj::add);
                additionalPredsAfter.forEach(sj::add);
            } else {
                additionalPredsBefore.forEach(sj::add);
                varPreds.values().stream().map(PredicateUseCollection::toString).forEach(sj::add);
                additionalPredsAfter.forEach(sj::add);
            }

            if (sj.length() == 0) {
                sj.add("true");
            }

            if (withClauseType) {
                return "//@ " + clauseType + " " + sj + ";";
            } else {
                return sj.toString();
            }
        }

        public int getPredNum() {
            return predNum;
        }
    }

    public class PredicateParameter {

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
            this.typeName = unannotatedSimpleTypeName(f.asType(), false);
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
            this(pa, subject, fieldNamer, Function.identity());
        }

        /**
         * Constructs a predicate use from the given property annotation and arguments.
         *
         * @param pa the property annotation corresponding to the predicate use
         * @param subject the subject argument; only used if {@code pa}'s subject type is primitive
         * @param fieldNamer a function supplying a name for every field argument; only used if {@code pa}'s subject
         *                     type is not primitive
         * @param typeArgTransformer a function transforming arguments to {@code pa} before they get passed to the
         *                     predicate
         */
        public PredicateUse(PropertyAnnotation pa, String subject, Function<VariableElement, String> fieldNamer, Function<String, String> typeArgTransformer) {
            PropertyAnnotationType pat = pa.getAnnotationType();
            this.name = pat.getName();
            this.args = new ArrayList<>();

            if (pat.getSubjectType() == null || pat.getSubjectType().getKind().isPrimitive() || pat.isNonNull()) {
                args.add(subject);
            } else {
                List<VariableElement> fields = nonStaticDependableFieldsInFrame(pat.getSubjectType());
                fields.stream().map(fieldNamer).forEach(this.args::add);
            }
            pa.getActualParameters().stream().map(typeArgTransformer).forEach(this.args::add);
        }

        @Override
        public String toString() {
            if (name.equals("NonNull")) {
                // Verifast does not open our NonNull predicate automatically, leading to nullness errors on method calls,
                // so we open the predicate here directly.
                return args.getFirst() + " != null";
            }
            StringJoiner sj = new StringJoiner(", ", name + "(", ")");
            args.forEach(sj::add);
            return sj.toString();
        }
    }

    public class PredicateDef {

        protected String name;
        protected List<PredicateParameter> inParams;
        protected List<PredicateParameter> outParams;
        protected String body;

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
