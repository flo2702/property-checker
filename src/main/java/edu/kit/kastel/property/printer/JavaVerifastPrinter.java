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

        StringJoiner fieldTypesPredBody = new StringJoiner(" &*& ");
        Map<VariableElement, List<PredicateUse>> fieldTypes = new HashMap<>();

        for (VariableElement field : allFields) {
            fieldTypes.put(field, new ArrayList<>());

            if (field.asType().getKind().isPrimitive()) {
                continue;
            }
            if (unannotatedTypeName(field.asType(), false).startsWith("java.")) {
                // Don't create OwnFields and FieldTypes predicates for library types
                // TODO add cmd option to customize this behavior
                continue;
            }

            AnnotationMirror packingType = propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
            PredicateUse ownFields = getOwnFieldsPredicateUse(packingType, field.asType(), fieldNamer.apply(field), f -> "?" + fieldOfFieldNamer.apply(field, f));
            PredicateUse fieldsOfFieldTypes = getFieldTypesPredicateUse(packingType, field.asType(), fieldNamer.apply(field), f -> fieldOfFieldNamer.apply(field, f));
            fieldTypes.get(field).add(ownFields);
            fieldTypes.get(field).add(fieldsOfFieldTypes);
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
                    fieldTypes.get(field).add(new PredicateUse(pa, fieldNamer.apply(field), f -> fieldOfFieldNamer.apply(field, f), typeArgTransformer));
                }
            }
        }

        for (Map.Entry<VariableElement, List<PredicateUse>> entry : fieldTypes.entrySet()) {
            StringJoiner sj = new StringJoiner(" &*& ");
            entry.getValue().stream().map(PredicateUse::toString).forEach(sj::add);
            if (entry.getKey().asType().getKind().isPrimitive()) {
                if (sj.length() > 0) {
                    fieldTypesPredBody.add("("+sj+")");
                }
            } else {
                fieldTypesPredBody.add(String.format("(%s == null ? true : %s)", fieldNamer.apply(entry.getKey()), sj.length() == 0 ? "true" : ("("+sj+")")));
            }
        }

        return fieldTypesPredBody.toString();
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

    protected VerifastContract contractForMethod(JCTree.JCMethodDecl tree, boolean trampoline) {
        ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();
        VerifastContract verifastContract = new VerifastContract(!trampoline, trampoline);

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

                // Side-effect free methods use no heap chunks except for the result.
                if (!propertyFactory.isSideEffectFree(element)) {
                    // Open OwnFields and FieldTypes predicates of receiver directly to avoid errors when verifying the
                    // method body.
                    // But leave them closed in trampoline methods to avoid missing heap chunks in callers.
                    if (trampoline) {
                        verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                                receiverInputType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_r"));
                        verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                                receiverInputType, receiverType.getUnderlyingType(), "this", f -> "this_" + f.getSimpleName() + "_r"));
                    } else {
                        verifastContract.addRequiresPredBefore(ownFieldsPredBody(enclClass, "this", f -> "?this_" + f.getSimpleName() + "_r"));
                        verifastContract.addRequiresPredBefore(fieldTypesPredBody(
                                enclClass,
                                f -> "this_" + f.getSimpleName() + "_r",
                                (f, ff) -> "this_" + f.getSimpleName() + "_" + ff.getSimpleName() + "_r",
                                // TODO the below only works for simple field accesses, not for more complex type arguments
                                a -> JavaExpressionUtil.isLiteral(a) ? a : ("this_" + a + "_r")));
                    }
                }
            }
        }

        if (isConstructor(tree)) {
            AnnotatedTypeMirror receiverType = propertyFactory.getMethodReturnType(tree);
            AnnotationMirror receiverOutputType = propertyFactory.getInitialized();
            if (trampoline) {
                verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "result", f -> "?result_" + f.getSimpleName() + "_e"));
                verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "result", f -> "result_" + f.getSimpleName() + "_e"));
            } else {
                verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_e"));
                verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                        receiverOutputType, receiverType.getUnderlyingType(), "this", f -> "this_" + f.getSimpleName() + "_e"));
            }
        } else if (!outputPackingTypes.isEmpty()) {
            AnnotationMirror receiverOutputType = outputPackingTypes.get(0);
            if (receiverOutputType == null && !ElementUtils.isStatic(element)) {
                receiverOutputType = propertyFactory.getInitialized();
            }
            if (receiverOutputType != null) {
                VariableElement el = TreeUtils.elementFromDeclaration(tree.getReceiverParameter());
                if (!propertyFactory.isSideEffectFree(element)) {
                    // Side-effect free methods use no heap chunks except for the result.
                    verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                            receiverOutputType, el, f -> "?this_" + f.getSimpleName() + "_e"));
                    verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                            receiverOutputType, el, f -> "this_" + f.getSimpleName() + "_e"));
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
                        if (!propertyFactory.isSideEffectFree(element)) {
                            // Side-effect free methods use no heap chunks except for the result.
                            verifastContract.addRequiresPred(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_r"));
                        }
                    }
                }

                if (receiverOutputType != null) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(receiverOutputType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if ((!outputWt || trampoline) && !pat.isTrivial() && !pat.isInv()) {
                        if (!propertyFactory.isSideEffectFree(element)) {
                            // Side-effect free methods use no heap chunks except for the result.
                            verifastContract.addEnsuresPred(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_e"));
                        }
                    }
                }
                if (!trampoline) {
                    if (!outputWt) {
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

                if ((!wt || trampoline) && !pat.isTrivial() && !pat.isInv()) {
                    if (trampoline) {
                        verifastContract.addEnsuresPred(new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                    } else {
                        verifastContract.addEnsuresPred(new PredicateUse(pa, "this", f -> "this_" + f.getSimpleName() + "_e"));
                    }
                }
                if (!trampoline) {
                    if (!wt) {
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
                        && returnType.getKind() != TypeKind.VOID && !returnType.getKind().isPrimitive()
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
                AnnotatedTypeMirror returnType = factory.getMethodReturnType(tree);

                if (!(returnType instanceof AnnotatedTypeMirror.AnnotatedExecutableType)
                        && returnType.getKind() != TypeKind.VOID
                        && !AnnotationUtils.areSame(returnType.getEffectiveAnnotationInHierarchy(getTop(factory)), getTop(factory))) {
                    boolean wt = wellTypedness.isWellTypedMethodResult(tree);
                    PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(returnType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if ((!wt || trampoline) && !pat.isTrivial() && !pat.isInv()) {
                        verifastContract.addEnsuresPred(new PredicateUse(pa, "result", f -> "result_" + f.getSimpleName() + "_e"));
                    }
                    if (!trampoline) {
                        if (!wt) {
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

            if (!javacType.toString().startsWith("java.") && !javacType.getKind().isPrimitive()) {
                // Don't create OwnFields and FieldTypes predicates for library types
                // TODO add cmd option to customize this behavior

                verifastContract.addRequiresPred(getOwnFieldsPredicateUse(
                        inputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_r"
                ));
                verifastContract.addRequiresPred(getFieldTypesPredicateUse(
                        inputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_r"
                ));
                /*verifastContract.addEnsuresPred(getOwnFieldsPredicateUse(
                        outputPackingTypes.get(i + 1), el, f -> "?" + paramName + "_" + f.getSimpleName() + "_e"
                ));
                verifastContract.addEnsuresPred(getFieldTypesPredicateUse(
                        outputPackingTypes.get(i + 1), el, f -> paramName + "_" + f.getSimpleName() + "_e"
                ));*/
            }

            for (CooperativeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                AnnotatedTypeMirror.AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                boolean outputWt = !illTypedMethodOutputParams.contains(i + 1);
                PropertyAnnotation pa = lattice.getEffectivePropertyAnnotation(paramType);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial() && !pat.isInv()) {
                    verifastContract.addRequiresPred(new PredicateUse(lattice.getEffectivePropertyAnnotation(paramType), paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                }
                if ((!outputWt || trampoline) && !pat.isTrivial() && !pat.isInv()) {
                    verifastContract.addEnsuresPred(new PredicateUse(lattice.getPropertyAnnotation(paramOutputType), paramName, f -> paramName + "_" + f.getSimpleName() + "_r"));
                }

                if (!trampoline) {
                    if (!outputWt) {
                        ++methodCallPostconditions;
                    } else {
                        ++freeMethodCallPostconditions;
                    }
                }
            }
        }

        Function<String, String> clauseTransformer = trampoline && isConstructor(tree) ? clause -> clause.replace("this", "result") : Function.identity();
        getVerifastRequiresClauseValues(element).stream().map(clauseTransformer).forEach(verifastContract::addRequiresPredAfter);
        getVerifastEnsuresClauseValues(element).stream().map(clauseTransformer).forEach(verifastContract::addEnsuresPredAfter);
        if (TRANSLATION_RAW) {
            getVerifastRequiresClauseValuesTranslationOnly(element).stream().map(clauseTransformer).forEach(verifastContract::addRequiresPredAfter);
            getVerifastEnsuresClauseValuesTranslationOnly(element).stream().map(clauseTransformer).forEach(verifastContract::addEnsuresPredAfter);
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

            receiverPacked.add(getOwnFieldsPredicateUse(receiverPackingType, receiverType.getUnderlyingType(), "this", f -> "?this_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
            printlnAligned(receiverPacked.toString());
        }

        List<VariableElement> allFields = enclClass.type == null
                ? List.of()
                : ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());
        for (VariableElement field : allFields) {
            VerifastClause fieldAssertion = new VerifastClause("assert", false);
            VerifastContract fieldAssumption = new VerifastContract(false, false);

            if (!field.asType().getKind().isPrimitive()) {
                AnnotationMirror packingType =
                        propertyFactory.getAnnotatedType(field).getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
                String name = field.getSimpleName().toString();
                fieldAssertion.add(getOwnFieldsPredicateUse(
                        packingType,
                        field.asType(), "this_" + name + "_a" + enclClassAssertionSequenceCounter,
                        f -> "?" + name + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));

                fieldAssumption.addRequiresPred(getOwnFieldsPredicateUse(packingType, field.asType(), "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
                fieldAssumption.addEnsuresPred(getOwnFieldsPredicateUse(packingType, field.asType(), "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                fieldAssumption.addEnsuresPred(getFieldTypesPredicateUse(packingType, field.asType(), "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            }

            for (LatticeVisitor.Result result : results) {
                List<VariableElement> uninitFields = result.getUninitializedFields(tree);
                AnnotatedTypeMirror type = result.getTypeFactory().getAnnotatedType(field);
                PropertyAnnotation pa = result.getLattice().getEffectivePropertyAnnotation(type);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial() && !pat.isInv()) {
                    boolean wt = !uninitFields.contains(field);

                    if (wt) {
                        String name = field.getSimpleName().toString();
                        fieldAssumption.addEnsuresPred(new PredicateUse(pa, name, f -> "arg_" + f.getSimpleName() + "_a"));
                    } else {
                        String name = field.getSimpleName().toString();
                        fieldAssertion.add(new PredicateUse(
                                pa,
                                "this_" + name + "_a" + enclClassAssertionSequenceCounter,
                                f -> name + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                    }
                    assumptions.add(fieldAssumption);
                    assertions.add(fieldAssertion);
                }
            }

            enclClassAssumptionsToGenerate.add(Pair.of(field.asType(), fieldAssumption));
            printlnAligned(String.format("assume%s(this.%s);", enclClassAssumptionCounter++, field.getSimpleName()));
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

        if (!underlyingType.getKind().isPrimitive()) {
            assertion.add(getOwnFieldsPredicateUse(
                    packingType,
                    underlyingType, "arg",
                    f -> "?" + subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter
            ));

            assumption.addRequiresPred(getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
            assumption.addEnsuresPred(getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            assumption.addEnsuresPred(getFieldTypesPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
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
            if (wt) {
                assumption.addEnsuresPred(new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                ++assumptions;
            } else {
                assertion.add(new PredicateUse(
                        pa,
                        subject,
                        f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                ++assertions;
            }
        }

        if (underlyingType.getKind().isPrimitive() && assertion.getPreds().size() == 0) {
            assertion = null;
        } else if (!underlyingType.getKind().isPrimitive() && assertion.getPreds().size() == 1) {
            assertion = null;
        }

        return Pair.of(assertion, assumption);
    }

    protected Pair<VerifastClause, VerifastContract> getConditions(JCTree.JCVariableDecl tree, String subject) {
        VerifastClause assertion = new VerifastClause("assert", false);
        VerifastContract assumption = new VerifastContract(false, false);

        AnnotatedTypeMirror packingTypeMirror = propertyFactory.getAnnotatedTypeLhs(tree);
        AnnotationMirror packingType = packingTypeMirror.getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
        TypeMirror underlyingType = packingTypeMirror.getUnderlyingType();
        String frame = unannotatedSimpleTypeName(getTypeFrame(packingType, underlyingType), false);
        if (frame.equals("Object")) {
            packingTypeMirror = propertyFactory.getAnnotatedType(tree.getInitializer());
            packingType = packingTypeMirror.getEffectiveAnnotationInHierarchy(propertyFactory.getInitialized());
            underlyingType = packingTypeMirror.getUnderlyingType();
            frame = unannotatedSimpleTypeName(getTypeFrame(packingType, underlyingType), false);
        }

        if (!underlyingType.getKind().isPrimitive() && !frame.equals("Object")) {
            assertion.add(getOwnFieldsPredicateUse(
                    packingType,
                    underlyingType, "arg",
                    f -> "?" + subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter
            ));

            assumption.addRequiresPred(getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "?arg_" + f.getSimpleName() + "_a"));
            assumption.addEnsuresPred(getOwnFieldsPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
            assumption.addEnsuresPred(getFieldTypesPredicateUse(packingType, underlyingType, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
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
            if (wt) {
                assumption.addEnsuresPred(new PredicateUse(pa, "arg", f -> "arg_" + f.getSimpleName() + "_a"));
                ++assumptions;
            } else {
                assertion.add(new PredicateUse(
                        pa,
                        subject,
                        f -> subject + "_" + f.getSimpleName() + "_a" + enclClassAssertionSequenceCounter));
                ++assertions;
            }
        }

        if (underlyingType.getKind().isPrimitive() && assertion.getPreds().size() == 0) {
            assertion = null;
        } else if (!underlyingType.getKind().isPrimitive() && assertion.getPreds().size() == 1) {
            assertion = null;
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
        private List<String> additionalRequiresClausesBefore;
        private List<String> additionalEnsuresClausesBefore;
        private List<String> additionalRequiresClausesAfter;
        private List<String> additionalEnsuresClausesAfter;

        public VerifastContract(boolean requiresPermission, boolean ensuresPermission) {
            this.requiresClause = new VerifastClause("requires", requiresPermission);
            this.ensuresClause = new VerifastClause("ensures", ensuresPermission);
            this.additionalRequiresClausesBefore = new ArrayList<>();
            this.additionalEnsuresClausesBefore = new ArrayList<>();
            this.additionalRequiresClausesAfter = new ArrayList<>();
            this.additionalEnsuresClausesAfter = new ArrayList<>();
        }

        public void addRequiresPred(PredicateUse req) {
            requiresClause.add(req);
        }

        public void addEnsuresPred(PredicateUse ens) {
            ensuresClause.add(ens);
        }

        public void addRequiresPredBefore(String req) {
            additionalRequiresClausesBefore.add(req);
        }

        public void addEnsuresPredBefore(String ens) {
            additionalEnsuresClausesBefore.add(ens);
        }

        public void addRequiresPredAfter(String req) {
            additionalRequiresClausesAfter.add(req);
        }

        public void addEnsuresPredAfter(String ens) {
            additionalEnsuresClausesAfter.add(ens);
        }

        @Override
        public String toString() {
            StringJoiner reqBefore = new StringJoiner(" &*& ");
            StringJoiner ensBefore = new StringJoiner(" &*& ");
            additionalRequiresClausesBefore.forEach(reqBefore::add);
            additionalEnsuresClausesBefore.forEach(ensBefore::add);
            StringJoiner reqAfter = new StringJoiner(" &*& ");
            StringJoiner ensAfter = new StringJoiner(" &*& ");
            additionalRequiresClausesAfter.forEach(reqAfter::add);
            additionalEnsuresClausesAfter.forEach(ensAfter::add);

            String reqStr = requiresClause.toString(false);
            if (reqAfter.length() != 0) {
                reqStr = reqStr + " &*& " + reqAfter;
            }
            String ensStr = ensuresClause.toString(false);
            if (ensAfter.length() != 0) {
                ensStr = ensStr + " &*& " + ensAfter;
            }

            if (reqBefore.length() != 0) {
                reqStr = reqBefore + " &*& " + reqStr;
            }
            if (ensBefore.length() != 0) {
                ensStr = ensBefore + " &*& " + ensStr;
            }

            return "//@ requires " + reqStr + ";\n//@ ensures " + ensStr + ";";
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

        public List<PredicateUse> getPreds() {
            return preds;
        }

        @Override
        public String toString() {
            return toString(true);
        }

        public String toString(boolean withClauseType) {
            StringJoiner sj = new StringJoiner(" &*& ");
            if (permission) {
                preds.stream().map(PredicateUse::toString).forEach(sj::add);
            } else {
                preds.stream().forEach(p -> sj.add("[_](" + p + ")"));
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
