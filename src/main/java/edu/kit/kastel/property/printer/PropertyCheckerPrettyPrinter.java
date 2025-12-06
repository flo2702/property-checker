package edu.kit.kastel.property.printer;

import com.sun.source.tree.MemberReferenceTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import org.apache.commons.lang3.StringUtils;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Name;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.ElementFilter;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.INTERFACE;

/**
 * Super class for {@link JavaJMLPrinter} and {@link JavaVerifastPrinter}
 * with common functionality.
 */
@SuppressWarnings("nls")
public abstract class PropertyCheckerPrettyPrinter extends PrettyPrinter {

    public static boolean TRANSLATION_RAW = false;

    protected List<LatticeVisitor.Result> results;
    protected PropertyAnnotatedTypeFactory propertyFactory;
    protected ExclusivityAnnotatedTypeFactory exclFactory;

    protected int assertions = 0;
    protected int assumptions = 0;
    protected int methodCallPreconditions = 0;
    protected int freeMethodCallPreconditions = 0;
    protected int methodCallPostconditions = 0;
    protected int freeMethodCallPostconditions = 0;

    protected int tempVarNum = 0;
    protected JCTree.JCClassDecl enclClass;
    protected JCTree.JCMethodDecl enclMethod;
    protected boolean enclBlock = false;

    public PropertyCheckerPrettyPrinter(
            List<LatticeVisitor.Result> results,
            PropertyChecker propertyChecker,
            BufferedWriter out) {
        super(out, true);
        this.results = results;
        this.propertyFactory = propertyChecker.getPropertyFactory();
        this.exclFactory = propertyFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);

        String translationOnlyOption = propertyChecker.getOption(Config.TRANSLATION_ONLY_OPTION);

        if (Objects.equals(translationOnlyOption, "true")) {
            TRANSLATION_RAW = true;
        }
    }

    public int getAssertions() {
        return assertions;
    }

    public int getAssumptions() {
        return assumptions;
    }

    public int getMethodCallPreconditions() {
        return methodCallPreconditions;
    }

    public int getFreeMethodCallPreconditions() {
        return freeMethodCallPreconditions;
    }

    public int getMethodCallPostconditions() {
        return methodCallPostconditions;
    }

    public int getFreeMethodCallPostconditions() {
        return freeMethodCallPostconditions;
    }

    protected String tempVarName() {
        return String.format("temp%d", tempVarNum++);
    }

    @Override
    public void visitImport(JCTree.JCImport tree) {
        String str = tree.qualid.toString();
        if (str.startsWith("edu.kit.kastel.property")
                || str.startsWith("org.checkerframework.")) {
            return;
        }

        super.visitImport(tree);
    }

    @Override
    public void printTypeParameters(com.sun.tools.javac.util.List<JCTree.JCTypeParameter> trees) throws IOException {
        if (propertyFactory.getChecker().shouldKeepGenerics()) {
            super.printTypeParameters(trees);
        }
    }

    @Override
    public void visitReference(JCTree.JCMemberReference tree) {
        try {
            this.printExpr(tree.expr);
            this.print("::");
            if (tree.typeargs != null && propertyFactory.getChecker().shouldKeepGenerics()) {
                this.print('<');
                this.printExprs(tree.typeargs);
                this.print('>');
            }

            this.print(tree.getMode() == MemberReferenceTree.ReferenceMode.INVOKE ? tree.name : "new");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitTypeApply(JCTree.JCTypeApply tree) {
        try {
            this.printExpr(tree.clazz);
            if (propertyFactory.getChecker().shouldKeepGenerics()) {
                this.print('<');
                this.printExprs(tree.arguments);
                this.print('>');
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected static Object getVisibilityString(EnumSet<Flags.Flag> flagSet) {
        if (flagSet.contains(Flags.Flag.PUBLIC)) {
            return "public";
        } else if (flagSet.contains(Flags.Flag.PROTECTED)) {
            return "protected";
        } else if (flagSet.contains(Flags.Flag.PRIVATE)) {
            return "private";
        } else {
            return "";
        }
    }

    @Override
    public void visitBlock(JCTree.JCBlock tree) {
        boolean prevEnclBlock = enclBlock;
        if (enclMethod != null || enclBlock) {
            enclBlock = true;
            try {
                printBlock(tree.stats);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        enclBlock = prevEnclBlock;
    }

    @Override
    public void visitModifiers(JCTree.JCModifiers mods) {
        try {
            printFlags(mods.flags);
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
                printUnpackStatement(enclMethod, unpackFrame.toString());
            } else if (packFrame != null) {
                printPackStatement(enclMethod, packFrame.toString());
            }
        } catch (IOException e) {
            throw new java.io.UncheckedIOException(e);
        }

        super.visitReturn(tree);
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

    protected abstract void printPackStatement(Tree tree, String frame) throws IOException;
    protected abstract void printUnpackStatement(Tree tree, String frame) throws IOException;

    @Override
    public void printTypeAnnotations(com.sun.tools.javac.util.List<JCTree.JCAnnotation> trees) throws IOException {
        // do nothing
    }

    protected void printlnAligned(String s) {
        for (String line : s.lines().collect(Collectors.toList())) {
            try {
                align();
                println(line);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
    }

    protected static List<VariableElement> nonStaticDependableFieldsInFrame(TypeMirror frame) {
        List<VariableElement> res = ElementFilter.fieldsIn(TypesUtils.getTypeElement(frame).getEnclosedElements());
        res.removeIf(ElementUtils::isStatic);
        res.removeIf(f -> !PackingAnnotatedTypeFactory.isDependableField(f));
        return res;
    }

    protected void println(String s) throws IOException {
        print(s + StringUtils.LF);
    }

    protected void print() throws IOException {
        print(StringUtils.EMPTY);
    }

    protected static boolean isAbstract(JCTree.JCClassDecl tree) {
        return (tree.mods.flags & ABSTRACT) != 0;
    }

    protected static boolean isInterface(JCTree.JCClassDecl tree) {
        return (tree.mods.flags & INTERFACE) != 0;
    }

    protected static boolean isConstructor(JCTree.JCMethodDecl tree) {
        return tree.name == tree.name.table.names.init;
    }

    protected String unannotatedTypeName(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedType(tree);
        return unannotatedTypeName(type, false);
    }

    protected String unannotatedNullableTypeName(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedType(tree);
        return unannotatedTypeName(type, true);
    }

    protected String unannotatedTypeNameLhs(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree);
        return unannotatedTypeName(type, false);
    }

    protected String unannotatedNullableTypeNameLhs(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree);
        return unannotatedTypeName(type, true);
    }

    protected String unannotatedTypeName(AnnotatedTypeMirror type) {
        return unannotatedTypeName(type, false);
    }

    protected String unannotatedTypeName(AnnotatedTypeMirror type, boolean nullable) {
        return unannotatedTypeName(type.getUnderlyingType(), nullable);
    }

    protected String unannotatedTypeName(TypeMirror type, boolean nullable) {
        if (type instanceof AnnotatedTypeMirror.AnnotatedExecutableType) {
            throw new IllegalArgumentException();
        }

        String unannotatedTypeName;
        if ((type instanceof Type.TypeVar || type instanceof Type.DelegatedType)
                && !propertyFactory.getChecker().shouldKeepGenerics()) {
            unannotatedTypeName = "Object";
        } else if (type instanceof Type.ArrayType arrType) {
            unannotatedTypeName = unannotatedTypeName(arrType.elemtype, false) + "[]";
        } else {
            unannotatedTypeName = ((Type) type).asElement().toString();;
        }

        return (!nullable || type.getKind() == TypeKind.VOID || type.getKind().isPrimitive()
                ? "" : "/*@nullable@*/ ")
                + unannotatedTypeName;
    }

    public Name getEnclClassName() {
        return enclClass.sym.getQualifiedName();
    }

    public Name getEnclMethodName() {
        return enclMethod.sym.getQualifiedName();
    }

    public AnnotationMirror getTop(GenericAnnotatedTypeFactory<?,?,?,?> factory) {
        return factory.getQualifierHierarchy().getTopAnnotations().first();
    }
}
