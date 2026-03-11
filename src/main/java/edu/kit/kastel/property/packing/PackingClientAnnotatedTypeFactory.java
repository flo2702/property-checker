package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import edu.kit.kastel.property.packing.qual.NonMonotonic;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.dataflow.cfg.visualize.DOTCFGVisualizer;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.UserError;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.type.TypeKind;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

public abstract class PackingClientAnnotatedTypeFactory<
        Value extends PackingClientValue<Value>,
        Store extends PackingClientStore<Value, Store>,
        TransferFunction extends PackingClientTransfer<Value, Store, TransferFunction>,
        FlowAnalysis extends PackingClientAnalysis<Value, Store, TransferFunction>>
        extends GenericAnnotatedTypeFactory<Value, Store, TransferFunction, FlowAnalysis> {

    private boolean useInputTypeLhs;

    protected PackingClientAnnotatedTypeFactory(BaseTypeChecker checker, boolean useFlow) {
        super(checker, useFlow);
    }

    protected PackingClientAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        // Unrefined aliases are handled by the Exclusivity Checker, so we deactivate the imprecise default handling.
        sideEffectsUnrefineAliases = false;
    }

    public void setUseInputTypeLhs(boolean useInputTypeLhs) {
        this.useInputTypeLhs = useInputTypeLhs;
    }

    @Override
    public AnnotatedTypeMirror getAnnotatedTypeLhs(Tree lhsTree) {
        AnnotatedTypeMirror annotatedType = super.getAnnotatedTypeLhs(lhsTree);

        if (!useInputTypeLhs) {
            Tree containingMethod = getEnclosingClassOrMethod(lhsTree);
            // For method parameters, the lhs type is always @ReadOnly
            if (lhsTree instanceof IdentifierTree && containingMethod instanceof MethodTree) {
                boolean isParam = ((IdentifierTree) lhsTree).getName().toString().equals("this");
                for (VariableTree param : ((MethodTree) containingMethod).getParameters()) {
                    isParam |= param.getName().equals(((IdentifierTree) lhsTree).getName());
                }

                if (isParam) {
                    annotatedType.replaceAnnotations(getQualifierHierarchy().getTopAnnotations());
                }
            }
        }

        return annotatedType;
    }

    @Override
    public AnnotationMirrorSet getExplicitNewClassAnnos(NewClassTree newClassTree) {
        // Return empty set so that the type visitor adds the annotation from the return type.
        return AnnotationMirrorSet.emptySet();
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(3);
        treeAnnotators.add(new PropagationTreeAnnotator(this));
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    public abstract AnnotationMirror getDefaultPrimitiveQualifier();
    public abstract AnnotationMirror getDefaultStringQualifier();

    @Override
    public AnnotatedTypeMirror.AnnotatedDeclaredType getSelfType(Tree tree) {
        if (TreeUtils.isClassTree(tree)) {
            return getAnnotatedType(TreeUtils.elementFromDeclaration((ClassTree) tree));
        }

        Tree enclosingTree = getEnclosingClassOrMethod(tree);
        if (enclosingTree == null) {
            // tree is inside an annotation, where "this" is not allowed. So, no self type exists.
            return null;
        } else if (enclosingTree.getKind() == Tree.Kind.METHOD) {
            MethodTree enclosingMethod = (MethodTree) enclosingTree;
            if (TreeUtils.isConstructor(enclosingMethod)) {
                return (AnnotatedTypeMirror.AnnotatedDeclaredType) getAnnotatedType(enclosingMethod).getReturnType();
            } else {
                return getAnnotatedType(enclosingMethod).getReceiverType();
            }
        } else if (TreeUtils.isClassTree(enclosingTree)) {
            return (AnnotatedTypeMirror.AnnotatedDeclaredType) getAnnotatedType(enclosingTree);
        }
        return null;
    }

    @Override
    public @Nullable Value getInferredValueFor(Tree tree) {
        final Store store = flowResult.getStoreBefore(tree);
        Set<Node> nodes = flowResult.getNodesForTree(tree);

        if (store == null || nodes == null) {
            return null;
        }

        return nodes.stream()
                .map(node -> {
                    JavaExpression expr;
                    if (node instanceof ValueLiteralNode
                            || node instanceof BinaryOperationNode
                            || node instanceof UnaryOperationNode) {
                        if (node.getType().getKind().isPrimitive()) {
                            return analysis.createAbstractValue(AnnotationMirrorSet.singleton(getDefaultPrimitiveQualifier()), node.getType());
                        } else if (node.getType().getKind().equals(TypeKind.NULL)) {
                            return analysis.createAbstractValue(getAnnotatedNullType(Set.of()));
                        } else {
                            // We already dealt with primitives and null, so node must be a String
                            return analysis.createAbstractValue(AnnotationMirrorSet.singleton(getDefaultStringQualifier()), node.getType());
                        }
                    } else if (node instanceof MethodInvocationNode) {
                        return store.getValue((MethodInvocationNode) node);
                    } else if (node instanceof FieldAccessNode) {
                        return store.getValue((FieldAccessNode) node);
                    } else if (node instanceof ArrayAccessNode) {
                        return store.getValue((ArrayAccessNode) node);
                    } else if (node instanceof LocalVariableNode) {
                        return store.getValue((LocalVariableNode) node);
                    } else if (node instanceof ThisNode) {
                        return store.getValue((ThisNode) node);
                    } else {
                        return null;  // No refined value available
                    }})
                .filter(Objects::nonNull)
                .reduce(Value::leastUpperBound)
                .orElse(null);
    }

    @Override
    protected void applyInferredAnnotations(AnnotatedTypeMirror type, Value inferred) {
        type.replaceAnnotations(inferred.getAnnotations());
    }

    @Override
    protected @Nullable CFGVisualizer<Value, Store, TransferFunction> createCFGVisualizer() {
        if (checker.hasOption("flowdotdir")) {
            try {
                Files.createDirectories(Path.of(checker.getOption("flowdotdir")));
            } catch (IOException e) { }
            String flowdotdir = checker.getOption("flowdotdir");
            if (flowdotdir.equals("")) {
                throw new UserError("Empty string provided for -Aflowdotdir command-line argument");
            }
            boolean verbose = checker.hasOption("verbosecfg");

            Map<String, Object> args = new HashMap<>(2);
            args.put("outdir", flowdotdir);
            args.put("verbose", verbose);
            args.put("checkerName", getFlowdotFilenamePostfix());

            CFGVisualizer<Value, Store, TransferFunction> res = new DOTCFGVisualizer<>();
            res.init(args);
            return res;
        } else {
            return super.createCFGVisualizer();
        }
    }

    protected String getFlowdotFilenamePostfix() {
        String checkerName = checker.getClass().getSimpleName();
        if (checkerName.endsWith("Checker")) {
            checkerName = checkerName.substring(0, checkerName.length() - "Checker".length());
        } else if (checkerName.endsWith("Subchecker")) {
            checkerName = checkerName.substring(0, checkerName.length() - "Subchecker".length());
        }
        return checkerName;
    }

    public boolean isMonotonicMethod(MethodTree tree) {
        return isMonotonicMethod(TreeUtils.elementFromDeclaration(tree));
    }

    public boolean isMonotonicMethod(Element el) {
        return !AnnotationUtils.containsSameByClass(getDeclAnnotations(el), NonMonotonic.class);
    }
}
