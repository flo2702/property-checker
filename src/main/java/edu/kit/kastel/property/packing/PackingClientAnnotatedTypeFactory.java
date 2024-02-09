package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.Unknown;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Set;

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

    @Override
    public AnnotatedTypeMirror.AnnotatedNullType getAnnotatedNullType(Set<? extends AnnotationMirror> annotations) {
        AnnotatedTypeMirror.AnnotatedNullType result = super.getAnnotatedNullType(annotations);
        result.replaceAnnotation(getDefaultPrimitiveQualifier());
        return result;
    }

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
                        return analysis.createAbstractValue(AnnotationMirrorSet.singleton(getDefaultPrimitiveQualifier()), node.getType());
                    } else if (!((expr = JavaExpression.fromNode(node)) instanceof Unknown)) {
                        return store.getValue(expr);
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
        }
        return super.createCFGVisualizer();
    }
}
