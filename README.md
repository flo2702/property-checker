# Property Checker

The Property Checker is a checker developed using the Checker Framework for Java. The Checker Framework allows programmers to leverage Java annotations to create pluggable Java type systems. Unlike other checkers in the CF, the Property Checker allows users to specify custom refinement-type qualifiers and qualifier hierarchies using a simple definition language.

For example, a non-null qualifier can be defined by the following line:
`annotation NonNull() java.lang.Object :<==> "§subject§ != null" for "true";`

An object `o` has the type `@NonNull Object` if the specified property `o != null` always evaluates to `true`.

If the Property Checker can't completely prove a program's well-typedness, it translates all type qualifiers into specification clauses in some other specification language. Currently available languages are the Java Modeling Language (JML) or Verifast. This translation can be given to a deductive verification tool like KeY or Verifast to prove those parts of the program which the checker couldn't prove. This approach combines the scalability and ease-of-use of pluggable type system with the power of deductive verification.

In addition to refinement types, the Property Checker contains a uniqueness type system and a packing type system (a generalization of the CF's initialization type system where initialized variables can be uninitialized and reinitialized), allowing for sound support of dependent types that depend on mutable program variables.

For more documentation on the theory behind the Property Checker, see the following publications:

[1] Florian Lanzinger, Alexander Weigl, Mattias Ulbrich, and Werner Dietl (2021). Scalability and Precision by Combining Expressive Type Systems and Deductive Verification. Proceedings of the ACM on programming languages, 5(OOPSLA). https://dx.doi.org/10.1145/3485520

[2] Florian Lanzinger, Joshua Bachmeier, Mattias Ulbrich, and Werner Dietl (2023). Scalable and Precise Refinement Types for Imperative Languages. iFM 2023. https://dx.doi.org/10.1007/978-3-031-47705-8_20

# Tests

See the folder `tests` for examples.

To run a specific test case, use `./gradlew clean test --tests <name of test case>`, e.g., `./gradlew clean test --tests NullnessTest` to run `tests.property.NullnessTest`.

To create your own test case, create a class extending `PropertyCheckerTest` that points to the source-code directory as well as the lattice files for the required type lattices.
See the existing test cases for examples.

# Building and running

After the first clone, the Checker Framework submodule must be initialized via `git submodule init && git submodule update`, then compiled via `cd checker-framework ; ./gradlew assemble`.

To build the Property Checker, run `./gradlew assemble`. The file `property-checker.jar` will be generated in the main directory. To be able to run the Property Checker, the files `property-checker.jar`, `checker-qual.jar`, and `javac` (not the regular Java compiler, but the one included here!) must be kept in the same directory.

To run the checker, use the following command. Arguments in [square brackets] are optional.

```
./javac \
-cp property-checker.jar:\
<qualifier_files> \
-processor edu.kit.iti.checker.property.checker.PropertyChecker \
<files_to_check> \
-APropertyChecker_inDir=<your_project_root> \
-APropertyChecker_outDir=<out_dir> \
-APropertyChecker_lattices=<lattice_file> \
-APropertyChecker_qualPkg=<qual_pkg> \
[-APropertyChecker_outputLang=<output_lang>]
[-APropertyChecker_translationOnly=<translation_only>]
[-APropertyChecker_shouldNotUseTrampoline=<should_not_use_trampoline>]
[-APropertyChecker_keepGenerics=<keep_generics>]
[-APropertyChecker_noExclusivity=<no_exclusivity>]
[-APropertyChecker_noInferUnpack=<no_infer_unpack>]
[-AconcurrentSemantics=<concurrent_semantics>]
[<nullness checker options>]
```

where

* `./java` is not the regular Java compiler, but the one included with the Property Checker.
* `<lattice_file>` is the file containing the definition of your qualifier hierarchy. You can specify multiple files by separating them with a comma `,`.
* `<qualifier_files>` are the class files (or a JAR file containing the class files) for all annotations used in your qualifier hierarchy.
* `<files_to_check>` is the name of the file(s) which should be type-checked.
* `<your_project_root>` is the root directory for the source code of the project which should be checked. This is indeed redundant with the previous option. It is there because it is necessary for the Property Checker to know not just the files it should check, but also the file/package structure of the project.
* `<out_dir>` is the directory to which the JML translation should be written.
* `<qual_pkg>` is the fully qualified name of the package containing all annotations.
* `<output_lang>` is `jml` or `verifast` depending on what language you want for the translation. The default is `jml`.
* `<translation_only>` is `true` if you want to only run the JML/Verifast translator without running the Property Checker beforehand. The default is `false`.
* `<should_not_use_trampoline>` is a comma-separated list of package-name prefixes. By default, the translation replaces method calls to `foo()` with calls to a generated method `foo_trampoline()`, which allows for a more precise translation. To suppress this replacement for methods in specific packages, add the package name or a prefix of the package name to this list.
* `<keep_generics>` is `true` if you want the Property Checker to keep generic types in the translation and `false` if you want generics to be erased. The default is `false`.
* `<no_exclusivity>` is `true` if you want to suppress checking of uniqueness types. The default is `false`.
* `<no_infer_unpack>` is `true` if you want the Property Checker to never automatically infer pack/unpack statements for the packing type system. The default is `false`.
* `<concurrent_semantics>` is `true` if you want to disable type refinements that are unsound in concurrent programs. The default is `false`. See https://eisop.github.io/cf/manual/manual.html#faq-concurrency
* `<nullness checker options>` The Property Checker includes a custom version of the CF's Nullness Checker and supports most of its options. See https://eisop.github.io/cf/manual/manual.html#nullness-checker
