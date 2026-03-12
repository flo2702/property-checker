Replicating the Daikon case study from our paper:

1. Navigate to the `property-checker` directory.
2. Run `./gradlew clean test --tests DaikonTest`. The JML translation will be written to `../property-checker-out`. If there is a problem, find the expected translation in `daikon_case_study/expected-jml` and copy it there.
3. Run `cd daikon_case_study && ./runKey.sh`.
4. Load the proof obligations corresponding to all methods that are not syntactically well-typed (`File->Proof Management)`) and prove them by pressing the green button in the top left of the screen as many times as it takes until the proof closes:
    1. `UnionVisitor.visit(daikon.diff.PptNode): JML normal_behavior operation contract 0`
    2. `UnionVisitor.visit(daikon.diff.InvNode): JML normal_behavior operation contract 0`
    3. `XorVisitor.visit(daikon.diff.PptNode): JML normal_behavior operation contract 0`
    4. `DetailedStatisticsVisitor.visit(daikon.diff.InvNode): JML normal_behavior operation contract 0`
    5. `DetailedStatisticsVisitor.addFrequency: JML normal_behavior operation contract 0`
    6. `DetailedStatisticsVisitor.determinteArity: JML normal_behavior operation contract 0`
    7. `MatchCountVisitor.visit(daikon.diff.InvNode): JML normal_behavior operation contract 0`
    8. `MatchCountVisitor.visitInv1: JML normal_behavior operation contract 0`
    9. `MatchCountVisitor.shouldPrint: JML normal_behavior operation contract 0`
