# Replicating the "web shop" case study from our paper:

## KeY + Property Checker version

1. Navigate to the `property-checker` directory.
2. Run `./gradlew clean test --tests CaseStudyMutableTest`. The JML translation will be written to `../property-checker-out`. If there is a problem, find the expected translation in `web_shop_case_study/src_key_enh` and copy it there.
3. Run `cd web_shop_case_study && ./runKey.sh`.
4. Load the finished proofs from the directories `web_shop_case_study/Proofs list` and `web_shop_case_study/Proofs order`.
5. The proofs' run times and number of manual steps are shown upon loading. Alternatively, they can be found by opening the proof files in a text editor.


## KeY only version

1. Navigate to the `property-checker` directory.
2. Run `./gradlew clean test --tests CaseStudyMutableTest -DtranslationOnly=true`. The JML translation will be written to `../property-checker-out`. If there is a problem, find the expected translation in `web_shop_case_study/src_key_raw` and copy it there.
3. Run `cd web_shop_case_study && ./runKey.sh`.
4. Load the finished proofs from the directories `web_shop_case_study/Proofs list raw` and `web_shop_case_study/Proofs order raw` and `web_shop_case_study/Proofs client raw`.
5. The proofs' run times and number of manual steps are shown upon loading. Alternatively, they can be found by opening the proof files in a text editor.


## Verifast + Property Checker version

1. Navigate to the `property-checker` directory.
2. Run `./gradlew clean test --tests CaseStudyMutableVerifastTest`. The Verifast translation will be written to `../property-checker-out`. If there is a problem, find the expected translation in `web_shop_case_study/src_verifast_enh` and copy it there.
3. Run `cd web_shop_case_study && time ./verifast_enh.sh`.


## Verifast only version

1. Navigate to the `property-checker` directory.
2. Run `./gradlew clean test --tests CaseStudyMutableVerifastTest -DtranslationOnly=true`. The Verifast translation will be written to `../property-checker-out`. If there is a problem, find the expected translation in `web_shop_case_study/src_verifast_raw` and copy it there.
3. Run `cd web_shop_case_study && time ./verifast_raw.sh`.
