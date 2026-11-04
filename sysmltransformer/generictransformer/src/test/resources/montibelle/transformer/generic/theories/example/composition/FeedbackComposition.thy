theory FeedbackComposition
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) io.EmptyBundle io.Output connector.Connectors_Feedback instance.SpecificationInstance instance.SpecificationInstance2 instance.SpecificationInstance3 io.FeedbackFeedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3) .
    ((natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2), (natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)
  = ((natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2), (natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "Instance2Input.buildSB"
               "Instance3Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_h1_map_def)+

definition rawinput_h2_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3) .
    ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)
  = ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "Instance1Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_h2_map_def)+

definition rawinput_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_map \<equiv>
    \<lambda> (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3) .
    ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)
  = ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "Connector3Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_map_def)+



definition rawoutput_h1_map ::
  "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
  ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3) .
  ((natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2), (natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)
  = ((natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2), (natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "Instance2Output.buildSB"
               "Instance3Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_h1_map_def)+

definition rawoutput_h2_map ::
  "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
  ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3) .
  ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)
  = ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "Instance1Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_h2_map_def)+

definition rawoutput_map ::
  "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
  ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawoutput_map \<equiv>
  \<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3) .
  ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)
  = ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "Connector3Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_map_def)+





abbreviation "FeedbackComposition_rawinput2Connectors_Feedback \<equiv> (fst o rawinput_map)"

abbreviation "FeedbackComposition_rawoutput2Connectors_Feedback \<equiv> (fst o rawoutput_map)"

interpretation Connectors_Feedback_input_Sub:
    subsetGen "RawInput.constructor" "Connector3Input.buildSB" "FeedbackComposition_rawinput2Connectors_Feedback"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation Connectors_Feedback_output_Sub:
    subsetGen "RawOutput.constructor" "Connector3Output.buildSB" "FeedbackComposition_rawoutput2Connectors_Feedback"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "FeedbackComposition_rawinput2SpecificationInstance \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "FeedbackComposition_rawoutput2SpecificationInstance \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation SpecificationInstance_input_Sub:
    subsetGen "RawInput.constructor" "Instance1Input.buildSB" "FeedbackComposition_rawinput2SpecificationInstance"
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance_output_Sub:
    subsetGen "RawOutput.constructor" "Instance1Output.buildSB" "FeedbackComposition_rawoutput2SpecificationInstance"
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "FeedbackComposition_rawinput2SpecificationInstance2 \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "FeedbackComposition_rawoutput2SpecificationInstance2 \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation SpecificationInstance2_input_Sub:
    subsetGen "RawInput.constructor" "Instance2Input.buildSB" "FeedbackComposition_rawinput2SpecificationInstance2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance2_output_Sub:
    subsetGen "RawOutput.constructor" "Instance2Output.buildSB" "FeedbackComposition_rawoutput2SpecificationInstance2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "FeedbackComposition_rawinput2SpecificationInstance3 \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "FeedbackComposition_rawoutput2SpecificationInstance3 \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation SpecificationInstance3_input_Sub:
    subsetGen "RawInput.constructor" "Instance3Input.buildSB" "FeedbackComposition_rawinput2SpecificationInstance3"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance3_output_Sub:
    subsetGen "RawOutput.constructor" "Instance3Output.buildSB" "FeedbackComposition_rawoutput2SpecificationInstance3"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2feedbackcomposition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> unit" where
"rawinput2feedbackcomposition
    (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)
  = ()"

interpretation FeedbackComposition_input_Sub:
    subsetGen "RawInput.constructor"
              "emptybundle_buildSB"
              "rawinput2feedbackcomposition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add:
               Connector3Input.buildSB_def
               Instance1Input.buildSB_def
               Instance2Input.buildSB_def
               Instance3Input.buildSB_def)+

fun rawoutput2feedbackcomposition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2feedbackcomposition
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)
  = (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"

interpretation FeedbackComposition_output_Sub:
    subsetGen "RawOutput.constructor"
              "Output.buildSB"
              "rawoutput2feedbackcomposition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: Output.buildSB_def
               Connector3Output.buildSB_def
               Instance1Output.buildSB_def
               Instance2Output.buildSB_def
               Instance3Output.buildSB_def)+


fun rawinput2feedbackcomposition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawinput2feedbackcomposition_feedback
    (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "FeedbackFeedback.buildSB"
              "rawinput2feedbackcomposition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: FeedbackFeedback.buildSB_def
               Connector3Input.buildSB_def
               Instance1Input.buildSB_def
               Instance2Input.buildSB_def
               Instance3Input.buildSB_def)+

fun rawoutput2feedbackcomposition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2feedbackcomposition_feedback
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "FeedbackFeedback.buildSB"
              "rawoutput2feedbackcomposition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: FeedbackFeedback.buildSB_def
               Connector3Output.buildSB_def
               Instance1Output.buildSB_def
               Instance2Output.buildSB_def
               Instance3Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((Connector3Input.channels \<union> (Instance1Input.channels \<union> (Instance2Input.channels \<union> Instance3Input.channels) - Instance2Output.channels \<union> Instance3Output.channels) - Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels) - Connector3Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels)\<^sup>\<Omega> \<rightarrow> (Connector3Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). Connectors_Feedback.Sps () \<Otimes> SpecificationInstance.Sps () \<Otimes> SpecificationInstance2.Sps () \<Otimes> SpecificationInstance3.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (EmptyBundle.channels) = chDom TYPE(((Connector3Input.channels \<union> (Instance1Input.channels \<union> (Instance2Input.channels \<union> Instance3Input.channels) - Instance2Output.channels \<union> Instance3Output.channels) - Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels) - Connector3Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (Output.channels) \<subseteq> chDom TYPE((Connector3Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels \<union> Instance3Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma Connectors_Feedback_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma Connectors_Feedback_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma SpecificationInstance_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma SpecificationInstance_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma SpecificationInstance2_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma SpecificationInstance2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma SpecificationInstance3_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma SpecificationInstance3_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma SpecificationInstance_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (Instance1Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (Instance1Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst SpecificationInstance_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst SpecificationInstance_output_eq[OF assms(1)])
  by(pred_solver inst2def: SpecificationInstance.pred_inst2def assms: assms)
 

lemma SpecificationInstance2_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (Instance2Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (Instance2Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst SpecificationInstance2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst SpecificationInstance2_output_eq[OF assms(1)])
  by(pred_solver inst2def: SpecificationInstance2.pred_inst2def assms: assms)
 

lemma SpecificationInstance3_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (Instance3Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (Instance3Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst SpecificationInstance3_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst SpecificationInstance3_output_eq[OF assms(1)])
  by(pred_solver inst2def: SpecificationInstance3.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "Connectors_Feedback.connector\<cdot>(Connector3Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (Connector3Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst Connectors_Feedback_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst Connectors_Feedback_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: Connectors_Feedback.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(FeedbackFeedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (FeedbackFeedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (EmptyBundle.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
