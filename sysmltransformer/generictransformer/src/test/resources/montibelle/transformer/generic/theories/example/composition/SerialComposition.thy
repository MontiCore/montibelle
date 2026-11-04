theory SerialComposition
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) io.Input io.Output connector.Connectors_Serial instance.SpecificationInstance instance.SpecificationInstance2 io.SerialFeedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2) .
    ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)
  = ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "Instance1Input.buildSB"
               "Instance2Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_h1_map_def)+

definition rawinput_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_map \<equiv>
    \<lambda> (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2) .
    ((natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)
  = ((natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "Connector2Input.buildSB"
               "RawInput_h1.constructor"
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
  \<lambda> (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) .
  ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)
  = ((natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "Instance1Output.buildSB"
               "Instance2Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_h1_map_def)+

definition rawoutput_map ::
  "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
  ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawoutput_map \<equiv>
  \<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2) .
  ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)
  = ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "Connector2Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_map_def)+





abbreviation "SerialComposition_rawinput2Connectors_Serial \<equiv> (fst o rawinput_map)"

abbreviation "SerialComposition_rawoutput2Connectors_Serial \<equiv> (fst o rawoutput_map)"

interpretation Connectors_Serial_input_Sub:
    subsetGen "RawInput.constructor" "Connector2Input.buildSB" "SerialComposition_rawinput2Connectors_Serial"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation Connectors_Serial_output_Sub:
    subsetGen "RawOutput.constructor" "Connector2Output.buildSB" "SerialComposition_rawoutput2Connectors_Serial"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "SerialComposition_rawinput2SpecificationInstance \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "SerialComposition_rawoutput2SpecificationInstance \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation SpecificationInstance_input_Sub:
    subsetGen "RawInput.constructor" "Instance1Input.buildSB" "SerialComposition_rawinput2SpecificationInstance"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance_output_Sub:
    subsetGen "RawOutput.constructor" "Instance1Output.buildSB" "SerialComposition_rawoutput2SpecificationInstance"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "SerialComposition_rawinput2SpecificationInstance2 \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "SerialComposition_rawoutput2SpecificationInstance2 \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation SpecificationInstance2_input_Sub:
    subsetGen "RawInput.constructor" "Instance2Input.buildSB" "SerialComposition_rawinput2SpecificationInstance2"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance2_output_Sub:
    subsetGen "RawOutput.constructor" "Instance2Output.buildSB" "SerialComposition_rawoutput2SpecificationInstance2"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2serialcomposition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawinput2serialcomposition
    (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)
  = (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)"

interpretation SerialComposition_input_Sub:
    subsetGen "RawInput.constructor"
              "Input.buildSB"
              "rawinput2serialcomposition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: Input.buildSB_def
               Connector2Input.buildSB_def
               Instance1Input.buildSB_def
               Instance2Input.buildSB_def)+

fun rawoutput2serialcomposition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2serialcomposition
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)
  = (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"

interpretation SerialComposition_output_Sub:
    subsetGen "RawOutput.constructor"
              "Output.buildSB"
              "rawoutput2serialcomposition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: Output.buildSB_def
               Connector2Output.buildSB_def
               Instance1Output.buildSB_def
               Instance2Output.buildSB_def)+


fun rawinput2serialcomposition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawinput2serialcomposition_feedback
    (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "SerialFeedback.buildSB"
              "rawinput2serialcomposition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: SerialFeedback.buildSB_def
               Connector2Input.buildSB_def
               Instance1Input.buildSB_def
               Instance2Input.buildSB_def)+

fun rawoutput2serialcomposition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2serialcomposition_feedback
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "SerialFeedback.buildSB"
              "rawoutput2serialcomposition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: SerialFeedback.buildSB_def
               Connector2Output.buildSB_def
               Instance1Output.buildSB_def
               Instance2Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((Connector2Input.channels \<union> (Instance1Input.channels \<union> Instance2Input.channels) - Instance1Output.channels \<union> Instance2Output.channels) - Connector2Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels)\<^sup>\<Omega> \<rightarrow> (Connector2Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). Connectors_Serial.Sps () \<Otimes> SpecificationInstance.Sps () \<Otimes> SpecificationInstance2.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (Input.channels) = chDom TYPE(((Connector2Input.channels \<union> (Instance1Input.channels \<union> Instance2Input.channels) - Instance1Output.channels \<union> Instance2Output.channels) - Connector2Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (Output.channels) \<subseteq> chDom TYPE((Connector2Output.channels \<union> Instance1Output.channels \<union> Instance2Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma Connectors_Serial_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma Connectors_Serial_output_eq:
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
    shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma SpecificationInstance2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)"
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

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "Connectors_Serial.connector\<cdot>(Connector2Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (Connector2Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst Connectors_Serial_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst Connectors_Serial_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: Connectors_Serial.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(SerialFeedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (SerialFeedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
