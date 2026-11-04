theory Composition
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) io.Input io.Output connector.Connectors instance.SpecificationInstance io.Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_map ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
    ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawinput_map \<equiv>
    \<lambda> (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1) .
    ((natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)
  = ((natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1), (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "Connector1Input.buildSB"
               "Instance1Input.buildSB"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_map_def)+



definition rawoutput_map ::
  "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<Rightarrow>
  ((nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<times> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream))" where
"rawoutput_map \<equiv>
  \<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1) .
  ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)
  = ((natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern), (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "Connector1Output.buildSB"
               "Instance1Output.buildSB"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_map_def)+





abbreviation "Composition_rawinput2Connectors \<equiv> (fst o rawinput_map)"

abbreviation "Composition_rawoutput2Connectors \<equiv> (fst o rawoutput_map)"

interpretation Connectors_input_Sub:
    subsetGen "RawInput.constructor" "Connector1Input.buildSB" "Composition_rawinput2Connectors"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation Connectors_output_Sub:
    subsetGen "RawOutput.constructor" "Connector1Output.buildSB" "Composition_rawoutput2Connectors"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "Composition_rawinput2SpecificationInstance \<equiv> (snd o rawinput_map)"

abbreviation "Composition_rawoutput2SpecificationInstance \<equiv> (snd o rawoutput_map)"

interpretation SpecificationInstance_input_Sub:
    subsetGen "RawInput.constructor" "Instance1Input.buildSB" "Composition_rawinput2SpecificationInstance"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation SpecificationInstance_output_Sub:
    subsetGen "RawOutput.constructor" "Instance1Output.buildSB" "Composition_rawoutput2SpecificationInstance"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2composition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawinput2composition
    (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)
  = (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)"

interpretation Composition_input_Sub:
    subsetGen "RawInput.constructor"
              "Input.buildSB"
              "rawinput2composition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: Input.buildSB_def
               Connector1Input.buildSB_def
               Instance1Input.buildSB_def)+

fun rawoutput2composition ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2composition
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)
  = (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"

interpretation Composition_output_Sub:
    subsetGen "RawOutput.constructor"
              "Output.buildSB"
              "rawoutput2composition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: Output.buildSB_def
               Connector1Output.buildSB_def
               Instance1Output.buildSB_def)+


fun rawinput2composition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawinput2composition_feedback
    (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "Feedback.buildSB"
              "rawinput2composition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: Feedback.buildSB_def
               Connector1Input.buildSB_def
               Instance1Input.buildSB_def)+

fun rawoutput2composition_feedback ::
    "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)
  \<Rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" where
"rawoutput2composition_feedback
    (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)
  = (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "Feedback.buildSB"
              "rawoutput2composition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: Feedback.buildSB_def
               Connector1Output.buildSB_def
               Instance1Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((Connector1Input.channels \<union> Instance1Input.channels) - Connector1Output.channels \<union> Instance1Output.channels)\<^sup>\<Omega> \<rightarrow> (Connector1Output.channels \<union> Instance1Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). Connectors.Sps () \<Otimes> SpecificationInstance.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (Input.channels) = chDom TYPE(((Connector1Input.channels \<union> Instance1Input.channels) - Connector1Output.channels \<union> Instance1Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (Output.channels) \<subseteq> chDom TYPE((Connector1Output.channels \<union> Instance1Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma Connectors_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma Connectors_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma SpecificationInstance_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma SpecificationInstance_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma SpecificationInstance_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> Specification.Sps () \<Longrightarrow> P (Input.SB.getter\<cdot>sb) (Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (Instance1Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (Instance1Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst SpecificationInstance_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst SpecificationInstance_output_eq[OF assms(1)])
  by(pred_solver inst2def: SpecificationInstance.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "Connectors.connector\<cdot>(Connector1Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (Connector1Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst Connectors_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst Connectors_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: Connectors.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
