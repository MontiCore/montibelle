theory def_Composition
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_Composition.def_Composition_Input bundle_Composition.def_Composition_Output sps_Composition_connector.def_Composition_connector sps_Composition_part.def_Composition_part bundle_Composition.def_Composition_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_map ::
    "(bool event stream \<times> bool event stream) \<Rightarrow>
    ((bool event stream) \<times> (bool event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_part_o_pattern, channel_part_i_pattern) .
    ((channel_part_o_pattern), (channel_part_i_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_part_o_pattern, channel_part_i_pattern)
  = ((channel_part_o_pattern), (channel_part_i_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_Composition_connector_Composition_connector_Input.buildSB"
               "def_Composition_part_Input.buildSB"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawinput_map_def)+



definition rawoutput_map ::
  "(bool event stream \<times> bool event stream \<times> bool event stream) \<Rightarrow>
  ((bool event stream \<times> bool event stream) \<times> (bool event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_o_pattern, channel_part_i_pattern, channel_part_o_pattern) .
  ((channel_o_pattern, channel_part_i_pattern), (channel_part_o_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_o_pattern, channel_part_i_pattern, channel_part_o_pattern)
  = ((channel_o_pattern, channel_part_i_pattern), (channel_part_o_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_Composition_connector_Composition_connector_Output.buildSB"
               "def_Composition_part_Output.buildSB"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    by(simp add: min.commute min.left_commute image_iff surj_def id_def len_unit_def len_prod_def
                 rawoutput_map_def)+





abbreviation "def_Composition_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_Composition_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_Composition_connector_Composition_connector_Input.buildSB" "def_Composition_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_Composition_connector_Composition_connector_Output.buildSB" "def_Composition_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_Composition_rawinput2part \<equiv> (snd o rawinput_map)"

abbreviation "def_Composition_rawoutput2part \<equiv> (snd o rawoutput_map)"

interpretation part_input_Sub:
    subsetGen "RawInput.constructor" "def_Composition_part_Input.buildSB" "def_Composition_rawinput2part"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation part_output_Sub:
    subsetGen "RawOutput.constructor" "def_Composition_part_Output.buildSB" "def_Composition_rawoutput2part"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_composition ::
    "(bool event stream \<times> bool event stream)
  \<Rightarrow> unit" where
"rawinput2def_composition
    (channel_part_o_pattern, channel_part_i_pattern)
  = ()"

interpretation def_Composition_input_Sub:
    subsetGen "RawInput.constructor"
              "def_composition_input_buildSB"
              "rawinput2def_composition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add:
               def_Composition_connector_Composition_connector_Input.buildSB_def
               def_Composition_part_Input.buildSB_def)+

fun rawoutput2def_composition ::
    "(bool event stream \<times> bool event stream \<times> bool event stream)
  \<Rightarrow> (bool event stream)" where
"rawoutput2def_composition
    (channel_o_pattern, channel_part_i_pattern, channel_part_o_pattern)
  = (channel_o_pattern)"

interpretation def_Composition_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_Composition_Output.buildSB"
              "rawoutput2def_composition"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_Composition_Output.buildSB_def
               def_Composition_connector_Composition_connector_Output.buildSB_def
               def_Composition_part_Output.buildSB_def)+


fun rawinput2def_composition_feedback ::
    "(bool event stream \<times> bool event stream)
  \<Rightarrow> (bool event stream \<times> bool event stream)" where
"rawinput2def_composition_feedback
    (channel_part_o_pattern, channel_part_i_pattern)
  = (channel_part_i_pattern, channel_part_o_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_Composition_Feedback.buildSB"
              "rawinput2def_composition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_Composition_Feedback.buildSB_def
               def_Composition_connector_Composition_connector_Input.buildSB_def
               def_Composition_part_Input.buildSB_def)+

fun rawoutput2def_composition_feedback ::
    "(bool event stream \<times> bool event stream \<times> bool event stream)
  \<Rightarrow> (bool event stream \<times> bool event stream)" where
"rawoutput2def_composition_feedback
    (channel_o_pattern, channel_part_i_pattern, channel_part_o_pattern)
  = (channel_part_i_pattern, channel_part_o_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_Composition_Feedback.buildSB"
              "rawoutput2def_composition_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_Composition_Feedback.buildSB_def
               def_Composition_connector_Composition_connector_Output.buildSB_def
               def_Composition_part_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_Composition_connector_Composition_connector_Input.channels \<union> def_Composition_part_Input.channels) - def_Composition_connector_Composition_connector_Output.channels \<union> def_Composition_part_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_Composition_connector_Composition_connector_Output.channels \<union> def_Composition_part_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_Composition_connector.Sps () \<Otimes> def_Composition_part.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_Composition_Input.channels) = chDom TYPE(((def_Composition_connector_Composition_connector_Input.channels \<union> def_Composition_part_Input.channels) - def_Composition_connector_Composition_connector_Output.channels \<union> def_Composition_part_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_Composition_Output.channels) \<subseteq> chDom TYPE((def_Composition_connector_Composition_connector_Output.channels \<union> def_Composition_part_Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma connector_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma connector_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma part_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma part_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma part_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_PartDefinition.Sps () \<Longrightarrow> P (def_PartDefinition_Input.SB.getter\<cdot>sb) (def_PartDefinition_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_Composition_part_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_Composition_part_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst part_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst part_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_Composition_part.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_Composition_connector.connector\<cdot>(def_Composition_connector_Composition_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_Composition_connector_Composition_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_Composition_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_Composition_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_Composition_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_Composition_Input.channels\<^sup>\<Omega> \<rightarrow> def_Composition_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
