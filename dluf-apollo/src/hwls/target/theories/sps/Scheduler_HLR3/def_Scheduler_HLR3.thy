theory def_Scheduler_HLR3
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_Scheduler_HLR2.def_Scheduler_HLR2_Input bundle_Scheduler_HLR2.def_Scheduler_HLR2_Output sps_Scheduler_HLR3_connector.def_Scheduler_HLR3_connector sps_Scheduler_HLR3_buffer.def_Scheduler_HLR3_buffer sps_Scheduler_HLR3_capacity.def_Scheduler_HLR3_capacity bundle_Scheduler_HLR3.def_Scheduler_HLR3_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((CtrlEnum event stream \<times> Packet event stream) \<times> (Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern) .
    ((channel_buffer_control_data_pattern, channel_buffer_input_data_pattern), (channel_capacity_input_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern)
  = ((channel_buffer_control_data_pattern, channel_buffer_input_data_pattern), (channel_capacity_input_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_Scheduler_HLR3_buffer_Input.buildSB"
               "def_Scheduler_HLR3_capacity_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream) \<times> (CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern, channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern) .
    ((channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern), (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern, channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern)
  = ((channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern), (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (CtrlEnum event stream \<times> Packet event stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern) .
  ((channel_buffer_output_data_pattern), (channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)
  = ((channel_buffer_output_data_pattern), (channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_Scheduler_HLR3_buffer_Output.buildSB"
               "def_Scheduler_HLR3_capacity_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream) \<Rightarrow>
  ((CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern) .
  ((channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern), (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)
  = ((channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern), (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_Scheduler_HLR3_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_Scheduler_HLR3_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.buildSB" "def_Scheduler_HLR3_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.buildSB" "def_Scheduler_HLR3_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_Scheduler_HLR3_rawinput2buffer \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "def_Scheduler_HLR3_rawoutput2buffer \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation buffer_input_Sub:
    subsetGen "RawInput.constructor" "def_Scheduler_HLR3_buffer_Input.buildSB" "def_Scheduler_HLR3_rawinput2buffer"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation buffer_output_Sub:
    subsetGen "RawOutput.constructor" "def_Scheduler_HLR3_buffer_Output.buildSB" "def_Scheduler_HLR3_rawoutput2buffer"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_Scheduler_HLR3_rawinput2capacity \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "def_Scheduler_HLR3_rawoutput2capacity \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation capacity_input_Sub:
    subsetGen "RawInput.constructor" "def_Scheduler_HLR3_capacity_Input.buildSB" "def_Scheduler_HLR3_rawinput2capacity"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation capacity_output_Sub:
    subsetGen "RawOutput.constructor" "def_Scheduler_HLR3_capacity_Output.buildSB" "def_Scheduler_HLR3_rawoutput2capacity"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_scheduler_hlr3 ::
    "(Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream)" where
"rawinput2def_scheduler_hlr3
    (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern, channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern)
  = (channel_input_data_pattern)"

interpretation def_Scheduler_HLR3_input_Sub:
    subsetGen "RawInput.constructor"
              "def_Scheduler_HLR2_Input.buildSB"
              "rawinput2def_scheduler_hlr3"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_Scheduler_HLR2_Input.buildSB_def
               def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.buildSB_def
               def_Scheduler_HLR3_buffer_Input.buildSB_def
               def_Scheduler_HLR3_capacity_Input.buildSB_def)+

fun rawoutput2def_scheduler_hlr3 ::
    "(CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream)" where
"rawoutput2def_scheduler_hlr3
    (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)
  = (channel_output_data_pattern)"

interpretation def_Scheduler_HLR3_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_Scheduler_HLR2_Output.buildSB"
              "rawoutput2def_scheduler_hlr3"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_Scheduler_HLR2_Output.buildSB_def
               def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.buildSB_def
               def_Scheduler_HLR3_buffer_Output.buildSB_def
               def_Scheduler_HLR3_capacity_Output.buildSB_def)+


fun rawinput2def_scheduler_hlr3_feedback ::
    "(Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream)" where
"rawinput2def_scheduler_hlr3_feedback
    (channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern, channel_input_data_pattern, channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern)
  = (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_Scheduler_HLR3_Feedback.buildSB"
              "rawinput2def_scheduler_hlr3_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_Scheduler_HLR3_Feedback.buildSB_def
               def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.buildSB_def
               def_Scheduler_HLR3_buffer_Input.buildSB_def
               def_Scheduler_HLR3_capacity_Input.buildSB_def)+

fun rawoutput2def_scheduler_hlr3_feedback ::
    "(CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream)
  \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream)" where
"rawoutput2def_scheduler_hlr3_feedback
    (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_output_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)
  = (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern, channel_capacity_input_data_pattern, channel_buffer_output_data_pattern, channel_capacity_control_data_pattern, channel_capacity_output_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_Scheduler_HLR3_Feedback.buildSB"
              "rawoutput2def_scheduler_hlr3_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_Scheduler_HLR3_Feedback.buildSB_def
               def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.buildSB_def
               def_Scheduler_HLR3_buffer_Output.buildSB_def
               def_Scheduler_HLR3_capacity_Output.buildSB_def)+




definition rawSps :: "(nat) \<Rightarrow> (((def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channels \<union> (def_Scheduler_HLR3_buffer_Input.channels \<union> def_Scheduler_HLR3_capacity_Input.channels) - def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels) - def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels \<union> def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels \<union> def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (var_capacity). def_Scheduler_HLR3_connector.Sps () \<Otimes> def_Scheduler_HLR3_buffer.Sps (var_capacity) \<Otimes> def_Scheduler_HLR3_capacity.Sps (var_capacity)"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_Scheduler_HLR2_Input.channels) = chDom TYPE(((def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channels \<union> (def_Scheduler_HLR3_buffer_Input.channels \<union> def_Scheduler_HLR3_capacity_Input.channels) - def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels) - def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels \<union> def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_Scheduler_HLR2_Output.channels) \<subseteq> chDom TYPE((def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels \<union> def_Scheduler_HLR3_buffer_Output.channels \<union> def_Scheduler_HLR3_capacity_Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma connector_input_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma connector_output_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma buffer_input_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma buffer_output_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma capacity_input_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma capacity_output_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma buffer_pred_general:
  assumes "spf \<in> (rawSps (var_capacity))"
      and "\<And>sb spf. spf \<in> def_Buffer_HLR3.Sps () \<Longrightarrow> P (def_Buffer_HLR3_Input.SB.getter\<cdot>sb) (def_Buffer_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_Scheduler_HLR3_buffer_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_Scheduler_HLR3_buffer_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst buffer_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst buffer_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_Scheduler_HLR3_buffer.pred_inst2def assms: assms)
 

lemma capacity_pred_general:
  assumes "spf \<in> (rawSps (var_capacity))"
      and "\<And>sb spf. spf \<in> def_Capacity_HLR3.Sps (var_capacity) \<Longrightarrow> P (def_Capacity_HLR3_Input.SB.getter\<cdot>sb) (def_Capacity_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_Scheduler_HLR3_capacity_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_Scheduler_HLR3_capacity_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst capacity_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst capacity_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_Scheduler_HLR3_capacity.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "def_Scheduler_HLR3_connector.connector\<cdot>(def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_Scheduler_HLR3_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps (var_capacity))"
    shows "(def_Scheduler_HLR3_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_Scheduler_HLR3_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "(nat) \<Rightarrow> (def_Scheduler_HLR2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_capacity). spsConvert \<cdot> (rawSps (var_capacity)) "

declare len_prod_inf_snd[simp]


end
