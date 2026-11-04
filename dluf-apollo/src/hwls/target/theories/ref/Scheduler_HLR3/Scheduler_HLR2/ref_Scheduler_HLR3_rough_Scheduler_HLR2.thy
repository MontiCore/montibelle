theory ref_Scheduler_HLR3_rough_Scheduler_HLR2
  imports
    (* Gen  *) sps_Scheduler_HLR2.def_Scheduler_HLR2 sps_Scheduler_HLR3.def_Scheduler_HLR3
               sps_Scheduler_HLR3_buffer.def_Scheduler_HLR3_buffer sps_Scheduler_HLR3_capacity.def_Scheduler_HLR3_capacity 
    (* Hwl  *)

begin




lemma pred_0:
  assumes "def_Buffer_HLR3.wholePredicate ()  (def_Scheduler_HLR3_buffer_InputMap.connector\<cdot>(channel_buffer_control_data_pattern, channel_buffer_input_data_pattern)) (def_Scheduler_HLR3_buffer_OutputMap.connector\<cdot>(channel_buffer_output_data_pattern))"
  assumes "def_Capacity_HLR3.wholePredicate (var_capacity)  (def_Scheduler_HLR3_capacity_InputMap.connector\<cdot>(channel_capacity_input_data_pattern)) (def_Scheduler_HLR3_capacity_OutputMap.connector\<cdot>(channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"
      and "wellformed (channel_input_data_pattern)"
      and "def_Scheduler_HLR2.assumption_0 (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern)"
      and "def_Scheduler_HLR2.assumption_1 (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern)"
      and "def_Scheduler_HLR2.assumption_2 (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern)"
      and "channel_buffer_input_data_pattern = channel_input_data_pattern"
      and "channel_capacity_input_data_pattern = channel_buffer_output_data_pattern"
      and "channel_buffer_control_data_pattern = channel_capacity_control_data_pattern"
      and "channel_output_data_pattern = channel_capacity_output_data_pattern"
    shows "def_Scheduler_HLR2.predicate_0 (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern)"
  apply(insert assms(1-6), simp add: assms(7-10))
  apply(simp add: def_Buffer_HLR3.wholePredicate_def def_Capacity_HLR3.wholePredicate_def def_Scheduler_HLR2.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_Scheduler_HLR3_buffer_InputMap.connector.rep_eq def_Scheduler_HLR3_buffer_OutputMap.connector.rep_eq def_Scheduler_HLR3_capacity_InputMap.connector.rep_eq def_Scheduler_HLR3_capacity_OutputMap.connector.rep_eq)?
  apply(simp add: def_Scheduler_HLR2.assumption_0_def def_Scheduler_HLR2.assumption_1_def def_Scheduler_HLR2.assumption_2_def def_Scheduler_HLR2.predicate_0_def def_Scheduler_HLR2.causality_def)?
  apply(simp add: def_Buffer_HLR3.assumption_0_def def_Buffer_HLR3.assumption_1_def def_Buffer_HLR3.predicate_0_def def_Buffer_HLR3.predicate_1_def def_Buffer_HLR3.causality_def)?
  apply(simp add: def_Capacity_HLR3.assumption_0_def def_Capacity_HLR3.assumption_1_def def_Capacity_HLR3.assumption_2_def def_Capacity_HLR3.predicate_0_def def_Capacity_HLR3.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(simp add: len_stream_def[symmetric])?
  (* autosledgi *) sorry

lemma causality:
  assumes "def_Buffer_HLR3.causality  (def_Scheduler_HLR3_buffer_InputMap.connector\<cdot>(channel_buffer_control_data_pattern, channel_buffer_input_data_pattern)) (def_Scheduler_HLR3_buffer_OutputMap.connector\<cdot>(channel_buffer_output_data_pattern))"
  assumes "def_Capacity_HLR3.causality  (def_Scheduler_HLR3_capacity_InputMap.connector\<cdot>(channel_capacity_input_data_pattern)) (def_Scheduler_HLR3_capacity_OutputMap.connector\<cdot>(channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"
      and "channel_buffer_input_data_pattern = channel_input_data_pattern"
      and "channel_capacity_input_data_pattern = channel_buffer_output_data_pattern"
      and "channel_buffer_control_data_pattern = channel_capacity_control_data_pattern"
      and "channel_output_data_pattern = channel_capacity_output_data_pattern"
    shows "def_Scheduler_HLR2.causality (channel_input_data_pattern) (channel_output_data_pattern)"
  apply(insert assms)
  apply(simp add: def_Buffer_HLR3.wholePredicate_def def_Buffer_HLR3.causality_def def_Capacity_HLR3.wholePredicate_def def_Capacity_HLR3.causality_def
                  def_Scheduler_HLR2.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_Scheduler_HLR3_buffer_InputMap.connector.rep_eq def_Scheduler_HLR3_buffer_OutputMap.connector.rep_eq def_Scheduler_HLR3_capacity_InputMap.connector.rep_eq def_Scheduler_HLR3_capacity_OutputMap.connector.rep_eq)?
  apply(simp add: def_Scheduler_HLR2.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  (* autosledgi *) sorry

lemma pred_whole:
  assumes "def_Buffer_HLR3.wholePredicate () (def_Scheduler_HLR3_buffer_InputMap.connector\<cdot>(channel_buffer_control_data_pattern, channel_buffer_input_data_pattern))  (def_Scheduler_HLR3_buffer_OutputMap.connector\<cdot>(channel_buffer_output_data_pattern))"
  assumes "def_Capacity_HLR3.wholePredicate (var_capacity) (def_Scheduler_HLR3_capacity_InputMap.connector\<cdot>(channel_capacity_input_data_pattern))  (def_Scheduler_HLR3_capacity_OutputMap.connector\<cdot>(channel_capacity_control_data_pattern, channel_capacity_output_data_pattern))"
      and "channel_buffer_input_data_pattern = channel_input_data_pattern"
      and "channel_capacity_input_data_pattern = channel_buffer_output_data_pattern"
      and "channel_buffer_control_data_pattern = channel_capacity_control_data_pattern"
      and "channel_output_data_pattern = channel_capacity_output_data_pattern"
    shows "def_Scheduler_HLR2.wholePredicate (var_capacity) (channel_input_data_pattern) (channel_output_data_pattern)"
  apply(simp add: def_Scheduler_HLR2.wholePredicate_def)
  using assms causality
    def_Buffer_HLR3.wholePredicate_def
    def_Capacity_HLR3.wholePredicate_def
  pred_0 by auto

lemma pred_whole2:
  assumes "def_Buffer_HLR3.wholePredicate () (def_Scheduler_HLR3_buffer_InputMap.connector\<cdot>(def_Scheduler_HLR3_rawinput2buffer input))(def_Scheduler_HLR3_buffer_OutputMap.connector\<cdot>(def_Scheduler_HLR3_rawoutput2buffer output))"
  assumes "def_Capacity_HLR3.wholePredicate (var_capacity) (def_Scheduler_HLR3_capacity_InputMap.connector\<cdot>(def_Scheduler_HLR3_rawinput2capacity input))(def_Scheduler_HLR3_capacity_OutputMap.connector\<cdot>(def_Scheduler_HLR3_rawoutput2capacity output))"
  assumes "def_Scheduler_HLR3_connector.connector\<cdot>(def_Scheduler_HLR3_rawinput2connector input) = def_Scheduler_HLR3_rawoutput2connector output"
  assumes "rawinput2def_scheduler_hlr3_feedback input = rawoutput2def_scheduler_hlr3_feedback output"
    shows "def_Scheduler_HLR2.wholePredicate (var_capacity) (rawinput2def_scheduler_hlr3 input) (rawoutput2def_scheduler_hlr3 output)"
  apply(rule rawinput2def_scheduler_hlr3.cases[of "input"],
        rule rawoutput2def_scheduler_hlr3.cases[of "output"], simp)
  apply(rule pred_whole)
  using assms apply (auto simp add: def_Scheduler_HLR3_connector.connector.rep_eq)
  done

lemma raw_input_eq:
  assumes "spf\<in>(def_Scheduler_HLR3.rawSps (var_capacity))"
    shows "((sb)\<star>::def_Scheduler_HLR2_Input.channels\<^sup>\<Omega>)
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channels
                           \<union>def_Scheduler_HLR3_buffer_Input.channels
                           \<union>def_Scheduler_HLR3_capacity_Input.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_pred_whole:
  assumes "spf\<in>(def_Scheduler_HLR3.rawSps (var_capacity))"
    shows "def_Scheduler_HLR2.wholePredicate (var_capacity)
             (def_Scheduler_HLR2_Input.SB.getter\<cdot>(sb\<star>))
             (def_Scheduler_HLR2_Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>))"
  apply(subst raw_input_eq[OF assms(1)])
  apply(simp add: def_Scheduler_HLR2_Input.sbgetter_def def_Scheduler_HLR2_Output.sbgetter_def
                  def_Scheduler_HLR3_input_Sub.getter_sub_eq def_Scheduler_HLR3_output_Sub.getter_sub_eq)
  apply(rule pred_whole2)
  apply(simp only: buffer_input_Sub.getter_sub_eq[symmetric] buffer_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_Scheduler_HLR3_buffer_InputMap.connector.rep_eq def_Scheduler_HLR3_buffer_OutputMap.connector.rep_eq)
  apply(subst def_Scheduler_HLR3_buffer_Input.getter_fold,
        subst def_Scheduler_HLR3_buffer_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule buffer_pred_general[OF assms(1)])
  apply(simp add: def_Buffer_HLR3.Sps_def)
  apply(simp only: capacity_input_Sub.getter_sub_eq[symmetric] capacity_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_Scheduler_HLR3_capacity_InputMap.connector.rep_eq def_Scheduler_HLR3_capacity_OutputMap.connector.rep_eq)
  apply(subst def_Scheduler_HLR3_capacity_Input.getter_fold,
        subst def_Scheduler_HLR3_capacity_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule capacity_pred_general[OF assms(1)])
  apply(simp add: def_Capacity_HLR3.Sps_def)
  apply(simp only: connector_input_Sub.getter_sub_eq[symmetric]
                   connector_output_Sub.getter_sub_eq[symmetric])
  apply(subst def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.getter_fold,
        subst def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst def_Scheduler_HLR3_Feedback.getter_fold,
        subst def_Scheduler_HLR3_Feedback.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

lemma comp_pred_whole:
  assumes "spf\<in>(def_Scheduler_HLR3.Sps (var_capacity))"
    shows "def_Scheduler_HLR2.wholePredicate (var_capacity)
             (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb)
             (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(rule spsconvert_predicate)
  using assms apply(simp add: def_Scheduler_HLR3.Sps_def)
  using raw_pred_whole apply blast
  by auto

lemma refinement[simp]: "def_Scheduler_HLR3.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
  by(simp add: subsetI def_Scheduler_HLR2.Sps_def comp_pred_whole)


end
