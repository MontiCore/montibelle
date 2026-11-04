theory ref_DLUF_HLR2_rough_DLUF_HLR1
  imports
    (* Gen  *) sps_DLUF_HLR1.def_DLUF_HLR1 sps_DLUF_HLR2.def_DLUF_HLR2
               sps_DLUF_HLR2_scheduler1.def_DLUF_HLR2_scheduler1 sps_DLUF_HLR2_scheduler2.def_DLUF_HLR2_scheduler2 sps_DLUF_HLR2_scheduler3.def_DLUF_HLR2_scheduler3 sps_DLUF_HLR2_scheduler4.def_DLUF_HLR2_scheduler4 
    (* Hwl  *)

begin




lemma pred_0:
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap1)  (def_DLUF_HLR2_scheduler1_InputMap.connector\<cdot>(channel_scheduler1_input_data_pattern)) (def_DLUF_HLR2_scheduler1_OutputMap.connector\<cdot>(channel_scheduler1_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap2)  (def_DLUF_HLR2_scheduler2_InputMap.connector\<cdot>(channel_scheduler2_input_data_pattern)) (def_DLUF_HLR2_scheduler2_OutputMap.connector\<cdot>(channel_scheduler2_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap3)  (def_DLUF_HLR2_scheduler3_InputMap.connector\<cdot>(channel_scheduler3_input_data_pattern)) (def_DLUF_HLR2_scheduler3_OutputMap.connector\<cdot>(channel_scheduler3_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap4)  (def_DLUF_HLR2_scheduler4_InputMap.connector\<cdot>(channel_scheduler4_input_data_pattern)) (def_DLUF_HLR2_scheduler4_OutputMap.connector\<cdot>(channel_scheduler4_output_data_pattern))"
      and "wellformed (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern)"
      and "def_DLUF_HLR1.assumption_0 (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
      and "def_DLUF_HLR1.assumption_1 (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
      and "def_DLUF_HLR1.assumption_2 (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
      and "channel_scheduler1_input_data_pattern = channel_input1_data_pattern"
      and "channel_scheduler2_input_data_pattern = channel_input2_data_pattern"
      and "channel_scheduler3_input_data_pattern = channel_input3_data_pattern"
      and "channel_scheduler4_input_data_pattern = channel_input4_data_pattern"
      and "channel_output1_data_pattern = channel_scheduler1_output_data_pattern"
      and "channel_output2_data_pattern = channel_scheduler2_output_data_pattern"
      and "channel_output3_data_pattern = channel_scheduler3_output_data_pattern"
      and "channel_output4_data_pattern = channel_scheduler4_output_data_pattern"
    shows "def_DLUF_HLR1.predicate_0 (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  apply(insert assms(1-8), simp add: assms(9-16))
  apply(simp add: def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.wholePredicate_def def_DLUF_HLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_DLUF_HLR2_scheduler1_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler1_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler2_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler2_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler3_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler3_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler4_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler4_OutputMap.connector.rep_eq)?
  apply(simp add: def_DLUF_HLR1.assumption_0_def def_DLUF_HLR1.assumption_1_def def_DLUF_HLR1.assumption_2_def def_DLUF_HLR1.predicate_0_def def_DLUF_HLR1.causality_def)?
  apply(simp add: def_Scheduler_HLR2.assumption_0_def def_Scheduler_HLR2.assumption_1_def def_Scheduler_HLR2.assumption_2_def def_Scheduler_HLR2.predicate_0_def def_Scheduler_HLR2.causality_def)?
  apply(simp add: def_Scheduler_HLR2.assumption_0_def def_Scheduler_HLR2.assumption_1_def def_Scheduler_HLR2.assumption_2_def def_Scheduler_HLR2.predicate_0_def def_Scheduler_HLR2.causality_def)?
  apply(simp add: def_Scheduler_HLR2.assumption_0_def def_Scheduler_HLR2.assumption_1_def def_Scheduler_HLR2.assumption_2_def def_Scheduler_HLR2.predicate_0_def def_Scheduler_HLR2.causality_def)?
  apply(simp add: def_Scheduler_HLR2.assumption_0_def def_Scheduler_HLR2.assumption_1_def def_Scheduler_HLR2.assumption_2_def def_Scheduler_HLR2.predicate_0_def def_Scheduler_HLR2.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(simp add: len_stream_def[symmetric])?
  (* autosledgi *) sorry

lemma causality:
  assumes "def_Scheduler_HLR2.causality  (def_DLUF_HLR2_scheduler1_InputMap.connector\<cdot>(channel_scheduler1_input_data_pattern)) (def_DLUF_HLR2_scheduler1_OutputMap.connector\<cdot>(channel_scheduler1_output_data_pattern))"
  assumes "def_Scheduler_HLR2.causality  (def_DLUF_HLR2_scheduler2_InputMap.connector\<cdot>(channel_scheduler2_input_data_pattern)) (def_DLUF_HLR2_scheduler2_OutputMap.connector\<cdot>(channel_scheduler2_output_data_pattern))"
  assumes "def_Scheduler_HLR2.causality  (def_DLUF_HLR2_scheduler3_InputMap.connector\<cdot>(channel_scheduler3_input_data_pattern)) (def_DLUF_HLR2_scheduler3_OutputMap.connector\<cdot>(channel_scheduler3_output_data_pattern))"
  assumes "def_Scheduler_HLR2.causality  (def_DLUF_HLR2_scheduler4_InputMap.connector\<cdot>(channel_scheduler4_input_data_pattern)) (def_DLUF_HLR2_scheduler4_OutputMap.connector\<cdot>(channel_scheduler4_output_data_pattern))"
      and "channel_scheduler1_input_data_pattern = channel_input1_data_pattern"
      and "channel_scheduler2_input_data_pattern = channel_input2_data_pattern"
      and "channel_scheduler3_input_data_pattern = channel_input3_data_pattern"
      and "channel_scheduler4_input_data_pattern = channel_input4_data_pattern"
      and "channel_output1_data_pattern = channel_scheduler1_output_data_pattern"
      and "channel_output2_data_pattern = channel_scheduler2_output_data_pattern"
      and "channel_output3_data_pattern = channel_scheduler3_output_data_pattern"
      and "channel_output4_data_pattern = channel_scheduler4_output_data_pattern"
    shows "def_DLUF_HLR1.causality (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  apply(insert assms)
  apply(simp add: def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def
                  def_DLUF_HLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_DLUF_HLR2_scheduler1_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler1_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler2_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler2_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler3_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler3_OutputMap.connector.rep_eq def_DLUF_HLR2_scheduler4_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler4_OutputMap.connector.rep_eq)?
  apply(simp add: def_DLUF_HLR1.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  (* autosledgi *) sorry

lemma pred_whole:
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap1) (def_DLUF_HLR2_scheduler1_InputMap.connector\<cdot>(channel_scheduler1_input_data_pattern))  (def_DLUF_HLR2_scheduler1_OutputMap.connector\<cdot>(channel_scheduler1_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap2) (def_DLUF_HLR2_scheduler2_InputMap.connector\<cdot>(channel_scheduler2_input_data_pattern))  (def_DLUF_HLR2_scheduler2_OutputMap.connector\<cdot>(channel_scheduler2_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap3) (def_DLUF_HLR2_scheduler3_InputMap.connector\<cdot>(channel_scheduler3_input_data_pattern))  (def_DLUF_HLR2_scheduler3_OutputMap.connector\<cdot>(channel_scheduler3_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap4) (def_DLUF_HLR2_scheduler4_InputMap.connector\<cdot>(channel_scheduler4_input_data_pattern))  (def_DLUF_HLR2_scheduler4_OutputMap.connector\<cdot>(channel_scheduler4_output_data_pattern))"
      and "channel_scheduler1_input_data_pattern = channel_input1_data_pattern"
      and "channel_scheduler2_input_data_pattern = channel_input2_data_pattern"
      and "channel_scheduler3_input_data_pattern = channel_input3_data_pattern"
      and "channel_scheduler4_input_data_pattern = channel_input4_data_pattern"
      and "channel_output1_data_pattern = channel_scheduler1_output_data_pattern"
      and "channel_output2_data_pattern = channel_scheduler2_output_data_pattern"
      and "channel_output3_data_pattern = channel_scheduler3_output_data_pattern"
      and "channel_output4_data_pattern = channel_scheduler4_output_data_pattern"
    shows "def_DLUF_HLR1.wholePredicate (var_cap1, var_cap2, var_cap3, var_cap4) (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  apply(simp add: def_DLUF_HLR1.wholePredicate_def)
  using assms causality
    def_Scheduler_HLR2.wholePredicate_def
    def_Scheduler_HLR2.wholePredicate_def
    def_Scheduler_HLR2.wholePredicate_def
    def_Scheduler_HLR2.wholePredicate_def
  pred_0 by auto

lemma pred_whole2:
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap1) (def_DLUF_HLR2_scheduler1_InputMap.connector\<cdot>(def_DLUF_HLR2_rawinput2scheduler1 input))(def_DLUF_HLR2_scheduler1_OutputMap.connector\<cdot>(def_DLUF_HLR2_rawoutput2scheduler1 output))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap2) (def_DLUF_HLR2_scheduler2_InputMap.connector\<cdot>(def_DLUF_HLR2_rawinput2scheduler2 input))(def_DLUF_HLR2_scheduler2_OutputMap.connector\<cdot>(def_DLUF_HLR2_rawoutput2scheduler2 output))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap3) (def_DLUF_HLR2_scheduler3_InputMap.connector\<cdot>(def_DLUF_HLR2_rawinput2scheduler3 input))(def_DLUF_HLR2_scheduler3_OutputMap.connector\<cdot>(def_DLUF_HLR2_rawoutput2scheduler3 output))"
  assumes "def_Scheduler_HLR2.wholePredicate (var_cap4) (def_DLUF_HLR2_scheduler4_InputMap.connector\<cdot>(def_DLUF_HLR2_rawinput2scheduler4 input))(def_DLUF_HLR2_scheduler4_OutputMap.connector\<cdot>(def_DLUF_HLR2_rawoutput2scheduler4 output))"
  assumes "def_DLUF_HLR2_connector.connector\<cdot>(def_DLUF_HLR2_rawinput2connector input) = def_DLUF_HLR2_rawoutput2connector output"
  assumes "rawinput2def_dluf_hlr2_feedback input = rawoutput2def_dluf_hlr2_feedback output"
    shows "def_DLUF_HLR1.wholePredicate (var_cap1, var_cap2, var_cap3, var_cap4) (rawinput2def_dluf_hlr2 input) (rawoutput2def_dluf_hlr2 output)"
  apply(rule rawinput2def_dluf_hlr2.cases[of "input"],
        rule rawoutput2def_dluf_hlr2.cases[of "output"], simp)
  apply(rule pred_whole)
  using assms apply (auto simp add: def_DLUF_HLR2_connector.connector.rep_eq)
  done

lemma raw_input_eq:
  assumes "spf\<in>(def_DLUF_HLR2.rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "((sb)\<star>::def_DLUF_HLR1_Input.channels\<^sup>\<Omega>)
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.channels
                           \<union>def_DLUF_HLR2_scheduler1_Input.channels
                           \<union>def_DLUF_HLR2_scheduler2_Input.channels
                           \<union>def_DLUF_HLR2_scheduler3_Input.channels
                           \<union>def_DLUF_HLR2_scheduler4_Input.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_pred_whole:
  assumes "spf\<in>(def_DLUF_HLR2.rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "def_DLUF_HLR1.wholePredicate (var_cap1, var_cap2, var_cap3, var_cap4)
             (def_DLUF_HLR1_Input.SB.getter\<cdot>(sb\<star>))
             (def_DLUF_HLR1_Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>))"
  apply(subst raw_input_eq[OF assms(1)])
  apply(simp add: def_DLUF_HLR1_Input.sbgetter_def def_DLUF_HLR1_Output.sbgetter_def
                  def_DLUF_HLR2_input_Sub.getter_sub_eq def_DLUF_HLR2_output_Sub.getter_sub_eq)
  apply(rule pred_whole2)
  apply(simp only: scheduler1_input_Sub.getter_sub_eq[symmetric] scheduler1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_DLUF_HLR2_scheduler1_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler1_OutputMap.connector.rep_eq)
  apply(subst def_DLUF_HLR2_scheduler1_Input.getter_fold,
        subst def_DLUF_HLR2_scheduler1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule scheduler1_pred_general[OF assms(1)])
  apply(simp add: def_Scheduler_HLR2.Sps_def)
  apply(simp only: scheduler2_input_Sub.getter_sub_eq[symmetric] scheduler2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_DLUF_HLR2_scheduler2_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler2_OutputMap.connector.rep_eq)
  apply(subst def_DLUF_HLR2_scheduler2_Input.getter_fold,
        subst def_DLUF_HLR2_scheduler2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule scheduler2_pred_general[OF assms(1)])
  apply(simp add: def_Scheduler_HLR2.Sps_def)
  apply(simp only: scheduler3_input_Sub.getter_sub_eq[symmetric] scheduler3_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_DLUF_HLR2_scheduler3_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler3_OutputMap.connector.rep_eq)
  apply(subst def_DLUF_HLR2_scheduler3_Input.getter_fold,
        subst def_DLUF_HLR2_scheduler3_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule scheduler3_pred_general[OF assms(1)])
  apply(simp add: def_Scheduler_HLR2.Sps_def)
  apply(simp only: scheduler4_input_Sub.getter_sub_eq[symmetric] scheduler4_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_DLUF_HLR2_scheduler4_InputMap.connector.rep_eq def_DLUF_HLR2_scheduler4_OutputMap.connector.rep_eq)
  apply(subst def_DLUF_HLR2_scheduler4_Input.getter_fold,
        subst def_DLUF_HLR2_scheduler4_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule scheduler4_pred_general[OF assms(1)])
  apply(simp add: def_Scheduler_HLR2.Sps_def)
  apply(simp only: connector_input_Sub.getter_sub_eq[symmetric]
                   connector_output_Sub.getter_sub_eq[symmetric])
  apply(subst def_DLUF_HLR2_connector_DLUF_HLR2_connector_Input.getter_fold,
        subst def_DLUF_HLR2_connector_DLUF_HLR2_connector_Output.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst def_DLUF_HLR2_Feedback.getter_fold,
        subst def_DLUF_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

lemma comp_pred_whole:
  assumes "spf\<in>(def_DLUF_HLR2.Sps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "def_DLUF_HLR1.wholePredicate (var_cap1, var_cap2, var_cap3, var_cap4)
             (def_DLUF_HLR1_Input.SB.getter\<cdot>sb)
             (def_DLUF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(rule spsconvert_predicate)
  using assms apply(simp add: def_DLUF_HLR2.Sps_def)
  using raw_pred_whole apply blast
  by auto

lemma refinement[simp]: "def_DLUF_HLR2.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLUF_HLR1.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
  by(simp add: subsetI def_DLUF_HLR1.Sps_def comp_pred_whole)


end
