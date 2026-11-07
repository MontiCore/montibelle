theory SecurityGate_HWL
  imports stream.StreamCodegen sps_SecurityGate_LLR.def_SecurityGate_LLR
begin

lemma statecontents: "\<And>s. s = StateConstr x1 \<Longrightarrow> x1\<in>{state__Alarm_Eve_detected, state__Bob_Alice, state__Bob, state__Alice,state__Bob_Alice_Eve}"
  using Substate.exhaust by blast

lemma no_tick_transitions: "fst ` behavior.transition () s Tick = {s}"
  apply (simp add: behavior.trans_states)
  apply (simp add: behavior.ndaTransition_tickC_def)
  apply (cases s)
  apply (auto)
  using Substate.exhaust by blast

lemma aut_total: "fst ` behavior.transition () s m \<noteq> {}"
  apply (simp add: behavior.trans_states)
  apply (cases m)
  apply (auto)
  apply (metis empty_not_UNIV eventGen.ndaTransition_tickC_def)
  apply (simp add: behavior.ndaTransition_eventC_def)
  by (metis empty_not_UNIV)

lemma adm_member_eValues:
  assumes "adm P"
  shows "adm (\<lambda>x. m \<in> eValues\<cdot>(e2ustream\<cdot>x) \<longrightarrow> P x)"
proof -
  have "adm (\<lambda>s. m \<notin> eValues\<cdot>(e2ustream\<cdot>s))"
    by (metis (no_types, lifting) ext adm_cmp adm_not_in)
  then show ?thesis
    by (simp add: assms)
qed

lemma reachability_induction:
  assumes "{channel_SecurityGate_LLR_input_dataConstr Alice_plus_Eve_request_Camera_accepts,
    channel_SecurityGate_LLR_input_dataConstr Bob_plus_Eve_request_Camera_accepts} \<inter> eValues\<cdot>input = {}"
  and "(StateConstr state__Bob_Alice_Eve) \<notin> init"
  shows "(StateConstr state__Bob_Alice_Eve) \<notin>
         sreachable_nda_all (\<lambda>s m. fst ` behavior.transition () s m)\<cdot>init\<cdot>input"
  using assms
  proof(induction input arbitrary: init)
  case adm
  then show ?case
   apply (rule adm_imp)
    apply (simp add: adm_in2 adm_cmp)
    apply (auto)
    done
  next
  case bottom
  then show ?case
    by simp
next
  case (step a input)
  thm step.IH
  show ?case
  proof (cases a)
    case Tick
    then have tick_eq: "a = Tick"
      by simp
    then show ?thesis
      apply (subst sreachable_nda_all_unfold)
      apply (simp add: no_tick_transitions)
      apply auto
      apply (simp add: step.prems)
      using step.IH step.prems(1,2) tick_eq by fastforce
  next
    case (EventMsg msg)
    then have msg_eq: "a = EventMsg (msg::def_SecurityGate_LLR_Input.channels msgWithChan)" by simp

    obtain channel message where 
      msg_decompose: "Rep_msgWithChan msg = (channel, message)"
      by (cases "Rep_msgWithChan msg")

    have channel_is_input: "channel = channel_input_data"
      apply (subst def_SecurityGate_LLR_Input.channels.nchotomy)
      apply simp
      done

    have msg_rep: "Rep_msgWithChan msg = (channel_input_data, message)"
      by (simp add: msg_decompose channel_is_input)

    obtain action where
      message_is_action: "message = ActionEnumEVENTConstr action"
      by (cases message; simp)

    have full_decompose: "Rep_msgWithChan msg = (channel_input_data, ActionEnumEVENTConstr action)"
      by (simp add: msg_rep message_is_action)

    have not_accept_action: 
      "action \<notin> {Alice_plus_Eve_request_Camera_accepts, Bob_plus_Eve_request_Camera_accepts}"
    proof
      assume "action \<in> {Alice_plus_Eve_request_Camera_accepts, Bob_plus_Eve_request_Camera_accepts}"
      then have "msg \<in> {channel_SecurityGate_LLR_input_dataConstr Alice_plus_Eve_request_Camera_accepts,
                        channel_SecurityGate_LLR_input_dataConstr Bob_plus_Eve_request_Camera_accepts}"
        apply (auto simp add: channel_SecurityGate_LLR_input_dataConstr.rep_eq full_decompose)
        apply (metis Rep_msgWithChan_inverse channel_SecurityGate_LLR_input_dataConstr.abs_eq full_decompose)
        by (metis Rep_msgWithChan_inverse channel_SecurityGate_LLR_input_dataConstr.abs_eq full_decompose)
      with step.prems(1) msg_eq show False
        by (auto simp add: eValues_def)
    qed

  have init_decompose: 
    "\<And>f. (\<Union>x\<in>init. fst `( f () x action)) = (\<Union>(substates)\<in>{(s). StateConstr s \<in> init}. fst ` (f () (StateConstr substates) action))"
        apply auto
        by (metis State.exhaust fst_conv image_iff)

    have noAlice:  "action  \<noteq>  Alice_plus_Eve_request_Camera_accepts"
      using not_accept_action by auto

    have noBob:  "action  \<noteq>  Bob_plus_Eve_request_Camera_accepts"
      using not_accept_action by auto

  have simplify_if_for_steBob:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alice then expression_09 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set1 where
      isset1: "set1 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alice then expression_09 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_plus_Eve_request_Camera_denies else {})))"
        by simp

      have fs1: " StateConstr state__Bob_Alice_Eve  \<notin> set1 "
        apply (subst isset1)
        by (simp add: step.prems(2))

  have simplify_if_for_steAlice:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob then expression_05 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set2 where
      isset2: "set2 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob then expression_05 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_plus_Eve_request_Camera_denies else {})))"
        by simp

      have fs2: " StateConstr state__Bob_Alice_Eve  \<notin> set2"
        apply (subst isset2)
        by (simp add: step.prems(2))

  have simplify_if_for_step3:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Alice then expression_08 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set3 where
      isset3: "set3 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Alice then expression_08 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_without_Eve_request_Camera_accepts else {})))"
        by simp

      have fs3: " StateConstr state__Bob_Alice_Eve  \<notin> set3"
        apply (subst isset3)
        by (simp add: step.prems(2))

  have simplify_if_for_step4:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Bob then expression_04 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set4 where
      isset4: "set4 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Bob then expression_04 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_without_Eve_request_Camera_accepts else {})))"
        by simp

      have fs4: " StateConstr state__Bob_Alice_Eve  \<notin> set4"
        apply (subst isset4)
        by (simp add: step.prems(2))

  have simplify_if_for_step5:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set5 where
      isset5: "set5 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_without_Eve_request_Camera_denies else {})))"
        by simp

      have fs5: " StateConstr state__Bob_Alice_Eve  \<notin> set5"
        apply (subst isset5)
        by (simp add: step.prems(2))

  have simplify_if_for_step6:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set6 where
      isset6: "set6 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_02 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_without_Eve_request_Camera_denies else {})))"
        by simp

      have fs6: " StateConstr state__Bob_Alice_Eve  \<notin> set6"
        apply (subst isset6)
        by (simp add: step.prems(2))

  have simplify_if_for_step7:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_00 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      obtain set7 where
      isset7: "set7 = (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_00 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Bob_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Bob_wants_to_exit_cockpit else {})))"
        by simp

      have fs7: " StateConstr state__Bob_Alice_Eve  \<notin> set7"
        apply (subst isset7)
        by (simp add: step.prems(2))

  have simplify_if_for_step8:
        "\<And>x. fst `
           (if (if x = state__Bob_Alice then expression_01 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Bob then expression_06 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Alice then expression_010 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) = {} \<and>
               (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) = {}
            then UNIV else eventTransition () (StateConstr x) (Rep_msgWithChan msg)) =
               fst ` eventTransition () (StateConstr x) (Rep_msgWithChan msg)"
        apply (case_tac x)
    by simp_all

      have fs8: " StateConstr state__Bob_Alice_Eve  \<notin> (\<Union>x\<in>{s. StateConstr s \<in> init}.
           fst `
           ((if x = state__Bob_Alice then expression_01 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Bob then expression_06 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Alice then expression_010 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Bob_Alice_Eve then expression_011 () (StateConstr x) Alice_wants_to_exit_cockpit else {}) \<union>
            (if x = state__Alarm_Eve_detected then expression_012 () (StateConstr x) Alice_wants_to_exit_cockpit else {})))"
        by (simp add: step.prems(2))


     show ?thesis
      apply (simp only: sreachable_nda_all_unfold no_tick_transitions step.prems)
      apply (simp add: step.prems msg_eq)
      apply (subst(2) behavior.trans_states)
      apply (simp add: behavior.ndaTransition_eventC_def aut_total)
      apply (subst init_decompose)
      apply (subst full_decompose)
      apply (cases action)
      apply (simp_all add: noBob noAlice simplify_if_for_steBob simplify_if_for_steAlice 
             simplify_if_for_step3 simplify_if_for_step4 simplify_if_for_step5 simplify_if_for_step6 
             simplify_if_for_step7 simplify_if_for_step8 full_decompose isset1[symmetric] 
             isset2[symmetric] isset3[symmetric] isset4[symmetric] isset5[symmetric]
             isset6[symmetric] isset7[symmetric]) 
          using fs1 fs2 fs3 fs4 fs5 fs6 fs7 fs8 msg_eq step.IH step.prems(1) apply fastforce+
          done
  qed
qed

end