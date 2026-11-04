theory lo_lemma_util
  imports
    move_to_core.hwl_core_ext

    to_be_generated.hwl_tsynSBlens
begin




lemma eve1_pred_inst2def_sb:
  assumes "\<And>spf sb. spf \<in> def_Eve1_HLR.Sps () \<Longrightarrow>
        P (def_SecureProtocol_HLR2_eve1_Input.SB.setter\<cdot>(def_Eve1_HLR_Input.SB.getter\<cdot>sb))
          (def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(def_Eve1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
      and "spf \<in> def_SecureProtocol_HLR2_eve1.Sps ()"
    shows "P sb (spf\<cdot>sb)"
  apply(insert assms(2))
  apply (auto simp add: def_SecureProtocol_HLR2_eve1.Sps_def def_SecureProtocol_HLR2_eve1_InputMap.Sps_def def_SecureProtocol_HLR2_eve1_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1)
  by (metis def_SecureProtocol_HLR2_eve1_Input.SB.set_get def_Eve1_HLR_Input.SB.get_set)


lemma eve1_pred_general_sb:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
      and "\<And>spf sb. spf \<in> def_Eve1_HLR.Sps () \<Longrightarrow>
            P (def_SecureProtocol_HLR2_eve1_Input.SB.setter\<cdot>(def_Eve1_HLR_Input.SB.getter\<cdot>sb))
              (def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(def_Eve1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
    shows "P ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Output.channels\<^sup>\<Omega>)"
  apply(insert eve1_pred_general[OF assms(1),
    of "\<lambda> s1 s2. P (def_SecureProtocol_HLR2_eve1_Input.SB.setter\<cdot>s1) (def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>s2)"
  ])
  by (metis assms(2) def_SecureProtocol_HLR2_eve1_Input.SB.set_get def_SecureProtocol_HLR2_eve1_Output.SB.set_get)




lemma eve2_pred_inst2def_sb:
  assumes "\<And>spf sb. spf \<in> def_Eve2_HLR.Sps () \<Longrightarrow>
        P (def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>(def_Eve2_HLR_Input.SB.getter\<cdot>sb))
          (def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>(def_Eve2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
      and "spf \<in> def_SecureProtocol_HLR2_eve2.Sps ()"
    shows "P sb (spf\<cdot>sb)"
  apply(insert assms(2))
  apply (auto simp add: def_SecureProtocol_HLR2_eve2.Sps_def def_SecureProtocol_HLR2_eve2_InputMap.Sps_def def_SecureProtocol_HLR2_eve2_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1)
  by (metis def_SecureProtocol_HLR2_eve2_Input.SB.set_get def_Eve2_HLR_Input.SB.get_set)

lemma eve2_pred_general_sb:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
      and "\<And>spf sb. spf \<in> def_Eve2_HLR.Sps () \<Longrightarrow>
            P (def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>(def_Eve2_HLR_Input.SB.getter\<cdot>sb))
              (def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>(def_Eve2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
    shows "P ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Output.channels\<^sup>\<Omega>)"
  apply(insert eve2_pred_general[OF assms(1),
    of "\<lambda> s1 s2. P (def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>s1) (def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>s2)"
  ])
  by (metis assms(2) def_SecureProtocol_HLR2_eve2_Input.SB.set_get def_SecureProtocol_HLR2_eve2_Output.SB.set_get)


lemma bob_pred_inst2def_sb:
  assumes "\<And>spf sb. spf \<in> def_Bob_HLR.Sps () \<Longrightarrow>
        P (def_SecureProtocol_HLR2_bob_Input.SB.setter\<cdot>(def_Bob_HLR_Input.SB.getter\<cdot>sb))
          (def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>(def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
      and "spf \<in> def_SecureProtocol_HLR2_bob.Sps ()"
    shows "P sb (spf\<cdot>sb)"
  apply(insert assms(2))
  apply (auto simp add: def_SecureProtocol_HLR2_bob.Sps_def def_SecureProtocol_HLR2_bob_InputMap.Sps_def def_SecureProtocol_HLR2_bob_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1)
  by (metis def_SecureProtocol_HLR2_bob_Input.SB.set_get def_Bob_HLR_Input.SB.get_set)

lemma bob_pred_general_sb:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
      and "\<And>spf sb. spf \<in> def_Bob_HLR.Sps () \<Longrightarrow>
            P (def_SecureProtocol_HLR2_bob_Input.SB.setter\<cdot>(def_Bob_HLR_Input.SB.getter\<cdot>sb))
              (def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>(def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb)))"
    shows "P ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega>)"
  apply(insert bob_pred_general[OF assms(1),
    of "\<lambda> s1 s2. P (def_SecureProtocol_HLR2_bob_Input.SB.setter\<cdot>s1) (def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>s2)"
  ])
  by (metis assms(2) def_SecureProtocol_HLR2_bob_Input.SB.set_get def_SecureProtocol_HLR2_bob_Output.SB.set_get)


lemma alice_out_eve1_in:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "def_SecureProtocol_HLR2_alice_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)
        = def_SecureProtocol_HLR2_eve1_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)"
proof-
  define ins where "ins = (def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>))"
  define outs where "outs = (def_SecureProtocol_HLR2.RawOutput.getter\<cdot>(spf\<cdot>sb))"

  have 1: "def_SecureProtocol_HLR2_alice_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)
        = def_SecureProtocol_HLR2_rawoutput2alice outs"
    by (simp add: alice_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_alice_Output.sbgetter_def outs_def)

  have 2: "def_SecureProtocol_HLR2_eve1_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)
      = (def_SecureProtocol_HLR2_rawinput2eve1 ins)"
    apply(simp only: ins_def def_SecureProtocol_HLR2.eve1_input_Sub.getter_sub_eq[symmetric])
    by (subst def_SecureProtocol_HLR2_eve1_Input.getter_fold,
        subst sb_star21, simp, simp)

  have 3: "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_rawinput2connector ins) = def_SecureProtocol_HLR2_rawoutput2connector outs"
    by (metis (no_types, lifting) assms connector_apply_eq connector_input_Sub.getter_sub_eq connector_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.sbgetter_def
        def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.sbgetter_def sbtypecast_reduce1 ins_def outs_def)

  have 4: "rawinput2def_attackedsystem_hlr2_feedback ins = rawoutput2def_attackedsystem_hlr2_feedback outs"
    apply(simp only: ins_def outs_def feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
    apply(subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
    using assms by(subst feedback_getter_eq, simp, simp)

  show ?thesis
    apply(simp only: 1 2)
    apply(case_tac outs, case_tac ins)
    using 3 4 by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)
qed


lemma eve1_out_bob_in:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "def_SecureProtocol_HLR2_eve1_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)
        = def_SecureProtocol_HLR2_bob_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)"
proof-
  define ins where "ins = (def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>))"
  define outs where "outs = (def_SecureProtocol_HLR2.RawOutput.getter\<cdot>(spf\<cdot>sb))"

  have 1: "def_SecureProtocol_HLR2_eve1_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)
        = def_SecureProtocol_HLR2_rawoutput2eve1 outs"
    by (simp add: eve1_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_eve1_Output.sbgetter_def outs_def)

  have 2: "def_SecureProtocol_HLR2_bob_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)
      = (def_SecureProtocol_HLR2_rawinput2bob ins)"
    apply(simp only: ins_def def_SecureProtocol_HLR2.bob_input_Sub.getter_sub_eq[symmetric])
    by (subst def_SecureProtocol_HLR2_bob_Input.getter_fold,
        subst sb_star21, simp, simp)

  have 3: "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_rawinput2connector ins) = def_SecureProtocol_HLR2_rawoutput2connector outs"
    by (metis (no_types, lifting) assms connector_apply_eq connector_input_Sub.getter_sub_eq connector_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.sbgetter_def
        def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.sbgetter_def sbtypecast_reduce1 ins_def outs_def)

  have 4: "rawinput2def_attackedsystem_hlr2_feedback ins = rawoutput2def_attackedsystem_hlr2_feedback outs"
    apply(simp only: ins_def outs_def feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
    apply(subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
    using assms by(subst feedback_getter_eq, simp, simp)

  show ?thesis
    apply(simp only: 1 2)
    apply(case_tac outs, case_tac ins)
    using 3 4 by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)
qed


lemma bob_ctrl_eve2_in:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "fst (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>))
        = def_SecureProtocol_HLR2_eve2_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)"
proof-
  define ins where "ins = (def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>))"
  define outs where "outs = (def_SecureProtocol_HLR2.RawOutput.getter\<cdot>(spf\<cdot>sb))"

  have 1: "def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)
        = def_SecureProtocol_HLR2_rawoutput2bob outs"
    by (simp add: bob_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_bob_Output.sbgetter_def outs_def)

  have 2: "def_SecureProtocol_HLR2_eve2_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)
      = (def_SecureProtocol_HLR2_rawinput2eve2 ins)"
    apply(simp only: ins_def def_SecureProtocol_HLR2.eve2_input_Sub.getter_sub_eq[symmetric])
    by (subst def_SecureProtocol_HLR2_eve2_Input.getter_fold,
        subst sb_star21, simp, simp)

  have 3: "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_rawinput2connector ins) = def_SecureProtocol_HLR2_rawoutput2connector outs"
    by (metis (no_types, lifting) assms connector_apply_eq connector_input_Sub.getter_sub_eq connector_output_Sub.getter_sub_eq def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.sbgetter_def
        def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.sbgetter_def sbtypecast_reduce1 ins_def outs_def)

  have 4: "rawinput2def_attackedsystem_hlr2_feedback ins = rawoutput2def_attackedsystem_hlr2_feedback outs"
    apply(simp only: ins_def outs_def feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
    apply(subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
    using assms by(subst feedback_getter_eq, simp, simp)

  show ?thesis
    apply(simp only: 1 2)
    apply(case_tac outs, case_tac ins)
    using 3 4 by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)
qed


end
