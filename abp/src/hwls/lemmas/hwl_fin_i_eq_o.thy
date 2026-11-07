theory hwl_fin_i_eq_o
  imports
    move_to_core.hwl_core_ext
    move_to_core.TsynStreamExtension

    move_to_core.TsynSBFunctionExtension
    move_to_core.TsynStreamExtension

    to_be_generated.hwl_tsynSBlens

    hwl_lemma_util

    hwl_eq_slen_eq_and_less
    hwl_med_nomed_eq
    hwl_output_rewrite
begin


definition fin_i_eq_o_pred where
"fin_i_eq_o_pred \<equiv> \<lambda> (i :: nat tsyn stream) (out :: nat tsyn stream).
    #i = \<infinity> \<longrightarrow> #\<^sub>-i < \<infinity> \<longrightarrow>
      out\<^sup>- = i\<^sup>-"

lemma fin_i_eq_o_pred_whole:
  assumes "def_Alice_HLR.wholePredicate () (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(alice_ctrl, alice_input)) (def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(alice_output))"
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
  assumes "def_Encrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(enc1_input)) (def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(enc1_output))"
  assumes "def_Encrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(enc2_input)) (def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(enc2_output))"
  assumes "def_Decrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(dec1_input)) (def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(dec1_output))"
  assumes "def_Decrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(dec2_input)) (def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(dec2_output))"
      and "enc1_input = alice_output"
      and "eve1_input = enc1_output"
      and "dec1_input = eve1_output"
      and "bob_input = dec1_output"
      and "enc2_input = bob_control"
      and "eve2_input = enc2_output"
      and "dec2_input = eve2_output"
      and "alice_ctrl = dec2_output"
    shows "fin_i_eq_o_pred alice_input bob_output"
  apply(subst fin_i_eq_o_pred_def)
  apply(subst hwl_output_rewrite.pred_whole[OF assms, simplified hwl_output_rewrite.pred_def])
  apply(simp add: hwl_med_nomed_eq.pred_whole[OF assms, simplified hwl_med_nomed_eq.pred_def])
  by(rule hwl_eq_slen_eq_and_less.pred_whole[OF assms, simplified hwl_eq_slen_eq_and_less.pred_def])


lemma fin_i_eq_o_pred_whole2:
  assumes "def_Alice_HLR.wholePredicate () (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2alice input))(def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output))"
  assumes "def_Encrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2encrypt1 input))(def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2encrypt1 output))"
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2eve1 input))(def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2eve1 output))"
  assumes "def_Decrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2decrypt1 input))(def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt1 output))"
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2bob input))(def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2bob output))"
  assumes "def_Encrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2encrypt2 input))(def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2encrypt2 output))"
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2eve2 input))(def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2eve2 output))"
  assumes "def_Decrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2decrypt2 input))(def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt2 output))"
  assumes "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_rawinput2connector input) = def_SecureProtocol_HLR2_rawoutput2connector output"
  assumes "rawinput2def_SecureProtocol_hlr2_feedback input = rawoutput2def_SecureProtocol_hlr2_feedback output"
  shows "fin_i_eq_o_pred
          (rawinput2def_SecureProtocol_hlr2 input)
          (rawoutput2def_SecureProtocol_hlr2 output)"
  apply(case_tac "output", case_tac "input")
  apply(rule fin_i_eq_o_pred_whole)
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)

lemma fin_i_eq_o_raw_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "fin_i_eq_o_pred
          (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>(sb\<star>))
          (def_SecureProtocol_HLR1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_input_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR1_Input.sbgetter_def
                  def_SecureProtocol_HLR1_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2_input_Sub.getter_sub_eq
      def_SecureProtocol_HLR2_output_Sub.getter_sub_eq)

  apply(rule fin_i_eq_o_pred_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])


  apply(simp only: alice_input_Sub.getter_sub_eq[symmetric] alice_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_alice_Input.getter_fold,
        subst def_SecureProtocol_HLR2_alice_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule alice_pred_general[OF assms(1)])
  apply(simp add: def_Alice_HLR.Sps_def)
  apply(simp only: encrypt1_input_Sub.getter_sub_eq[symmetric] encrypt1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_encrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_encrypt1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_encrypt1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule encrypt1_pred_general[OF assms(1)])
  apply(simp add: def_Encrypt1_HLR.Sps_def)
  apply(simp only: eve1_input_Sub.getter_sub_eq[symmetric] eve1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_eve1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_eve1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule eve1_pred_general[OF assms(1)])
  apply(simp add: def_Eve1_HLR.Sps_def)
  apply(simp only: decrypt1_input_Sub.getter_sub_eq[symmetric] decrypt1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_decrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_decrypt1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_decrypt1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule decrypt1_pred_general[OF assms(1)])
  apply(simp add: def_Decrypt1_HLR.Sps_def)
  apply(simp only: bob_input_Sub.getter_sub_eq[symmetric] bob_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_bob_Input.getter_fold,
        subst def_SecureProtocol_HLR2_bob_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule bob_pred_general[OF assms(1)])
  apply(simp add: def_Bob_HLR.Sps_def)
  apply(simp only: encrypt2_input_Sub.getter_sub_eq[symmetric] encrypt2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_encrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_encrypt2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_encrypt2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule encrypt2_pred_general[OF assms(1)])
  apply(simp add: def_Encrypt2_HLR.Sps_def)
  apply(simp only: eve2_input_Sub.getter_sub_eq[symmetric] eve2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_eve2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_eve2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule eve2_pred_general[OF assms(1)])
  apply(simp add: def_Eve2_HLR.Sps_def)
  apply(simp only: decrypt2_input_Sub.getter_sub_eq[symmetric] decrypt2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_decrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_decrypt2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_decrypt2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule decrypt2_pred_general[OF assms(1)])
  apply(simp add: def_Decrypt2_HLR.Sps_def)
  apply(simp only: connector_input_Sub.getter_sub_eq[symmetric]
                   connector_output_Sub.getter_sub_eq[symmetric])
  apply(subst def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.getter_fold,
        subst def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

lemma fin_i_eq_o_nearly:
  assumes "spf\<in> def_SecureProtocol_HLR2.Sps ()"
  shows "fin_i_eq_o_pred (def_SecureProtocol_HLR1_Input.sbgetter\<cdot>sb) (def_SecureProtocol_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  apply(rule spsconvert_predicate[of "spf" "def_SecureProtocol_HLR2.rawSps ()"])
  using assms(1) apply(simp add: def_SecureProtocol_HLR2.Sps_def)
  using fin_i_eq_o_raw_pred_whole apply blast
  by auto

lemma fin_i_eq_o:
  assumes "spf\<in> def_SecureProtocol_HLR2.Sps ()"
    and "i = def_SecureProtocol_HLR1_Input.SB.getter\<cdot>((sb)\<star>)"
    and "#i = \<infinity>"
    and "#\<^sub>-i < \<infinity>"
    and "out = def_SecureProtocol_HLR1_Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>)"
  shows "out\<^sup>- = i\<^sup>-"
  by (metis assms(1,2,3,4,5) fin_i_eq_o_nearly fin_i_eq_o_pred_def sbconv_eq)

lemma fin_i_eq_o2:
  assumes "spf\<in> def_SecureProtocol_HLR2.Sps ()"
    and "output = (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR1_Output.channels\<^sup>\<Omega>)"
    and "input = (sb\<star> :: def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega>)"
    and "#input = \<infinity>"
    and "tsynSBlen input < \<infinity>"
  shows "(def_SecureProtocol_HLR1_Input.sbgetter\<cdot>input)\<^sup>- = (def_SecureProtocol_HLR1_Output.sbgetter\<cdot>output)\<^sup>-"
proof-
  define i where "i = def_SecureProtocol_HLR1_Input.SB.getter\<cdot>((sb)\<star>)"
  have 1: "#i = \<infinity>"
    by (metis assms(3,4) def_SecureProtocol_HLR1_Input.SB.getter_len i_def somechannotempty)
  have 2: "#\<^sub>-i < \<infinity>"
    by (metis Min_singleton assms(3,5) def_SecureProtocol_HLR1_Input.SB.set_get def_SecureProtocol_HLR1_Input_tsynSBlen_setter i_def)
  show ?thesis
    by (metis "1" "2" assms(1,2,3) fin_i_eq_o i_def)
qed


end
