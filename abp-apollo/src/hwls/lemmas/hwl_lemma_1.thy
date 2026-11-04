theory hwl_lemma_1
  imports
    move_to_core.hwl_core_ext
    move_to_core.TsynStreamExtension

    hwl_lemma_util
    hwl_encrypt_decrypt
begin


definition Data_Bool_TupleProjSnd :: "Data_Bool_Tuple tsyn stream \<rightarrow> bool tsyn stream" where
  "Data_Bool_TupleProjSnd = tsynProjSnd oo (tsynMap Data_Bool_Tuple2tuple)"


definition lemma1_pred where
"lemma1_pred \<equiv> \<lambda> (i :: Data_Bool_Tuple tsyn stream) (out :: bool tsyn stream).
    #\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>(i))) \<ge> #\<^sub>-(\<alpha>\<^sub>-(out))"

lemma tsynBoolFilter_alt_intro: "tsynBoolFilter\<cdot>y\<cdot>ora = \<Pi>\<^sub>1\<^sub>-({(d::'a :: countable, True::bool). True} \<ominus>\<^sub>- tsynZip\<cdot>y\<cdot>ora)"
  apply(simp add: tsynBoolFilter_def)
  apply(subgoal_tac "{t::'a \<times> bool. \<exists>d::'a. t = (d, True)} = {(d::'a, True::bool). True}")
   apply (metis snd_def)
  by auto

lemma Data_Bool_TupleProjSnd_tsynBoolFilter_corr:
  "Data_Bool_TupleProjSnd\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora) = tsynBoolFilter\<cdot>(Data_Bool_TupleProjSnd\<cdot>y)\<cdot>ora"
  apply(simp add: Data_Bool_TupleProjSnd_def tsynProjSnd_def)
  apply (induction y arbitrary: ora, simp_all)
  apply(case_tac ora, auto)
  apply(case_tac a, auto)
   apply (simp add: tsynboolfilter_Eps_bool_rec tsynmap_sconc_Eps)
  apply(case_tac aa, auto)
   apply(simp add: tsynMap_def smaps2smap tsynboolfilter_msg_true_rec)
  by(simp add: tsynMap_def smaps2smap tsynboolfilter_msg_false_rec)

lemma tsynlen_boolfilter_remdups_Data_Bool_TupleProjSnd_leq:
  "#\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora)))
   \<le> #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(Data_Bool_TupleProjSnd\<cdot>y)\<cdot>ora))"
  by(simp add: Data_Bool_TupleProjSnd_tsynBoolFilter_corr)

lemma lemma1_streams_1:
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
      and "eve1_input = alice_output"
    shows "#\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>alice_output)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>eve1_output))"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_eve1_InputMap.connector_def
      def_SecureProtocol_HLR2_eve1_OutputMap.connector_def)
  apply(simp add: def_Eve1_HLR.wholePredicate_def)
  apply(simp add:
      def_Eve1_HLR.assumption_0_def
      def_Eve1_HLR.predicate_0_def)
  apply auto
  using well_all apply blast+
  using Data_Bool_TupleProjSnd_tsynBoolFilter_corr tsynlen_remdups_boolfilter_leq by auto

lemma lemma1_streams_2:
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
    and "def_Bob_HLR.assumption_0 () eve1_output (bob_control, bob_output)"
    and "def_Bob_HLR.assumption_1 () eve1_output (bob_control, bob_output)"
    and "bob_input = eve1_output"
    shows "#\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>eve1_output)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(bob_control))"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_bob_InputMap.connector_def
      def_SecureProtocol_HLR2_bob_OutputMap.connector_def)
  apply(simp add: def_Bob_HLR.wholePredicate_def)
  apply(simp add: Abs_cfun_id_x)
  apply(simp add:
      def_Bob_HLR.assumption_0_def
      def_Bob_HLR.predicate_0_def
      def_Bob_HLR.assumption_1_def
      def_Bob_HLR.predicate_1_def)
  apply auto
  using well_all apply blast+
  by(simp add: Data_Bool_TupleProjSnd_def tsynMap_def tsynApplyElem_def2[symmetric] tsynlen_tsynremdups_cons_eps)

lemma lemma1_streams_3:
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
    and "eve2_input = bob_control"
    shows "#\<^sub>-(\<alpha>\<^sub>-(bob_control)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(eve2_output))"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_eve2_InputMap.connector_def
      def_SecureProtocol_HLR2_eve2_OutputMap.connector_def)
  apply(simp add: def_Eve2_HLR.wholePredicate_def)
  apply(simp add:
      def_Eve2_HLR.assumption_0_def
      def_Eve2_HLR.predicate_0_def)
  apply auto
  using well_all apply blast+
  using Data_Bool_TupleProjSnd_tsynBoolFilter_corr tsynlen_remdups_boolfilter_leq by auto



lemma lemma1_pred_whole:
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
    shows "lemma1_pred alice_output dec2_output"
  apply(subst lemma1_pred_def)
  apply(insert lemma1_streams_1[OF encrypt_decrypt_1[OF assms(3,5,7,10,11)] assms(9)])
  apply(insert lemma1_streams_2[OF assms(2), of dec1_output])
  apply(insert lemma1_streams_3[OF encrypt_decrypt_2[OF assms(4,6,8,14,15)] assms(13)])
  by(simp add: def_Bob_HLR.assumption_0_def def_Bob_HLR.assumption_1_def
      def_Eve1_HLR.assumption_0_def def_Eve2_HLR.assumption_0_def assms)

lemma lemma1_pred_whole2:
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
  shows "lemma1_pred
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output)
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt2 output)"
  apply(case_tac "output", case_tac "input")
  apply(rule lemma1_pred_whole)
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)


lemma lemma1_raw_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "lemma1_pred
          (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))
          (def_SecureProtocol_HLR2_decrypt2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_output1_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output6_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR2_alice_Output.sbgetter_def
                  def_SecureProtocol_HLR2_decrypt2_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2.alice_output_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.decrypt2_output_Sub.getter_sub_eq)

  apply(rule lemma1_pred_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])

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

lemma lemma1:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "i = def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>(spf\<cdot>(sb)\<star>)"
    and "out = def_SecureProtocol_HLR2_decrypt2_Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>)"
  shows "#\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>(i))) \<ge> #\<^sub>-(\<alpha>\<^sub>-(out))"
  using assms lemma1_pred_def lemma1_raw_pred_whole by presburger

end
