theory hwl_len3
  imports
    move_to_core.hwl_core_ext
    move_to_core.TsynStreamExtension

    hwl_lemma_util
    hwl_len2
    hwl_lemma_1
begin


definition pred where
"pred \<equiv> \<lambda> (i :: nat tsyn stream) (alice_out :: Data_Bool_Tuple tsyn stream) (eve1_out :: Data_Bool_Tuple tsyn stream).
    #i = \<infinity> \<longrightarrow>
      #\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(alice_out))) = #\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(eve1_out)))"

lemma pred_whole:
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
    shows "pred alice_input alice_output dec1_output"
proof (subst pred_def, auto)
  assume a: "#alice_input = \<infinity>"

  have "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-(alice_output))) = #\<^sub>-alice_input"
    by (metis (no_types, opaque_lifting) a assms hwl_len1.pred_def hwl_len1.pred_whole)
  then have "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(\<alpha>\<^sub>-(alice_output))) = #\<^sub>-alice_input"
    by (metis tsynLen_smap_map_tsyn)
  then have r: "#\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(alice_output)))
              \<le> #\<^sub>-(\<alpha>\<^sub>-(dec2_output))"
    by (metis assms fp_len[OF assms a] Data_Bool_TupleProjSnd_def cfcomp2 lemma1_bridge smap_Data_Bool_Tuple_get_snd_def2 tsynMap_def2)

  have geq:  "#\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(alice_output)))
                \<ge> #\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(dec1_output)))"
    apply(simp add: assms(12)[symmetric])
    apply(insert encrypt_decrypt_1[OF assms(3,5,7,10,11)])
    apply(simp add: def_Eve1_HLR.wholePredicate_def def_Eve1_HLR.assumption_0_def def_Eve1_HLR.predicate_0_def def_Eve1_HLR.causality_def)
    apply(simp add: def_SecureProtocol_HLR2_eve1_InputMap.connector_def def_SecureProtocol_HLR2_eve1_OutputMap.connector_def)
    apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
    apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
    by (metis Eps_eq_map_tsyn_iff smap_tsynBoolFilter tsynlen_remdups_boolfilter_leq assms)
  also have leq: "#\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(alice_output)))
              \<le> #\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(dec1_output)))"
    apply(insert assms(2))
    apply(simp add: def_Bob_HLR.wholePredicate_def def_Bob_HLR.assumption_0_def def_Bob_HLR.predicate_0_def def_Bob_HLR.assumption_1_def def_Bob_HLR.predicate_1_def def_Bob_HLR.causality_def)
    apply(simp add: def_SecureProtocol_HLR2_bob_InputMap.connector_def def_SecureProtocol_HLR2_bob_OutputMap.connector_def)
    apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
    apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
    apply(insert encrypt_decrypt_2[OF assms(4,6,8,14,15)])
    by (metis (no_types, lifting) assms lemma1_streams_3 order_trans r smap_Data_Bool_Tuple_get_snd_def2 tsynlen_tsynremdups_cons_eps)

  finally show "#\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(alice_output)))
                = #\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(dec1_output)))"
    by metis
qed

lemma pred_whole2:
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
  shows "pred
          (rawinput2def_SecureProtocol_hlr2 input)
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output)
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt1 output)"
  apply(case_tac "output", case_tac "input")
  apply(rule pred_whole)
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)


lemma len3_raw_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "pred
          (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>(sb\<star>))
          (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))
          (def_SecureProtocol_HLR2_decrypt1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_input_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output1_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output5_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR1_Input.sbgetter_def
                  def_SecureProtocol_HLR2_alice_Output.sbgetter_def
                  def_SecureProtocol_HLR2_decrypt1_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2_input_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.alice_output_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.decrypt1_output_Sub.getter_sub_eq)

  apply(rule pred_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])

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

lemmas len3_raw = len3_raw_pred_whole[simplified pred_def, rule_format]

end
