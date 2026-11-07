theory hwl_lemma_3
  imports
    move_to_core.hwl_core_ext
    
    to_be_generated.hwl_tsynSBlens
    
    hwl_lemma_util
    hwl_encrypt_decrypt
begin


lemma liveness_helper: "#i = \<infinity> \<longrightarrow> sprojsnd\<cdot>({(d, True)|d. True} \<ominus> szip\<cdot>i\<cdot>ora) = {True} \<ominus> ora"
proof (induction ora arbitrary:i)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a ora)
  then show ?case 
    apply (cases i)
     apply simp
    apply (cases a)
    by simp_all
qed

lemma TsynBoolFilter_live:
  "#\<^sub>-i = \<infinity> \<longrightarrow> (#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora) = #({True} \<ominus> ora))"
proof
  assume inf_i: "#\<^sub>-i = \<infinity>"
  have inf_u_i: "#(tsyn2ustream\<cdot>i) = \<infinity> " 
    using inf_i by (simp add: tsynlen_insert)

  have a1: "#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora)
            = #\<^sub>-(\<Pi>\<^sub>1\<^sub>-({(d, True)|d. True} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora))"
    apply (simp add: tsynBoolFilter_def)
    by (metis (full_types) Pair_inject prod.collapse)
  have a2: "... = #(tsyn2ustream\<cdot>({(d, True)|d. True} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora))"
    by (simp add: slen_sprojfst tsynprojfst_tsynabs tsynlen_insert snd_def)
  have a3: "... = #(tsyn2ustream\<cdot>({TSynMsg (d, True)|d. True} \<ominus> tsynZip\<cdot>i\<cdot>ora))"
    by (metis (no_types, lifting) ext tsynzip_tsynabs tsynfilter_tsynabs tsynzip_tsynabs2)
  have b1: "... = #({(d, True)|d. True} \<ominus> szip\<cdot>(tsyn2ustream\<cdot>i)\<cdot>ora)"
    by (metis (lifting) ext tsynzip_tsynabs2)
  have b2: "... = #(sprojsnd\<cdot>({(d, True)|d. True} \<ominus> szip\<cdot>(tsyn2ustream\<cdot>i)\<cdot>ora))"
    by (simp add: slen_sprojsnd)
  have b3: "... = #({True} \<ominus> ora)"
        using inf_u_i liveness_helper by fastforce
  from a1 a2 a3 b1 b2 b3
  show "#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora) = #({True} \<ominus> ora)" by simp
qed

lemma TsynBoolFilter_live_inf_insert:
  assumes "#\<^sub>-i = \<infinity>"
    and "#({True} \<ominus> ora) = \<infinity>"
  shows "#\<^sub>-(tsynBoolFilter\<cdot>i\<cdot>ora) = \<infinity>"
  by (simp add: TsynBoolFilter_live assms(1,2))

lemma TsynBoolFilter_live_inf_rule:
  assumes "#\<^sub>-i = \<infinity>"
    and "#({True} \<ominus> ora) = \<infinity>"
  shows "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-({(d, True). True} \<ominus>\<^sub>- tsynZip\<cdot>i\<cdot>ora)) = \<infinity>"
proof -
  have a1: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-({uu. \<exists>d :: 'a. uu = (d, True)} \<ominus>\<^sub>- tsynZip\<cdot> i\<cdot> ora)) = \<infinity>"
    apply(insert TsynBoolFilter_live_inf_insert[OF assms])
    apply(simp add: tsynBoolFilter_def)
    by (smt Collect_cong prod.collapse prod.inject)
  have "(\<lambda>(d, b). b) = (\<lambda>p. \<exists>d. p = (d :: 'a, True))"
    by blast
  then show ?thesis
    using a1 by presburger
qed

lemma lemma3_streams_1:
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
      and "eve1_input = alice_output"
    shows "#\<^sub>-alice_output = \<infinity> \<Longrightarrow> #\<^sub>-eve1_output = \<infinity>"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_eve1_InputMap.connector_def
      def_SecureProtocol_HLR2_eve1_OutputMap.connector_def)
  apply(simp add: def_Eve1_HLR.wholePredicate_def)
  apply(simp add:
      def_Eve1_HLR.assumption_0_def
      def_Eve1_HLR.predicate_0_def)
  apply auto
  using well_all by blast+

lemma lemma3_streams_2:
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
      and "bob_input = eve1_output"
    shows "#\<^sub>-eve1_output = \<infinity> \<Longrightarrow> #\<^sub>-bob_control = \<infinity>"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_bob_InputMap.connector_def
      def_SecureProtocol_HLR2_bob_OutputMap.connector_def)
  apply(simp add: def_Bob_HLR.wholePredicate_def)
  apply(simp add:
      def_Bob_HLR.assumption_0_def
      def_Bob_HLR.predicate_0_def
      def_Bob_HLR.assumption_1_def
      def_Bob_HLR.predicate_1_def)
  apply(simp add: Abs_cfun_id_x)
  apply auto
  using well_all apply blast+
  by (metis tsynLen_smap_map_tsyn tsynlen_sconc_Eps tsynprojsnd_tsynlen)

lemma lemma3_streams_3:
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
      and "eve2_input = bob_control"
    shows "#\<^sub>-bob_control = \<infinity> \<Longrightarrow> #\<^sub>-eve2_output = \<infinity>"
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_eve2_InputMap.connector_def
      def_SecureProtocol_HLR2_eve2_OutputMap.connector_def)
  apply(simp add: def_Eve2_HLR.wholePredicate_def)
  apply(simp add:
      def_Eve2_HLR.assumption_0_def
      def_Eve2_HLR.predicate_0_def)
  apply auto
  using well_all by blast+

definition lemma3_pred where
"lemma3_pred \<equiv> \<lambda> (ins :: Data_Bool_Tuple tsyn stream) (outs :: bool tsyn stream).
    #\<^sub>-(ins) = \<infinity> \<longrightarrow> #\<^sub>-(outs) = \<infinity>"

lemma lemma3_pred_whole:
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
    shows "lemma3_pred alice_output dec2_output"
  apply(subst lemma3_pred_def)
  apply(insert lemma3_streams_1[OF encrypt_decrypt_1[OF assms(3,5,7,10,11)] assms(9)])
  apply(insert lemma3_streams_2[OF assms(2,12)])
  apply(insert lemma3_streams_3[OF encrypt_decrypt_2[OF assms(4,6,8,14,15)] assms(13)])
  by(auto)

lemma lemma3_pred_whole2:
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
  shows "lemma3_pred
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output)
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt2 output)"
  apply(case_tac "output", case_tac "input")
  apply(rule lemma3_pred_whole)
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)

lemma lemma3_raw_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "lemma3_pred
          (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))
          (def_SecureProtocol_HLR2_decrypt2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_output1_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output6_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR2_alice_Output.sbgetter_def
                  def_SecureProtocol_HLR2_decrypt2_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2.alice_output_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.decrypt2_output_Sub.getter_sub_eq)

  apply(rule lemma3_pred_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])

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

lemma lemma3:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "tsynSBlen (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR2_alice_Output.channels\<^sup>\<Omega>) = \<infinity> \<Longrightarrow>
    tsynSBlen (((spf\<cdot>(sb)))\<star> :: def_SecureProtocol_HLR2_decrypt2_Output.channels\<^sup>\<Omega>) = \<infinity>"
  apply(simp add: def_SecureProtocol_HLR2_decrypt2_Output_tsynSBlen_setter[of "def_SecureProtocol_HLR2_decrypt2_Output.sbgetter\<cdot>(spf\<cdot>sb\<star>)", simplified])
  apply(simp add: def_SecureProtocol_HLR2_alice_Output_tsynSBlen_setter[of "def_SecureProtocol_HLR2_alice_Output.sbgetter\<cdot>(spf\<cdot>sb\<star>)", simplified])
  apply(insert lemma3_raw_pred_whole[of spf sb, OF assms(1)])
  by(simp add: lemma3_pred_def)

end
