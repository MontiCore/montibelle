theory ref_SecureProtocol_HLR2_rough_SecureProtocol_HLR1
  imports
    (* Gen  *) sps_SecureProtocol_HLR1.def_SecureProtocol_HLR1 sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2
               sps_SecureProtocol_HLR2_alice.def_SecureProtocol_HLR2_alice sps_SecureProtocol_HLR2_encrypt1.def_SecureProtocol_HLR2_encrypt1 sps_SecureProtocol_HLR2_eve1.def_SecureProtocol_HLR2_eve1 sps_SecureProtocol_HLR2_decrypt1.def_SecureProtocol_HLR2_decrypt1 sps_SecureProtocol_HLR2_bob.def_SecureProtocol_HLR2_bob sps_SecureProtocol_HLR2_encrypt2.def_SecureProtocol_HLR2_encrypt2 sps_SecureProtocol_HLR2_eve2.def_SecureProtocol_HLR2_eve2 sps_SecureProtocol_HLR2_decrypt2.def_SecureProtocol_HLR2_decrypt2 
    (* Hwl  *) lemmas.hwl_refinement

begin

lemma causality:
  assumes "def_Alice_HLR.causality  (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(alice_control, alice_input)) (def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(alice_output))"
  assumes "def_Encrypt1_HLR.causality  (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(encrypt1_input)) (def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(encrypt1_output))"
  assumes "def_Eve1_HLR.causality  (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
  assumes "def_Decrypt1_HLR.causality (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(decrypt1_input)) (def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(decrypt1_output))"
  assumes "def_Bob_HLR.causality (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
  assumes "def_Encrypt2_HLR.causality (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(encrypt2_input)) (def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(encrypt2_output))"
  assumes "def_Eve2_HLR.causality (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
  assumes "def_Decrypt2_HLR.causality (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(decrypt2_input)) (def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(decrypt2_output))"
      and "alice_input = input"
      and "encrypt1_input = alice_output"
      and "eve1_input = encrypt1_output"
      and "decrypt1_input = eve1_output"
      and "bob_input = decrypt1_output"
      and "encrypt2_input = bob_control"
      and "eve2_input = encrypt2_output"
      and "decrypt2_input = eve2_output"
      and "alice_control = decrypt2_output"
      and "output = bob_output"
    shows "def_SecureProtocol_HLR1.causality (input) (output)"
  apply(insert assms(1-8))
  apply(simp add: def_Bob_HLR.wholePredicate_def
                  def_Bob_HLR.causality_def
                  def_Alice_HLR.wholePredicate_def
                  def_Alice_HLR.causality_def
                  def_Eve1_HLR.wholePredicate_def
                  def_Eve1_HLR.causality_def
                  def_Eve2_HLR.wholePredicate_def
                  def_Eve2_HLR.causality_def
                  def_Decrypt1_HLR.wholePredicate_def
                  def_Decrypt1_HLR.causality_def
                  def_Decrypt2_HLR.wholePredicate_def
                  def_Decrypt2_HLR.causality_def
                  def_Encrypt1_HLR.wholePredicate_def
                  def_Encrypt1_HLR.causality_def
                  def_Encrypt2_HLR.wholePredicate_def
                  def_Encrypt2_HLR.causality_def
                  def_SecureProtocol_HLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_SecureProtocol_HLR2_decrypt2_OutputMap.connector_def def_SecureProtocol_HLR2_decrypt2_InputMap.connector_def def_SecureProtocol_HLR2_encrypt2_InputMap.connector_def def_SecureProtocol_HLR2_decrypt1_InputMap.connector_def def_SecureProtocol_HLR2_encrypt2_OutputMap.connector_def def_SecureProtocol_HLR2_decrypt1_OutputMap.connector_def def_SecureProtocol_HLR2_encrypt1_OutputMap.connector_def def_SecureProtocol_HLR2_encrypt1_InputMap.connector_def def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_InputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq)?
  apply(simp add: def_SecureProtocol_HLR1.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  apply (auto simp add: assms)
  apply(subgoal_tac "#input \<le> #decrypt2_output")
   apply(subgoal_tac "#decrypt1_output <\<^sup>l #bob_output")
    apply (metis (no_types, lifting)  len_prod_leq  dual_order.trans lnle_and_gt_inf(1) nle_le)
   apply (metis len_prod_minr trans_lnle)
  using not_that_hard[of decrypt2_output input alice_output encrypt1_output eve1_output decrypt1_output bob_control bob_output encrypt2_output eve2_output]
  apply(auto simp add: assms)
  (* autosledgi *) sorry


lemma causality_whole:
  assumes "def_Alice_HLR.causality (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(alice_control, alice_input)) (def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(alice_output))"
  assumes "def_Encrypt1_HLR.causality (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(encrypt1_input)) (def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(encrypt1_output))"
  assumes "def_Eve1_HLR.causality (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
  assumes "def_Decrypt1_HLR.causality (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(decrypt1_input)) (def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(decrypt1_output))"
  assumes "def_Bob_HLR.causality (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
  assumes "def_Encrypt2_HLR.causality (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(encrypt2_input)) (def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(encrypt2_output))"
  assumes "def_Eve2_HLR.causality (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
  assumes "def_Decrypt2_HLR.causality (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(decrypt2_input)) (def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(decrypt2_output))"
      and "alice_input = input"
      and "encrypt1_input = alice_output"
      and "eve1_input = encrypt1_output"
      and "decrypt1_input = eve1_output"
      and "bob_input = decrypt1_output"
      and "encrypt2_input = bob_control"
      and "eve2_input = encrypt2_output"
      and "decrypt2_input = eve2_output"
      and "alice_control = decrypt2_output"
      and "output = bob_output"
    shows "def_SecureProtocol_HLR1.causality (input) (output)"
  apply(rule causality[of alice_control alice_input alice_output encrypt1_input encrypt1_output eve1_input eve1_output decrypt1_input decrypt1_output bob_input bob_control bob_output encrypt2_input encrypt2_output eve2_input eve2_output decrypt2_input decrypt2_output])
  apply(insert assms)
  by(auto simp add: assms def_Bob_HLR.wholePredicate_def def_Alice_HLR.wholePredicate_def def_Eve1_HLR.wholePredicate_def def_Eve2_HLR.wholePredicate_def)

lemma causality_whole2:
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
    shows "def_SecureProtocol_HLR1.causality (rawinput2def_SecureProtocol_hlr2 input) (rawoutput2def_SecureProtocol_hlr2 output)"
  apply(rule rawinput2def_SecureProtocol_hlr2.cases[of "input"],
        rule rawoutput2def_SecureProtocol_hlr2.cases[of "output"], simp)
  apply(rule_tac
          alice_control="channel_alice_control_val_pattern"
      and alice_input="channel_alice_input_val_pattern"
      and alice_output="channel_alice_output_val_pattern"
      and alice_input="channel_alice_input_val_pattern"
      and encrypt1_input="channel_encrypt1_input_val_pattern"
      and encrypt1_output="channel_encrypt1_output_val_pattern"
      and eve1_input="channel_eve1_input_val_pattern"
      and eve1_output="channel_eve1_output_val_pattern"
      and decrypt1_input="channel_decrypt1_input_val_pattern"
      and decrypt1_output="channel_decrypt1_output_val_pattern"
      and bob_input="channel_bob_input_val_pattern"
      and bob_output="channel_bob_output_val_pattern"
      and bob_control="channel_bob_control_val_pattern"
      and encrypt2_input="channel_encrypt2_input_val_pattern"
      and encrypt2_output="channel_encrypt2_output_val_pattern"
      and eve2_input="channel_eve2_input_val_pattern"
      and eve2_output="channel_eve2_output_val_pattern"
      and decrypt2_input="channel_decrypt2_input_val_pattern"
      and decrypt2_output="channel_decrypt2_output_val_pattern"
       in causality_whole)
  using assms apply (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)
  apply(simp_all add:
      def_Alice_HLR.wholePredicate_def
      def_Encrypt1_HLR.wholePredicate_def
      def_Eve1_HLR.wholePredicate_def
      def_Decrypt1_HLR.wholePredicate_def
      def_Bob_HLR.wholePredicate_def
      def_Encrypt2_HLR.wholePredicate_def
      def_Eve2_HLR.wholePredicate_def
      def_Decrypt2_HLR.wholePredicate_def)
  done


lemma raw_causality_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "def_SecureProtocol_HLR1.causality
          (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>(sb\<star>))
          (def_SecureProtocol_HLR1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_input_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR1_Input.sbgetter_def
                  def_SecureProtocol_HLR1_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2_input_Sub.getter_sub_eq
      def_SecureProtocol_HLR2_output_Sub.getter_sub_eq)

  apply(rule causality_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])


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


lemma causality':
  assumes "spf\<in>(def_SecureProtocol_HLR2.Sps ())"
    shows "def_SecureProtocol_HLR1.causality
             (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>sb)
             (def_SecureProtocol_HLR1_Output.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(rule spsconvert_predicate)
  using assms apply(simp add: def_SecureProtocol_HLR2.Sps_def)
  using raw_causality_whole apply blast
  using assert_output_type apply linarith
  using assert_input_type by linarith

lemma comp_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.Sps ())"
    shows "def_SecureProtocol_HLR1.wholePredicate ()
             (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>sb)
             (def_SecureProtocol_HLR1_Output.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(auto simp add: def_SecureProtocol_HLR1.wholePredicate_def def_SecureProtocol_HLR1.assumption_0_def def_SecureProtocol_HLR1.predicate_0_def)
   apply(simp add: wellformed_stream_def tlen_prod_def)
  apply (metis assms def_SecureProtocol_HLR1_Input.SB.getter_len pred_0_lifted sbconv_eq somechannotempty tsynEps_tsynEps2slen_infinite_msg)
  by(simp add: assms causality')

lemma refinement[simp]: "def_SecureProtocol_HLR2.Sps () \<subseteq> def_SecureProtocol_HLR1.Sps ()"
  by(simp add: subsetI def_SecureProtocol_HLR1.Sps_def comp_pred_whole)

end
