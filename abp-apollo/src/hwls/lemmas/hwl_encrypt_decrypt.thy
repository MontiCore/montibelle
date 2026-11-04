theory hwl_encrypt_decrypt
  imports
    move_to_core.hwl_core_ext
    move_to_core.TsynStreamExtension

    hwl_lemma_util
begin



lemma decrypt1_fn_encrypt1_fn: "(decrypt1_fn o Data_Bool_Tuple2tuple o encrypt1_fn o Data_Bool_Tuple2tuple) = id"
  apply(rule fun_eqI)
  apply(case_tac x)
  by(auto simp add: decrypt1_fn_def encrypt1_fn_def o_def)

lemma encrypt_decrypt_1:
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
  assumes "def_Encrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(enc1_input)) (def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(enc1_output))"
  assumes "def_Decrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(dec1_input)) (def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(dec1_output))"
      and "eve1_input = enc1_output"
      and "dec1_input = eve1_output"
    shows "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(enc1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(dec1_output))"
  apply(insert assms)
  apply(simp add: def_Encrypt1_HLR.wholePredicate_def def_Eve1_HLR.wholePredicate_def def_Decrypt1_HLR.wholePredicate_def Let_def case_prod_unfold)
  apply(simp add: def_SecureProtocol_HLR2_encrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_OutputMap.connector.rep_eq)?
  apply(simp add: def_Encrypt1_HLR.predicate_0_def def_Encrypt1_HLR.causality_def)?
  apply(simp add: def_Eve1_HLR.assumption_0_def def_Eve1_HLR.predicate_0_def def_Eve1_HLR.causality_def)?
  apply(simp add: def_Decrypt1_HLR.predicate_0_def def_Decrypt1_HLR.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(auto)
   apply (rule_tac x="ora" in exI)
  using decrypt1_fn_encrypt1_fn[simplified o_def]
  by (metis inf_ub sfilterl4 tsynboolfilter_tsynmap tsynmap_id2 tsynmap_tsynmap2)

lemma encrypt_decrypt_2:
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
  assumes "def_Encrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(enc2_input)) (def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(enc2_output))"
  assumes "def_Decrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(dec2_input)) (def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(dec2_output))"
      and "eve2_input = enc2_output"
      and "dec2_input = eve2_output"
    shows "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(enc2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(dec2_output))"
  apply(insert assms)
  apply(simp add: def_Encrypt2_HLR.wholePredicate_def def_Eve2_HLR.wholePredicate_def def_Decrypt2_HLR.wholePredicate_def Let_def case_prod_unfold)
  apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_OutputMap.connector.rep_eq)?
  apply(simp add: def_Encrypt2_HLR.predicate_0_def def_Encrypt2_HLR.causality_def)?
  apply(simp add: def_Eve2_HLR.assumption_0_def def_Eve2_HLR.predicate_0_def def_Eve2_HLR.causality_def)?
  apply(simp add: def_Decrypt2_HLR.predicate_0_def def_Decrypt2_HLR.causality_def)?
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(auto)
   apply (rule_tac x="ora" in exI)
  apply(simp_all add: tsynmap_slen)
  apply(subgoal_tac "#enc2_input \<le> #ora")
   apply (simp add: tsynboolfilter_tsynmap)
  by (metis inf_ub sfilterl4)

end
