theory hwl_len1
  imports
    move_to_core.hwl_core_ext
    move_to_core.TsynStreamExtension

    hwl_lemma_util
    hwl_lemma_1
    hwl_lemma_3
    hwl_inf_x_ctrl
    hwl_S4
begin


definition pred where
"pred \<equiv> \<lambda> (i :: nat tsyn stream) (alice_out :: Data_Bool_Tuple tsyn stream).
    #i = \<infinity> \<longrightarrow>
      #\<^sub>-i = #\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>- alice_out))"

lemma lemma1_bridge:
  "#\<^sub>-(\<alpha>\<^sub>-(Data_Bool_TupleProjSnd\<cdot>alice_output)) \<le> #\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(\<alpha>\<^sub>-alice_output))"
  apply(simp add: tsynMap_def2 smap_Data_Bool_Tuple_get_snd_def2 Data_Bool_TupleProjSnd_def)
  apply(subst tsynRemDups_smap[of "map_tsyn Data_Bool_Tuple2tuple"])
    apply (simp add: tsyn.inj_map)+
  by (simp add: tsynprojsnd_tsynlen tsynremdups_proj2_tsynlen)

lemma len_h1:
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
    shows "#\<^sub>-(\<alpha>\<^sub>-(alice_ctrl)) \<le> #\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>(\<alpha>\<^sub>-alice_output))"
  apply(insert hwl_lemma_1.lemma1_pred_whole[OF assms, simplified lemma1_pred_def])
  apply(simp add: assms Data_Bool_TupleProjSnd_def)
  by (metis (no_types, lifting) Data_Bool_TupleProjSnd_def cfcomp2 dual_order.trans lemma1_bridge)

lemma len_x_sender_leq:
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
  assumes "#alice_input = \<infinity>"
  shows "#\<^sub>-alice_input \<ge> #\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output))" 
proof - 
  have repl: "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>alice_output)))
        = #\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output))"
    apply(simp add: smap_Data_Bool_Tuple_get_fst_def2)
    apply(subst tsynRemDups_smap[of "map_tsyn Data_Bool_Tuple2tuple"])
    by (simp add: tsyn.inj_map)+
  have "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output)) = min (#\<^sub>-alice_input) (Fin 1 +  #\<^sub>-(\<alpha>\<^sub>-alice_ctrl))"
    apply(insert hwl_inf_x_ctrl.pred_whole[OF assms(1-8), simplified hwl_inf_x_ctrl.pred_def, rule_format, OF assms(9-17)])
    apply(insert assms(1))
    apply(simp add: def_Alice_HLR.wholePredicate_def def_Alice_HLR.assumption_0_def def_Alice_HLR.predicate_0_def def_Alice_HLR.causality_def)
    apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector_def def_SecureProtocol_HLR2_alice_OutputMap.connector_def)
    apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
    apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def repl)
    using assms(16,17) by fastforce

  then show ?thesis 
    by simp
qed


lemma B29:
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
  assumes "#alice_input = \<infinity>"
      and "#alice_ctrl = \<infinity>"
      and "#\<^sub>-alice_input \<le> #\<^sub>-(\<alpha>\<^sub>-alice_ctrl)"
  shows "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output)) = #\<^sub>-alice_input"
  apply(insert assms(1))
  apply(simp add: def_Alice_HLR.wholePredicate_def def_Alice_HLR.assumption_0_def def_Alice_HLR.predicate_0_def def_Alice_HLR.causality_def)
  apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector_def def_SecureProtocol_HLR2_alice_OutputMap.connector_def)
  apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
  by (metis (no_types, lifting) assms hwl_S4.pred_def hwl_S4.pred_whole lnat_add_leq min.orderE)


lemma len_h2:
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
  assumes "#alice_input = \<infinity>"
    and "#\<^sub>-alice_ctrl < \<infinity>"
  shows "#\<^sub>-alice_input \<le> #\<^sub>-(\<alpha>\<^sub>-alice_ctrl)"
  apply(subgoal_tac "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output)) < \<infinity>")
   apply(subgoal_tac "#\<^sub>-alice_output < \<infinity> \<Longrightarrow> #\<^sub>-alice_input \<le> #\<^sub>-(\<alpha>\<^sub>-alice_ctrl)")
  using hwl_inf_x_ctrl.pred_whole[OF assms(1-8), simplified hwl_inf_x_ctrl.pred_def, rule_format, OF assms(9-17)]
    apply (metis assms inf_great lemma3_pred_def lemma3_pred_whole linorder_less_linear)
   apply(insert assms(1))
   apply(simp add: def_Alice_HLR.wholePredicate_def def_Alice_HLR.assumption_0_def def_Alice_HLR.predicate_0_def def_Alice_HLR.causality_def)
   apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector_def def_SecureProtocol_HLR2_alice_OutputMap.connector_def)
   apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
   apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
   apply (metis \<open>#(dec2_output::bool tsyn stream) = \<infinity>\<close> assms(16,17) inf_great linorder_le_less_linear)
  by (metis assms(10,11,12,13,14,15,16,18,2,3,4,5,6,7,8,9) encrypt_decrypt_1 encrypt_decrypt_2 leD lemma3_streams_1 lemma3_streams_2 lemma3_streams_3 tsynLen_smap_map_tsyn tsynlen_not_inf_eq_inf
      tsynlen_tsynremdups_le)
  

lemma B5:
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
    shows "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output)) \<ge> #\<^sub>-(\<alpha>\<^sub>-(alice_ctrl))"
  using len_h1[OF assms]
  by (metis tsynLen_smap_map_tsyn)


lemma B28:
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
  assumes "#alice_input = \<infinity>" and "#alice_ctrl = \<infinity>" and "#\<^sub>-alice_input > #\<^sub>-(\<alpha>\<^sub>-alice_ctrl)"
  shows "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output)) = 1 + #\<^sub>-(\<alpha>\<^sub>-alice_ctrl)" 
  using hwl_S4.pred_whole[OF assms(1-7), simplified hwl_S4.pred_def, rule_format, OF assms(8-18)]
  by (metis assms(19) less2lnleD lnat_plus_fin lnat_well_h2 min.absorb2 min.absorb4 min.strict_order_iff one_lnat_def plus_1_eq_Suc tsynlen_not_inf_eq_inf)


lemma B34:
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
    assumes inf_y: "#\<^sub>-alice_output < \<infinity>"
    shows "#\<^sub>-alice_ctrl < \<infinity>"
proof -
  have live_proj2: "#\<^sub>-(smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>dec1_output) < \<infinity>"
    using tsynprojsnd_tsynlen inf_y assms
  proof -
    have f1: "def_Eve1_HLR.wholePredicate () alice_output dec1_output"
      by (metis assms(10,11,3,5,7,9) def_SecureProtocol_HLR2_eve1_InputMap.connector.abs_eq def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq
          def_SecureProtocol_HLR2_eve1_OutputMap.connector.abs_eq encrypt_decrypt_1)
    have f2: "\<forall>s u sa. \<not> def_Eve1_HLR.wholePredicate u s sa \<or> \<not> def_Eve1_HLR.assumption_0 u s sa \<or> def_Eve1_HLR.predicate_0 u s sa"
      using def_Eve1_HLR.wholePredicate_def well_all by blast
    have f3: "\<forall>u. (\<lambda>s sa. True) = def_Eve1_HLR.assumption_0 u"
      by (simp add: def_Eve1_HLR.assumption_0_def)
    have "\<forall>u. (\<lambda>s sa. \<exists>sb. #({True} \<ominus> sb) = \<infinity> \<and> sa = tsynBoolFilter\<cdot>s\<cdot>sb) = def_Eve1_HLR.predicate_0 u"
      by (metis (lifting) case_unit def_Eve1_HLR.predicate_0_def)
    then have "\<exists>s. #({True} \<ominus> s) = \<infinity> \<and> dec1_output = tsynBoolFilter\<cdot>alice_output\<cdot>s"
      using f3 f2 f1 by presburger
    then show ?thesis
      by (metis (no_types) dual_order.strict_iff_not inf_great inf_y linorder_neq_iff tsyn2ustream_len tsynlen_boolfilter tsynlen_insert)
  qed
  show ?thesis
    apply(simp add: assms(16))
    apply(insert encrypt_decrypt_2[OF assms(4,6,8,14,15)])
    apply(simp add: def_Eve2_HLR.wholePredicate_def def_Eve2_HLR.assumption_0_def def_Eve2_HLR.predicate_0_def def_Eve2_HLR.causality_def)
    apply(simp add: def_SecureProtocol_HLR2_eve2_InputMap.connector_def def_SecureProtocol_HLR2_eve2_OutputMap.connector_def)
    apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
    apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
    apply(simp add: assms(13))
    apply(insert assms(2))
    apply(simp add: def_Bob_HLR.wholePredicate_def def_Bob_HLR.assumption_0_def def_Bob_HLR.predicate_0_def def_Bob_HLR.causality_def)
    apply(simp add: def_SecureProtocol_HLR2_bob_InputMap.connector_def def_SecureProtocol_HLR2_bob_OutputMap.connector_def)
    apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
    apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
    by (metis assms(12) inf_ub live_proj2 lnle_and_gt_inf(2) smap_Data_Bool_Tuple_get_snd_def2 tsynlen_boolfilter tsynlen_not_inf_eq_inf tsynlen_sconc_Eps)
qed


lemma c2: 
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
  assumes "#alice_input = \<infinity>"
      and "#\<^sub>-alice_output = \<infinity>"
    shows "#\<^sub>-(\<alpha>\<^sub>-(alice_output)) = \<infinity>"
  apply(insert assms)
  apply(simp add: def_Alice_HLR.wholePredicate_def def_Alice_HLR.assumption_0_def def_Alice_HLR.predicate_0_def def_Alice_HLR.causality_def)
  apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector_def def_SecureProtocol_HLR2_alice_OutputMap.connector_def)
  apply(simp add: def_Bob_HLR.wholePredicate_def def_Bob_HLR.assumption_0_def def_Bob_HLR.assumption_1_def def_Bob_HLR.predicate_0_def def_Bob_HLR.predicate_1_def def_Bob_HLR.causality_def)
  apply(simp add: def_SecureProtocol_HLR2_bob_InputMap.connector_def def_SecureProtocol_HLR2_bob_OutputMap.connector_def)
  apply(simp add: def_Eve1_HLR.wholePredicate_def def_Eve1_HLR.assumption_0_def def_Eve1_HLR.predicate_0_def def_Eve1_HLR.causality_def)
  apply(simp add: def_SecureProtocol_HLR2_eve1_InputMap.connector_def def_SecureProtocol_HLR2_eve1_OutputMap.connector_def)
  apply(simp add: def_Eve2_HLR.wholePredicate_def def_Eve2_HLR.assumption_0_def def_Eve2_HLR.predicate_0_def def_Eve2_HLR.causality_def)
  apply(simp add: def_SecureProtocol_HLR2_eve2_InputMap.connector_def def_SecureProtocol_HLR2_eve2_OutputMap.connector_def)
  apply(simp add: Let_def case_prod_unfold Abs_cfun_id_x)
  apply(auto simp add: assms weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)
  sorry


lemma fp_len:
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
  assumes "#alice_input = \<infinity>"
  shows "#\<^sub>-(\<alpha>\<^sub>- alice_ctrl) = #\<^sub>-alice_input"
  apply(subgoal_tac "#\<^sub>-(\<alpha>\<^sub>- alice_ctrl) \<le> #\<^sub>-alice_input \<and> #\<^sub>-(\<alpha>\<^sub>- alice_ctrl) \<ge> #\<^sub>-alice_input")
  using nle_le apply blast
  apply(rule conjI)
  using B5 len_x_sender_leq apply (smt assms(1,10,11,12,13,14,15,16,17,2,3,4,5,6,7,8,9) dual_order.trans)
  using len_h2
        B34
        B28
        c2
        hwl_inf_x_ctrl.pred_whole[OF assms(1-8), simplified hwl_inf_x_ctrl.pred_def, rule_format, OF assms(9-17)]
  by (metis (no_types, lifting) assms(1,10,11,12,13,14,15,16,17,2,3,4,5,6,7,8,9) linorder_le_less_linear lnat_1_inf order_less_imp_le plus_lnatInf_l plus_unique_r tsynLen_smap_map_tsyn
      tsynlen_not_inf_eq_inf)

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
    shows "pred alice_input alice_output"
  apply(subst pred_def)
  by(simp add: hwl_inf_x_ctrl.pred_whole[OF assms, simplified hwl_inf_x_ctrl.pred_def]
                  fp_len[OF assms]
                  B29[OF assms])


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
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output)"
  apply(case_tac "output", case_tac "input")
  apply(rule pred_whole)
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)

lemma len1_raw_pred_whole:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
  shows "pred
          (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>(sb\<star>))
          (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_input_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output1_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR1_Input.sbgetter_def
                  def_SecureProtocol_HLR2_alice_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2_input_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.alice_output_Sub.getter_sub_eq)

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

lemmas len1_raw = len1_raw_pred_whole[simplified pred_def, rule_format]


end
