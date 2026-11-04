theory def_SecureProtocol_LLR_bob
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_bob.def_SecureProtocol_LLR_bob_Input bundle_SecureProtocol_LLR_bob.def_SecureProtocol_LLR_bob_Output sps_Bob_LLR.def_Bob_LLR sps_SecureProtocol_LLR_bob_InputMap.def_SecureProtocol_LLR_bob_InputMap sps_SecureProtocol_LLR_bob_OutputMap.def_SecureProtocol_LLR_bob_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_bob_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_LLR_bob_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SecureProtocol_LLR_bob_InputMap.Sps () \<then> def_Bob_LLR.Sps () \<then> def_SecureProtocol_LLR_bob_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Bob_LLR.Sps () \<Longrightarrow> P (def_Bob_HLR_Input.SB.getter\<cdot>sb) (def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SecureProtocol_LLR_bob_Input.SB.getter\<cdot>sb) (def_SecureProtocol_LLR_bob_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SecureProtocol_LLR_bob_InputMap.Sps_def def_SecureProtocol_LLR_bob_OutputMap.Sps_def
    oo_def def_SecureProtocol_LLR_bob_InputMap.connector.rep_eq def_SecureProtocol_LLR_bob_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Bob_HLR_Input.SB.get_set)


end
