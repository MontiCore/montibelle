theory def_SecureProtocol_LLR_encrypt1
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_LLR_encrypt1.def_SecureProtocol_LLR_encrypt1_Input bundle_SecureProtocol_LLR_encrypt1.def_SecureProtocol_LLR_encrypt1_Output sps_Encrypt1_HLR.def_Encrypt1_HLR sps_SecureProtocol_LLR_encrypt1_InputMap.def_SecureProtocol_LLR_encrypt1_InputMap sps_SecureProtocol_LLR_encrypt1_OutputMap.def_SecureProtocol_LLR_encrypt1_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_LLR_encrypt1_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_LLR_encrypt1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SecureProtocol_LLR_encrypt1_InputMap.Sps () \<then> def_Encrypt1_HLR.Sps () \<then> def_SecureProtocol_LLR_encrypt1_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Encrypt1_HLR.Sps () \<Longrightarrow> P (def_Encrypt1_HLR_Input.SB.getter\<cdot>sb) (def_Encrypt1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SecureProtocol_LLR_encrypt1_Input.SB.getter\<cdot>sb) (def_SecureProtocol_LLR_encrypt1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SecureProtocol_LLR_encrypt1_InputMap.Sps_def def_SecureProtocol_LLR_encrypt1_OutputMap.Sps_def
    oo_def def_SecureProtocol_LLR_encrypt1_InputMap.connector.rep_eq def_SecureProtocol_LLR_encrypt1_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Encrypt1_HLR_Input.SB.get_set)


end
