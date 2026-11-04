theory def_SecureProtocol_HLR2_decrypt2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_decrypt2.def_SecureProtocol_HLR2_decrypt2_Input bundle_SecureProtocol_HLR2_decrypt2.def_SecureProtocol_HLR2_decrypt2_Output sps_Decrypt2_HLR.def_Decrypt2_HLR sps_SecureProtocol_HLR2_decrypt2_InputMap.def_SecureProtocol_HLR2_decrypt2_InputMap sps_SecureProtocol_HLR2_decrypt2_OutputMap.def_SecureProtocol_HLR2_decrypt2_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_decrypt2_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR2_decrypt2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SecureProtocol_HLR2_decrypt2_InputMap.Sps () \<then> def_Decrypt2_HLR.Sps () \<then> def_SecureProtocol_HLR2_decrypt2_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Decrypt2_HLR.Sps () \<Longrightarrow> P (def_Decrypt2_HLR_Input.SB.getter\<cdot>sb) (def_Decrypt2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SecureProtocol_HLR2_decrypt2_Input.SB.getter\<cdot>sb) (def_SecureProtocol_HLR2_decrypt2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SecureProtocol_HLR2_decrypt2_InputMap.Sps_def def_SecureProtocol_HLR2_decrypt2_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_decrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Decrypt2_HLR_Input.SB.get_set)


end
