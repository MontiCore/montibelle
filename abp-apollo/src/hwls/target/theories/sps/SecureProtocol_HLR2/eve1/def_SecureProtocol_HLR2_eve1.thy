theory def_SecureProtocol_HLR2_eve1
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_eve1.def_SecureProtocol_HLR2_eve1_Input bundle_SecureProtocol_HLR2_eve1.def_SecureProtocol_HLR2_eve1_Output sps_Eve1_HLR.def_Eve1_HLR sps_SecureProtocol_HLR2_eve1_InputMap.def_SecureProtocol_HLR2_eve1_InputMap sps_SecureProtocol_HLR2_eve1_OutputMap.def_SecureProtocol_HLR2_eve1_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_eve1_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR2_eve1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SecureProtocol_HLR2_eve1_InputMap.Sps () \<then> def_Eve1_HLR.Sps () \<then> def_SecureProtocol_HLR2_eve1_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Eve1_HLR.Sps () \<Longrightarrow> P (def_Eve1_HLR_Input.SB.getter\<cdot>sb) (def_Eve1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SecureProtocol_HLR2_eve1_Input.SB.getter\<cdot>sb) (def_SecureProtocol_HLR2_eve1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SecureProtocol_HLR2_eve1_InputMap.Sps_def def_SecureProtocol_HLR2_eve1_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Eve1_HLR_Input.SB.get_set)


end
