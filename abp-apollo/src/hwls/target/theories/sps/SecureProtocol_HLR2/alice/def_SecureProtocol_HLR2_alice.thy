theory def_SecureProtocol_HLR2_alice
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SecureProtocol_HLR2_alice.def_SecureProtocol_HLR2_alice_Input bundle_SecureProtocol_HLR2_alice.def_SecureProtocol_HLR2_alice_Output sps_Alice_HLR.def_Alice_HLR sps_SecureProtocol_HLR2_alice_InputMap.def_SecureProtocol_HLR2_alice_InputMap sps_SecureProtocol_HLR2_alice_OutputMap.def_SecureProtocol_HLR2_alice_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR2_alice_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR2_alice_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SecureProtocol_HLR2_alice_InputMap.Sps () \<then> def_Alice_HLR.Sps () \<then> def_SecureProtocol_HLR2_alice_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Alice_HLR.Sps () \<Longrightarrow> P (def_Alice_HLR_Input.SB.getter\<cdot>sb) (def_Alice_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SecureProtocol_HLR2_alice_Input.SB.getter\<cdot>sb) (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SecureProtocol_HLR2_alice_InputMap.Sps_def def_SecureProtocol_HLR2_alice_OutputMap.Sps_def
    oo_def def_SecureProtocol_HLR2_alice_InputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Alice_HLR_Input.SB.get_set)


end
