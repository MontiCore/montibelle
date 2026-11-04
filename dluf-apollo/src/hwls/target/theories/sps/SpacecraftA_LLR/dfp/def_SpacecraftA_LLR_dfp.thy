theory def_SpacecraftA_LLR_dfp
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_dfp.def_SpacecraftA_LLR_dfp_Input bundle_SpacecraftA_LLR_dfp.def_SpacecraftA_LLR_dfp_Output sps_DFP.def_DFP sps_SpacecraftA_LLR_dfp_InputMap.def_SpacecraftA_LLR_dfp_InputMap sps_SpacecraftA_LLR_dfp_OutputMap.def_SpacecraftA_LLR_dfp_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_dfp_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_dfp_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SpacecraftA_LLR_dfp_InputMap.Sps () \<then> def_DFP.Sps () \<then> def_SpacecraftA_LLR_dfp_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_DFP.Sps () \<Longrightarrow> P (def_DFP_Input.SB.getter\<cdot>sb) (def_DFP_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SpacecraftA_LLR_dfp_Input.SB.getter\<cdot>sb) (def_SpacecraftA_LLR_dfp_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SpacecraftA_LLR_dfp_InputMap.Sps_def def_SpacecraftA_LLR_dfp_OutputMap.Sps_def
    oo_def def_SpacecraftA_LLR_dfp_InputMap.connector.rep_eq def_SpacecraftA_LLR_dfp_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_DFP_Input.SB.get_set)


end
