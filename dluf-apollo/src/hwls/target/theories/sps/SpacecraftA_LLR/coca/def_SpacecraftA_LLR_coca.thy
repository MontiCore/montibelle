theory def_SpacecraftA_LLR_coca
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_coca.def_SpacecraftA_LLR_coca_Input bundle_SpacecraftA_LLR_coca.def_SpacecraftA_LLR_coca_Output sps_CometCamera.def_CometCamera sps_SpacecraftA_LLR_coca_InputMap.def_SpacecraftA_LLR_coca_InputMap sps_SpacecraftA_LLR_coca_OutputMap.def_SpacecraftA_LLR_coca_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_coca_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_coca_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SpacecraftA_LLR_coca_InputMap.Sps () \<then> def_CometCamera.Sps () \<then> def_SpacecraftA_LLR_coca_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_CometCamera.Sps () \<Longrightarrow> P (def_CometCamera_Input.SB.getter\<cdot>sb) (def_CometCamera_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SpacecraftA_LLR_coca_Input.SB.getter\<cdot>sb) (def_SpacecraftA_LLR_coca_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SpacecraftA_LLR_coca_InputMap.Sps_def def_SpacecraftA_LLR_coca_OutputMap.Sps_def
    oo_def def_SpacecraftA_LLR_coca_InputMap.connector.rep_eq def_SpacecraftA_LLR_coca_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_CometCamera_Input.SB.get_set)


end
