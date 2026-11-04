theory def_SpacecraftA_LLR_mirmis
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_mirmis.def_SpacecraftA_LLR_mirmis_Input bundle_SpacecraftA_LLR_mirmis.def_SpacecraftA_LLR_mirmis_Output sps_MIRMIS.def_MIRMIS sps_SpacecraftA_LLR_mirmis_InputMap.def_SpacecraftA_LLR_mirmis_InputMap sps_SpacecraftA_LLR_mirmis_OutputMap.def_SpacecraftA_LLR_mirmis_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_mirmis_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_mirmis_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SpacecraftA_LLR_mirmis_InputMap.Sps () \<then> def_MIRMIS.Sps () \<then> def_SpacecraftA_LLR_mirmis_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_MIRMIS.Sps () \<Longrightarrow> P (def_MIRMIS_Input.SB.getter\<cdot>sb) (def_MIRMIS_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SpacecraftA_LLR_mirmis_Input.SB.getter\<cdot>sb) (def_SpacecraftA_LLR_mirmis_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SpacecraftA_LLR_mirmis_InputMap.Sps_def def_SpacecraftA_LLR_mirmis_OutputMap.Sps_def
    oo_def def_SpacecraftA_LLR_mirmis_InputMap.connector.rep_eq def_SpacecraftA_LLR_mirmis_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_MIRMIS_Input.SB.get_set)


end
