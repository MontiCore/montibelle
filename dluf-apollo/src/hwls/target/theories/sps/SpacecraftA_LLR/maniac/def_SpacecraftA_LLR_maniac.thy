theory def_SpacecraftA_LLR_maniac
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_maniac.def_SpacecraftA_LLR_maniac_Input bundle_SpacecraftA_LLR_maniac.def_SpacecraftA_LLR_maniac_Output sps_MANiaC.def_MANiaC sps_SpacecraftA_LLR_maniac_InputMap.def_SpacecraftA_LLR_maniac_InputMap sps_SpacecraftA_LLR_maniac_OutputMap.def_SpacecraftA_LLR_maniac_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_maniac_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_maniac_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SpacecraftA_LLR_maniac_InputMap.Sps () \<then> def_MANiaC.Sps () \<then> def_SpacecraftA_LLR_maniac_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_MANiaC.Sps () \<Longrightarrow> P (def_MANiaC_Input.SB.getter\<cdot>sb) (def_MANiaC_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SpacecraftA_LLR_maniac_Input.SB.getter\<cdot>sb) (def_SpacecraftA_LLR_maniac_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SpacecraftA_LLR_maniac_InputMap.Sps_def def_SpacecraftA_LLR_maniac_OutputMap.Sps_def
    oo_def def_SpacecraftA_LLR_maniac_InputMap.connector.rep_eq def_SpacecraftA_LLR_maniac_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_MANiaC_Input.SB.get_set)


end
