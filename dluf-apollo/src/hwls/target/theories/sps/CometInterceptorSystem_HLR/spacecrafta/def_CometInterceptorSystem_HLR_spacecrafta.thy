theory def_CometInterceptorSystem_HLR_spacecrafta
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_HLR_spacecrafta.def_CometInterceptorSystem_HLR_spacecrafta_Input bundle_CometInterceptorSystem_HLR_spacecrafta.def_CometInterceptorSystem_HLR_spacecrafta_Output sps_SpacecraftA_HLR.def_SpacecraftA_HLR sps_CometInterceptorSystem_HLR_spacecrafta_InputMap.def_CometInterceptorSystem_HLR_spacecrafta_InputMap sps_CometInterceptorSystem_HLR_spacecrafta_OutputMap.def_CometInterceptorSystem_HLR_spacecrafta_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_HLR_spacecrafta_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_CometInterceptorSystem_HLR_spacecrafta_InputMap.Sps () \<then> def_SpacecraftA_HLR.Sps () \<then> def_CometInterceptorSystem_HLR_spacecrafta_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_SpacecraftA_HLR.Sps () \<Longrightarrow> P (def_SpacecraftA_HLR_Input.SB.getter\<cdot>sb) (def_SpacecraftA_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_CometInterceptorSystem_HLR_spacecrafta_Input.SB.getter\<cdot>sb) (def_CometInterceptorSystem_HLR_spacecrafta_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_CometInterceptorSystem_HLR_spacecrafta_InputMap.Sps_def def_CometInterceptorSystem_HLR_spacecrafta_OutputMap.Sps_def
    oo_def def_CometInterceptorSystem_HLR_spacecrafta_InputMap.connector.rep_eq def_CometInterceptorSystem_HLR_spacecrafta_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_SpacecraftA_HLR_Input.SB.get_set)


end
