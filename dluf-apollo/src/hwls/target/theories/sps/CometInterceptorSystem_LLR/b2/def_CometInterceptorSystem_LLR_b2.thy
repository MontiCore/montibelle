theory def_CometInterceptorSystem_LLR_b2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_LLR_b2.def_CometInterceptorSystem_LLR_b2_Input bundle_CometInterceptorSystem_LLR_b2.def_CometInterceptorSystem_LLR_b2_Output sps_ProbeB2.def_ProbeB2 sps_CometInterceptorSystem_LLR_b2_InputMap.def_CometInterceptorSystem_LLR_b2_InputMap sps_CometInterceptorSystem_LLR_b2_OutputMap.def_CometInterceptorSystem_LLR_b2_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_LLR_b2_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_LLR_b2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_CometInterceptorSystem_LLR_b2_InputMap.Sps () \<then> def_ProbeB2.Sps () \<then> def_CometInterceptorSystem_LLR_b2_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_ProbeB2.Sps () \<Longrightarrow> P (def_ProbeB2_Input.SB.getter\<cdot>sb) (def_ProbeB2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_CometInterceptorSystem_LLR_b2_Input.SB.getter\<cdot>sb) (def_CometInterceptorSystem_LLR_b2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_CometInterceptorSystem_LLR_b2_InputMap.Sps_def def_CometInterceptorSystem_LLR_b2_OutputMap.Sps_def
    oo_def def_CometInterceptorSystem_LLR_b2_InputMap.connector.rep_eq def_CometInterceptorSystem_LLR_b2_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_ProbeB2_Input.SB.get_set)


end
