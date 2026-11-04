theory def_CometInterceptorSystem_LLR_b1
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_LLR_b1.def_CometInterceptorSystem_LLR_b1_Input bundle_CometInterceptorSystem_LLR_b1.def_CometInterceptorSystem_LLR_b1_Output sps_ProbeB1.def_ProbeB1 sps_CometInterceptorSystem_LLR_b1_InputMap.def_CometInterceptorSystem_LLR_b1_InputMap sps_CometInterceptorSystem_LLR_b1_OutputMap.def_CometInterceptorSystem_LLR_b1_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_LLR_b1_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_LLR_b1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_CometInterceptorSystem_LLR_b1_InputMap.Sps () \<then> def_ProbeB1.Sps () \<then> def_CometInterceptorSystem_LLR_b1_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_ProbeB1.Sps () \<Longrightarrow> P (def_ProbeB1_Input.SB.getter\<cdot>sb) (def_ProbeB1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_CometInterceptorSystem_LLR_b1_Input.SB.getter\<cdot>sb) (def_CometInterceptorSystem_LLR_b1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_CometInterceptorSystem_LLR_b1_InputMap.Sps_def def_CometInterceptorSystem_LLR_b1_OutputMap.Sps_def
    oo_def def_CometInterceptorSystem_LLR_b1_InputMap.connector.rep_eq def_CometInterceptorSystem_LLR_b1_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_ProbeB1_Input.SB.get_set)


end
