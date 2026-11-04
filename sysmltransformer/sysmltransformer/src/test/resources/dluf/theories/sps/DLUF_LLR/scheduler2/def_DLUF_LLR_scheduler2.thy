theory def_DLUF_LLR_scheduler2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLUF_LLR_scheduler2.def_DLUF_LLR_scheduler2_Input bundle_DLUF_LLR_scheduler2.def_DLUF_LLR_scheduler2_Output sps_Scheduler_LLR.def_Scheduler_LLR sps_DLUF_LLR_scheduler2_InputMap.def_DLUF_LLR_scheduler2_InputMap sps_DLUF_LLR_scheduler2_OutputMap.def_DLUF_LLR_scheduler2_OutputMap
    (* Hwl  *)

begin


definition Sps :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (def_DLUF_LLR_scheduler2_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLUF_LLR_scheduler2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4). def_DLUF_LLR_scheduler2_InputMap.Sps () \<then> def_Scheduler_LLR.Sps (var_cap2) \<then> def_DLUF_LLR_scheduler2_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Scheduler_LLR.Sps (var_cap2) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    shows "P (def_DLUF_LLR_scheduler2_Input.SB.getter\<cdot>sb) (def_DLUF_LLR_scheduler2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_DLUF_LLR_scheduler2_InputMap.Sps_def def_DLUF_LLR_scheduler2_OutputMap.Sps_def
    oo_def def_DLUF_LLR_scheduler2_InputMap.connector.rep_eq def_DLUF_LLR_scheduler2_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Scheduler_HLR2_Input.SB.get_set)


end
