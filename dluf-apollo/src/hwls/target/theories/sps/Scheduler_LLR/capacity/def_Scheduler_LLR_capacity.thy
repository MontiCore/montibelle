theory def_Scheduler_LLR_capacity
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_LLR_capacity.def_Scheduler_LLR_capacity_Input bundle_Scheduler_LLR_capacity.def_Scheduler_LLR_capacity_Output sps_Capacity_LLR.def_Capacity_LLR sps_Scheduler_LLR_capacity_InputMap.def_Scheduler_LLR_capacity_InputMap sps_Scheduler_LLR_capacity_OutputMap.def_Scheduler_LLR_capacity_OutputMap
    (* Hwl  *)

begin


definition Sps :: "(nat) \<Rightarrow> (def_Scheduler_LLR_capacity_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_LLR_capacity_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_capacity). def_Scheduler_LLR_capacity_InputMap.Sps () \<then> def_Capacity_LLR.Sps (var_capacity) \<then> def_Scheduler_LLR_capacity_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Capacity_LLR.Sps (var_capacity) \<Longrightarrow> P (def_Capacity_HLR3_Input.SB.getter\<cdot>sb) (def_Capacity_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps (var_capacity)"
    shows "P (def_Scheduler_LLR_capacity_Input.SB.getter\<cdot>sb) (def_Scheduler_LLR_capacity_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_Scheduler_LLR_capacity_InputMap.Sps_def def_Scheduler_LLR_capacity_OutputMap.Sps_def
    oo_def def_Scheduler_LLR_capacity_InputMap.connector.rep_eq def_Scheduler_LLR_capacity_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Capacity_HLR3_Input.SB.get_set)


end
