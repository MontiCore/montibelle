theory def_Scheduler_LLR_capacityComponent
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_LLR_capacityComponent.def_Scheduler_LLR_capacityComponent_Input bundle_Scheduler_LLR_capacityComponent.def_Scheduler_LLR_capacityComponent_Output sps_Capacity_LLR.def_Capacity_LLR sps_Scheduler_LLR_capacityComponent_InputMap.def_Scheduler_LLR_capacityComponent_InputMap sps_Scheduler_LLR_capacityComponent_OutputMap.def_Scheduler_LLR_capacityComponent_OutputMap
    (* Hwl  *)

begin


definition Sps :: "(nat) \<Rightarrow> (def_Scheduler_LLR_capacityComponent_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_LLR_capacityComponent_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_capacity). def_Scheduler_LLR_capacityComponent_InputMap.Sps () \<then> def_Capacity_LLR.Sps (var_capacity) \<then> def_Scheduler_LLR_capacityComponent_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Capacity_LLR.Sps (var_capacity) \<Longrightarrow> P (def_Capacity_HLR3_Input.SB.getter\<cdot>sb) (def_Capacity_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps (var_capacity)"
    shows "P (def_Scheduler_LLR_capacityComponent_Input.SB.getter\<cdot>sb) (def_Scheduler_LLR_capacityComponent_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_Scheduler_LLR_capacityComponent_InputMap.Sps_def def_Scheduler_LLR_capacityComponent_OutputMap.Sps_def
    oo_def def_Scheduler_LLR_capacityComponent_InputMap.connector.rep_eq def_Scheduler_LLR_capacityComponent_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Capacity_HLR3_Input.SB.get_set)


end
