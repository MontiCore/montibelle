theory def_Scheduler_HLR3_buffer
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_HLR3_buffer.def_Scheduler_HLR3_buffer_Input bundle_Scheduler_HLR3_buffer.def_Scheduler_HLR3_buffer_Output sps_Buffer_HLR3.def_Buffer_HLR3 sps_Scheduler_HLR3_buffer_InputMap.def_Scheduler_HLR3_buffer_InputMap sps_Scheduler_HLR3_buffer_OutputMap.def_Scheduler_HLR3_buffer_OutputMap
    (* Hwl  *)

begin


definition Sps :: "(nat) \<Rightarrow> (def_Scheduler_HLR3_buffer_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR3_buffer_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_capacity). def_Scheduler_HLR3_buffer_InputMap.Sps () \<then> def_Buffer_HLR3.Sps () \<then> def_Scheduler_HLR3_buffer_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Buffer_HLR3.Sps () \<Longrightarrow> P (def_Buffer_HLR3_Input.SB.getter\<cdot>sb) (def_Buffer_HLR3_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps (var_capacity)"
    shows "P (def_Scheduler_HLR3_buffer_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR3_buffer_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_Scheduler_HLR3_buffer_InputMap.Sps_def def_Scheduler_HLR3_buffer_OutputMap.Sps_def
    oo_def def_Scheduler_HLR3_buffer_InputMap.connector.rep_eq def_Scheduler_HLR3_buffer_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Buffer_HLR3_Input.SB.get_set)


end
