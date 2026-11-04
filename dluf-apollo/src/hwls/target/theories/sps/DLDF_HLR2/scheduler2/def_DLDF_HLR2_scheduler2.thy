theory def_DLDF_HLR2_scheduler2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLDF_HLR2_scheduler2.def_DLDF_HLR2_scheduler2_Input bundle_DLDF_HLR2_scheduler2.def_DLDF_HLR2_scheduler2_Output sps_Scheduler_HLR2.def_Scheduler_HLR2 sps_DLDF_HLR2_scheduler2_InputMap.def_DLDF_HLR2_scheduler2_InputMap sps_DLDF_HLR2_scheduler2_OutputMap.def_DLDF_HLR2_scheduler2_OutputMap
    (* Hwl  *)

begin


definition Sps :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (def_DLDF_HLR2_scheduler2_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLDF_HLR2_scheduler2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4). def_DLDF_HLR2_scheduler2_InputMap.Sps () \<then> def_Scheduler_HLR2.Sps (var_cap2) \<then> def_DLDF_HLR2_scheduler2_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Scheduler_HLR2.Sps (var_cap2) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
    shows "P (def_DLDF_HLR2_scheduler2_Input.SB.getter\<cdot>sb) (def_DLDF_HLR2_scheduler2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_DLDF_HLR2_scheduler2_InputMap.Sps_def def_DLDF_HLR2_scheduler2_OutputMap.Sps_def
    oo_def def_DLDF_HLR2_scheduler2_InputMap.connector.rep_eq def_DLDF_HLR2_scheduler2_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Scheduler_HLR2_Input.SB.get_set)


end
