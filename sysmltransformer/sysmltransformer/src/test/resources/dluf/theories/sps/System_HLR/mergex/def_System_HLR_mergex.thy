theory def_System_HLR_mergex
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_System_HLR_mergex.def_System_HLR_mergex_Input bundle_System_HLR_mergex.def_System_HLR_mergex_Output sps_Merge_LLR.def_Merge_LLR sps_System_HLR_mergex_InputMap.def_System_HLR_mergex_InputMap sps_System_HLR_mergex_OutputMap.def_System_HLR_mergex_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_System_HLR_mergex_Input.channels\<^sup>\<Omega> \<rightarrow> def_System_HLR_mergex_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_System_HLR_mergex_InputMap.Sps () \<then> def_Merge_LLR.Sps () \<then> def_System_HLR_mergex_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Merge_LLR.Sps () \<Longrightarrow> P (def_Merge_LLR_Input.SB.getter\<cdot>sb) (def_Merge_LLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_System_HLR_mergex_Input.SB.getter\<cdot>sb) (def_System_HLR_mergex_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_System_HLR_mergex_InputMap.Sps_def def_System_HLR_mergex_OutputMap.Sps_def
    oo_def def_System_HLR_mergex_InputMap.connector.rep_eq def_System_HLR_mergex_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Merge_LLR_Input.SB.get_set)


end
