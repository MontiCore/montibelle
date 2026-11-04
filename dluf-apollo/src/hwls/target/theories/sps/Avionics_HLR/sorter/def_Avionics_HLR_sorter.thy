theory def_Avionics_HLR_sorter
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Avionics_HLR_sorter.def_Avionics_HLR_sorter_Input bundle_Avionics_HLR_sorter.def_Avionics_HLR_sorter_Output sps_Sorter.def_Sorter sps_Avionics_HLR_sorter_InputMap.def_Avionics_HLR_sorter_InputMap sps_Avionics_HLR_sorter_OutputMap.def_Avionics_HLR_sorter_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_Avionics_HLR_sorter_Input.channels\<^sup>\<Omega> \<rightarrow> def_Avionics_HLR_sorter_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_Avionics_HLR_sorter_InputMap.Sps () \<then> def_Sorter.Sps () \<then> def_Avionics_HLR_sorter_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Sorter.Sps () \<Longrightarrow> P (def_Sorter_Input.SB.getter\<cdot>sb) (def_Sorter_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_Avionics_HLR_sorter_Input.SB.getter\<cdot>sb) (def_Avionics_HLR_sorter_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_Avionics_HLR_sorter_InputMap.Sps_def def_Avionics_HLR_sorter_OutputMap.Sps_def
    oo_def def_Avionics_HLR_sorter_InputMap.connector.rep_eq def_Avionics_HLR_sorter_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Sorter_Input.SB.get_set)


end
