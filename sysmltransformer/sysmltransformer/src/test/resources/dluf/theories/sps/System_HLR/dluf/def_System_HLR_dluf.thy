theory def_System_HLR_dluf
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_System_HLR_dluf.def_System_HLR_dluf_Input bundle_System_HLR_dluf.def_System_HLR_dluf_Output sps_DLUF_HLR1.def_DLUF_HLR1 sps_System_HLR_dluf_InputMap.def_System_HLR_dluf_InputMap sps_System_HLR_dluf_OutputMap.def_System_HLR_dluf_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_System_HLR_dluf_Input.channels\<^sup>\<Omega> \<rightarrow> def_System_HLR_dluf_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_System_HLR_dluf_InputMap.Sps () \<then> def_DLUF_HLR1.Sps (400, 300, 200, 100) \<then> def_System_HLR_dluf_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_DLUF_HLR1.Sps (400, 300, 200, 100) \<Longrightarrow> P (def_DLUF_HLR1_Input.SB.getter\<cdot>sb) (def_DLUF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_System_HLR_dluf_Input.SB.getter\<cdot>sb) (def_System_HLR_dluf_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_System_HLR_dluf_InputMap.Sps_def def_System_HLR_dluf_OutputMap.Sps_def
    oo_def def_System_HLR_dluf_InputMap.connector.rep_eq def_System_HLR_dluf_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_DLUF_HLR1_Input.SB.get_set)


end
