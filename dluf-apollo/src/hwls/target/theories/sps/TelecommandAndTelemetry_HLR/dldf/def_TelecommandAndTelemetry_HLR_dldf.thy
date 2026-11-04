theory def_TelecommandAndTelemetry_HLR_dldf
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_TelecommandAndTelemetry_HLR_dldf.def_TelecommandAndTelemetry_HLR_dldf_Input bundle_TelecommandAndTelemetry_HLR_dldf.def_TelecommandAndTelemetry_HLR_dldf_Output sps_DLDF_HLR1.def_DLDF_HLR1 sps_TelecommandAndTelemetry_HLR_dldf_InputMap.def_TelecommandAndTelemetry_HLR_dldf_InputMap sps_TelecommandAndTelemetry_HLR_dldf_OutputMap.def_TelecommandAndTelemetry_HLR_dldf_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_TelecommandAndTelemetry_HLR_dldf_Input.channels\<^sup>\<Omega> \<rightarrow> def_TelecommandAndTelemetry_HLR_dldf_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_TelecommandAndTelemetry_HLR_dldf_InputMap.Sps () \<then> def_DLDF_HLR1.Sps (400, 300, 200, 100) \<then> def_TelecommandAndTelemetry_HLR_dldf_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_DLDF_HLR1.Sps (400, 300, 200, 100) \<Longrightarrow> P (def_DLDF_HLR1_Input.SB.getter\<cdot>sb) (def_DLDF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_TelecommandAndTelemetry_HLR_dldf_Input.SB.getter\<cdot>sb) (def_TelecommandAndTelemetry_HLR_dldf_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_TelecommandAndTelemetry_HLR_dldf_InputMap.Sps_def def_TelecommandAndTelemetry_HLR_dldf_OutputMap.Sps_def
    oo_def def_TelecommandAndTelemetry_HLR_dldf_InputMap.connector.rep_eq def_TelecommandAndTelemetry_HLR_dldf_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_DLDF_HLR1_Input.SB.get_set)


end
