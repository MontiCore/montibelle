theory def_SpacecraftA_LLR_tele
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_tele.def_SpacecraftA_LLR_tele_Input bundle_SpacecraftA_LLR_tele.def_SpacecraftA_LLR_tele_Output sps_TelecommandAndTelemetry_LLR.def_TelecommandAndTelemetry_LLR sps_SpacecraftA_LLR_tele_InputMap.def_SpacecraftA_LLR_tele_InputMap sps_SpacecraftA_LLR_tele_OutputMap.def_SpacecraftA_LLR_tele_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_tele_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_tele_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_SpacecraftA_LLR_tele_InputMap.Sps () \<then> def_TelecommandAndTelemetry_LLR.Sps () \<then> def_SpacecraftA_LLR_tele_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_TelecommandAndTelemetry_LLR.Sps () \<Longrightarrow> P (def_TelecommandAndTelemetry_HLR_Input.SB.getter\<cdot>sb) (def_TelecommandAndTelemetry_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_SpacecraftA_LLR_tele_Input.SB.getter\<cdot>sb) (def_SpacecraftA_LLR_tele_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_SpacecraftA_LLR_tele_InputMap.Sps_def def_SpacecraftA_LLR_tele_OutputMap.Sps_def
    oo_def def_SpacecraftA_LLR_tele_InputMap.connector.rep_eq def_SpacecraftA_LLR_tele_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_TelecommandAndTelemetry_HLR_Input.SB.get_set)


end
