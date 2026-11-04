theory def_TelecommandAndTelemetry_HLR_router
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_TelecommandAndTelemetry_HLR_router.def_TelecommandAndTelemetry_HLR_router_Input bundle_TelecommandAndTelemetry_HLR_router.def_TelecommandAndTelemetry_HLR_router_Output sps_Router.def_Router sps_TelecommandAndTelemetry_HLR_router_InputMap.def_TelecommandAndTelemetry_HLR_router_InputMap sps_TelecommandAndTelemetry_HLR_router_OutputMap.def_TelecommandAndTelemetry_HLR_router_OutputMap
    (* Hwl  *)

begin


definition Sps :: "unit \<Rightarrow> (def_TelecommandAndTelemetry_HLR_router_Input.channels\<^sup>\<Omega> \<rightarrow> def_TelecommandAndTelemetry_HLR_router_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). def_TelecommandAndTelemetry_HLR_router_InputMap.Sps () \<then> def_Router.Sps () \<then> def_TelecommandAndTelemetry_HLR_router_OutputMap.Sps ()"

lemma pred_inst2def:
  assumes "\<And>spf sb. spf \<in> def_Router.Sps () \<Longrightarrow> P (def_Router_Input.SB.getter\<cdot>sb) (def_Router_Output.SB.getter\<cdot>(spf\<cdot>sb))"
      and "spf \<in> Sps ()"
    shows "P (def_TelecommandAndTelemetry_HLR_router_Input.SB.getter\<cdot>sb) (def_TelecommandAndTelemetry_HLR_router_Output.SB.getter\<cdot>(spf\<cdot>sb))"
  apply(insert assms(2), auto simp add: Sps_def def_TelecommandAndTelemetry_HLR_router_InputMap.Sps_def def_TelecommandAndTelemetry_HLR_router_OutputMap.Sps_def
    oo_def def_TelecommandAndTelemetry_HLR_router_InputMap.connector.rep_eq def_TelecommandAndTelemetry_HLR_router_OutputMap.connector.rep_eq seqcomp_insert)
  using assms(1) by (metis def_Router_Input.SB.get_set)


end
