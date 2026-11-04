theory def_TelecommandAndTelemetry_HLR_router_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Router.def_Router_Output bundle_TelecommandAndTelemetry_HLR_router.def_TelecommandAndTelemetry_HLR_router_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern). (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Router_Output.channels\<^sup>\<Omega> \<rightarrow> def_TelecommandAndTelemetry_HLR_router_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_TelecommandAndTelemetry_HLR_router_Output.SB.setter oo connector oo def_Router_Output.SB.getter }"


end
