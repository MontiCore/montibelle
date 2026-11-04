theory def_SpacecraftA_HLR_tele_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_TelecommandAndTelemetry_HLR.def_TelecommandAndTelemetry_HLR_Output bundle_SpacecraftA_HLR_tele.def_SpacecraftA_HLR_tele_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern). (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_TelecommandAndTelemetry_HLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_tele_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_tele_Output.SB.setter oo connector oo def_TelecommandAndTelemetry_HLR_Output.SB.getter }"


end
