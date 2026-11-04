theory def_SpacecraftA_HLR_tele_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_HLR_tele.def_SpacecraftA_HLR_tele_Input bundle_TelecommandAndTelemetry_HLR.def_TelecommandAndTelemetry_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern). (channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_HLR_tele_Input.channels\<^sup>\<Omega> \<rightarrow> def_TelecommandAndTelemetry_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_TelecommandAndTelemetry_HLR_Input.SB.setter oo connector oo def_SpacecraftA_HLR_tele_Input.SB.getter }"


end
