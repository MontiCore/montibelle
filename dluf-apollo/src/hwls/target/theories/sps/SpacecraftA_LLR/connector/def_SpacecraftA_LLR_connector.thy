theory def_SpacecraftA_LLR_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_connector.def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input bundle_SpacecraftA_LLR_connector.def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern). (channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern, channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.SB.setter oo connector oo def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.SB.getter }"


end
