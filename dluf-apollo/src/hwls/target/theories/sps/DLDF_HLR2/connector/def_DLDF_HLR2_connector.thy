theory def_DLDF_HLR2_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLDF_HLR2_connector.def_DLDF_HLR2_connector_DLDF_HLR2_connector_Input bundle_DLDF_HLR2_connector.def_DLDF_HLR2_connector_DLDF_HLR2_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern). (channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern, channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DLDF_HLR2_connector_DLDF_HLR2_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLDF_HLR2_connector_DLDF_HLR2_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_DLDF_HLR2_connector_DLDF_HLR2_connector_Output.SB.setter oo connector oo def_DLDF_HLR2_connector_DLDF_HLR2_connector_Input.SB.getter }"


end
