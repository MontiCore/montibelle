theory def_System_HLR_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_System_HLR_connector.def_System_HLR_connector_System_HLR_connector_Input bundle_System_HLR_connector.def_System_HLR_connector_System_HLR_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern). (channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern, channel_mergex_output_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_System_HLR_connector_System_HLR_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_System_HLR_connector_System_HLR_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_System_HLR_connector_System_HLR_connector_Output.SB.setter oo connector oo def_System_HLR_connector_System_HLR_connector_Input.SB.getter }"


end
