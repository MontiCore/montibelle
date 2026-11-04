theory def_CometInterceptorSystem_HLR_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_HLR_connector.def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input bundle_CometInterceptorSystem_HLR_connector.def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern). (channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.SB.setter oo connector oo def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.SB.getter }"


end
