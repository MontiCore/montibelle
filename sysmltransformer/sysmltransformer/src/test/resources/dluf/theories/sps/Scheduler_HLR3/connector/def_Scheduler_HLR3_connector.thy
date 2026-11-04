theory def_Scheduler_HLR3_connector
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_HLR3_connector.def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input bundle_Scheduler_HLR3_connector.def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (CtrlEnum event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_buffer_output_data_pattern, channel_capacityComponent_control_data_pattern, channel_capacityComponent_output_data_pattern, channel_input_data_pattern). (channel_capacityComponent_control_data_pattern, channel_input_data_pattern, channel_buffer_output_data_pattern, channel_capacityComponent_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Output.SB.setter oo connector oo def_Scheduler_HLR3_connector_Scheduler_HLR3_connector_Input.SB.getter }"


end
