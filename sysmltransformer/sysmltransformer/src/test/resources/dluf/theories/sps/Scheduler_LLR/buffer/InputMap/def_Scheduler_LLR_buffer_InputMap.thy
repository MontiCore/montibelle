theory def_Scheduler_LLR_buffer_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_LLR_buffer.def_Scheduler_LLR_buffer_Input bundle_Buffer_HLR3.def_Buffer_HLR3_Input
    (* Hwl  *)

begin


lift_definition connector :: "(CtrlEnum event stream \<times> Packet event stream) \<rightarrow> (CtrlEnum event stream \<times> Packet event stream)" is
"\<lambda> (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern). (channel_buffer_control_data_pattern, channel_buffer_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Scheduler_LLR_buffer_Input.channels\<^sup>\<Omega> \<rightarrow> def_Buffer_HLR3_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Buffer_HLR3_Input.SB.setter oo connector oo def_Scheduler_LLR_buffer_Input.SB.getter }"


end
