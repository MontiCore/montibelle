theory def_System_HLR_dluf_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_System_HLR_dluf.def_System_HLR_dluf_Input bundle_DLUF_HLR1.def_DLUF_HLR1_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern). (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_System_HLR_dluf_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLUF_HLR1_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_DLUF_HLR1_Input.SB.setter oo connector oo def_System_HLR_dluf_Input.SB.getter }"


end
