theory def_System_LLR_dluf_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLUF_HLR1.def_DLUF_HLR1_Output bundle_System_LLR_dluf.def_System_LLR_dluf_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern). (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DLUF_HLR1_Output.channels\<^sup>\<Omega> \<rightarrow> def_System_LLR_dluf_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_System_LLR_dluf_Output.SB.setter oo connector oo def_DLUF_HLR1_Output.SB.getter }"


end
