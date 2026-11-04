theory def_Avionics_HLR_mergex_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Avionics_HLR_mergex.def_Avionics_HLR_mergex_Input bundle_Merge_LLR.def_Merge_LLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern). (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Avionics_HLR_mergex_Input.channels\<^sup>\<Omega> \<rightarrow> def_Merge_LLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Merge_LLR_Input.SB.setter oo connector oo def_Avionics_HLR_mergex_Input.SB.getter }"


end
