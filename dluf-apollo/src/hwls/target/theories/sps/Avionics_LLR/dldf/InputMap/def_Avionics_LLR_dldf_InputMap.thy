theory def_Avionics_LLR_dldf_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Avionics_LLR_dldf.def_Avionics_LLR_dldf_Input bundle_DLDF_HLR1.def_DLDF_HLR1_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern). (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Avionics_LLR_dldf_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLDF_HLR1_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_DLDF_HLR1_Input.SB.setter oo connector oo def_Avionics_LLR_dldf_Input.SB.getter }"


end
