theory def_Avionics_HLR_dldf_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLDF_HLR1.def_DLDF_HLR1_Output bundle_Avionics_HLR_dldf.def_Avionics_HLR_dldf_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern). (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DLDF_HLR1_Output.channels\<^sup>\<Omega> \<rightarrow> def_Avionics_HLR_dldf_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Avionics_HLR_dldf_Output.SB.setter oo connector oo def_DLDF_HLR1_Output.SB.getter }"


end
