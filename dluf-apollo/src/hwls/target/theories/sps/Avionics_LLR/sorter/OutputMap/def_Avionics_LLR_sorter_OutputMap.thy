theory def_Avionics_LLR_sorter_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Sorter.def_Sorter_Output bundle_Avionics_LLR_sorter.def_Avionics_LLR_sorter_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_prio1_data_pattern, channel_prio2_data_pattern, channel_prio3_data_pattern, channel_prio4_data_pattern). (channel_prio1_data_pattern, channel_prio2_data_pattern, channel_prio3_data_pattern, channel_prio4_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Sorter_Output.channels\<^sup>\<Omega> \<rightarrow> def_Avionics_LLR_sorter_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Avionics_LLR_sorter_Output.SB.setter oo connector oo def_Sorter_Output.SB.getter }"


end
