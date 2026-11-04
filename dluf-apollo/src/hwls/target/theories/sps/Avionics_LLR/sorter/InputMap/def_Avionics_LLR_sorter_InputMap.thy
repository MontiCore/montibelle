theory def_Avionics_LLR_sorter_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Avionics_LLR_sorter.def_Avionics_LLR_sorter_Input bundle_Sorter.def_Sorter_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern). (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Avionics_LLR_sorter_Input.channels\<^sup>\<Omega> \<rightarrow> def_Sorter_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Sorter_Input.SB.setter oo connector oo def_Avionics_LLR_sorter_Input.SB.getter }"


end
