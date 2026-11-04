theory def_Avionics_LLR_mergex_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Merge_LLR.def_Merge_LLR_Output bundle_Avionics_LLR_mergex.def_Avionics_LLR_mergex_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Merge_LLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_Avionics_LLR_mergex_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Avionics_LLR_mergex_Output.SB.setter oo connector oo def_Merge_LLR_Output.SB.getter }"


end
