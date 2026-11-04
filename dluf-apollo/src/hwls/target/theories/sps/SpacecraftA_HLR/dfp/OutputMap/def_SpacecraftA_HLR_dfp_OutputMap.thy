theory def_SpacecraftA_HLR_dfp_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DFP.def_DFP_Output bundle_SpacecraftA_HLR_dfp.def_SpacecraftA_HLR_dfp_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DFP_Output.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_dfp_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_dfp_Output.SB.setter oo connector oo def_DFP_Output.SB.getter }"


end
