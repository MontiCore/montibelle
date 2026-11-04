theory def_SpacecraftA_HLR_maniac_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_MANiaC.def_MANiaC_Output bundle_SpacecraftA_HLR_maniac.def_SpacecraftA_HLR_maniac_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_MANiaC_Output.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_maniac_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_maniac_Output.SB.setter oo connector oo def_MANiaC_Output.SB.getter }"


end
