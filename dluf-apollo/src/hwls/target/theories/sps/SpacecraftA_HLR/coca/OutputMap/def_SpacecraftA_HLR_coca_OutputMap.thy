theory def_SpacecraftA_HLR_coca_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometCamera.def_CometCamera_Output bundle_SpacecraftA_HLR_coca.def_SpacecraftA_HLR_coca_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_CometCamera_Output.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_coca_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_coca_Output.SB.setter oo connector oo def_CometCamera_Output.SB.getter }"


end
