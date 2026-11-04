theory def_SpacecraftA_HLR_mirmis_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_MIRMIS.def_MIRMIS_Output bundle_SpacecraftA_HLR_mirmis.def_SpacecraftA_HLR_mirmis_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_MIRMIS_Output.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_mirmis_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_mirmis_Output.SB.setter oo connector oo def_MIRMIS_Output.SB.getter }"


end
