theory def_SpacecraftA_HLR_mirmis_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_HLR_mirmis.def_SpacecraftA_HLR_mirmis_Input bundle_MIRMIS.def_MIRMIS_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_mirmis_input_data_pattern). (channel_mirmis_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_HLR_mirmis_Input.channels\<^sup>\<Omega> \<rightarrow> def_MIRMIS_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_MIRMIS_Input.SB.setter oo connector oo def_SpacecraftA_HLR_mirmis_Input.SB.getter }"


end
