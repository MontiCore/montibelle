theory def_SpacecraftA_LLR_coca_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_coca.def_SpacecraftA_LLR_coca_Input bundle_CometCamera.def_CometCamera_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_coca_input_data_pattern). (channel_coca_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_coca_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometCamera_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_CometCamera_Input.SB.setter oo connector oo def_SpacecraftA_LLR_coca_Input.SB.getter }"


end
