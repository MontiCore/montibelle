theory def_SpacecraftA_LLR_maniac_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_LLR_maniac.def_SpacecraftA_LLR_maniac_Input bundle_MANiaC.def_MANiaC_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_maniac_input_data_pattern). (channel_maniac_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_LLR_maniac_Input.channels\<^sup>\<Omega> \<rightarrow> def_MANiaC_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_MANiaC_Input.SB.setter oo connector oo def_SpacecraftA_LLR_maniac_Input.SB.getter }"


end
