theory def_SpacecraftA_HLR_dfp_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_HLR_dfp.def_SpacecraftA_HLR_dfp_Input bundle_DFP.def_DFP_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_dfp_input_data_pattern). (channel_dfp_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_HLR_dfp_Input.channels\<^sup>\<Omega> \<rightarrow> def_DFP_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_DFP_Input.SB.setter oo connector oo def_SpacecraftA_HLR_dfp_Input.SB.getter }"


end
