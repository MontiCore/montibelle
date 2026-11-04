theory def_CometInterceptorSystem_HLR_spacecrafta_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_HLR_spacecrafta.def_CometInterceptorSystem_HLR_spacecrafta_Input bundle_SpacecraftA_HLR.def_SpacecraftA_HLR_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern). (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_HLR_spacecrafta_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_SpacecraftA_HLR_Input.SB.setter oo connector oo def_CometInterceptorSystem_HLR_spacecrafta_Input.SB.getter }"


end
