theory def_CometInterceptorSystem_HLR_spacecrafta_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_SpacecraftA_HLR.def_SpacecraftA_HLR_Output bundle_CometInterceptorSystem_HLR_spacecrafta.def_CometInterceptorSystem_HLR_spacecrafta_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream \<times> Packet event stream \<times> Packet event stream) \<rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream)" is
"\<lambda> (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_groundOut_data_pattern). (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_groundOut_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_HLR_Output.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_CometInterceptorSystem_HLR_spacecrafta_Output.SB.setter oo connector oo def_SpacecraftA_HLR_Output.SB.getter }"


end
