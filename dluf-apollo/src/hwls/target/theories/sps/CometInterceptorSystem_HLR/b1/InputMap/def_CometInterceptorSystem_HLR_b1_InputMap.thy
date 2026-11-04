theory def_CometInterceptorSystem_HLR_b1_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_HLR_b1.def_CometInterceptorSystem_HLR_b1_Input bundle_ProbeB1.def_ProbeB1_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_b1_input_data_pattern). (channel_b1_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_HLR_b1_Input.channels\<^sup>\<Omega> \<rightarrow> def_ProbeB1_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_ProbeB1_Input.SB.setter oo connector oo def_CometInterceptorSystem_HLR_b1_Input.SB.getter }"


end
