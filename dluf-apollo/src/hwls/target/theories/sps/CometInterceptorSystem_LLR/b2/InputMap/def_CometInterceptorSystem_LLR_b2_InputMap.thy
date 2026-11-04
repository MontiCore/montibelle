theory def_CometInterceptorSystem_LLR_b2_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_CometInterceptorSystem_LLR_b2.def_CometInterceptorSystem_LLR_b2_Input bundle_ProbeB2.def_ProbeB2_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_b2_input_data_pattern). (channel_b2_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_LLR_b2_Input.channels\<^sup>\<Omega> \<rightarrow> def_ProbeB2_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_ProbeB2_Input.SB.setter oo connector oo def_CometInterceptorSystem_LLR_b2_Input.SB.getter }"


end
