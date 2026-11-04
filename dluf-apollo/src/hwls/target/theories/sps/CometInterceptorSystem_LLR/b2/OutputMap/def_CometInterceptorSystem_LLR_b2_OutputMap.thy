theory def_CometInterceptorSystem_LLR_b2_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_ProbeB2.def_ProbeB2_Output bundle_CometInterceptorSystem_LLR_b2.def_CometInterceptorSystem_LLR_b2_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_ProbeB2_Output.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_LLR_b2_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_CometInterceptorSystem_LLR_b2_Output.SB.setter oo connector oo def_ProbeB2_Output.SB.getter }"


end
