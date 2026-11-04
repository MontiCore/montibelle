theory def_CometInterceptorSystem_HLR_b1_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_ProbeB1.def_ProbeB1_Output bundle_CometInterceptorSystem_HLR_b1.def_CometInterceptorSystem_HLR_b1_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_ProbeB1_Output.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_HLR_b1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_CometInterceptorSystem_HLR_b1_Output.SB.setter oo connector oo def_ProbeB1_Output.SB.getter }"


end
