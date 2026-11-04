theory def_DLUF_HLR3_scheduler1_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_HLR2.def_Scheduler_HLR2_Output bundle_DLUF_HLR3_scheduler1.def_DLUF_HLR3_scheduler1_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Scheduler_HLR2_Output.channels\<^sup>\<Omega> \<rightarrow> def_DLUF_HLR3_scheduler1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_DLUF_HLR3_scheduler1_Output.SB.setter oo connector oo def_Scheduler_HLR2_Output.SB.getter }"


end
