theory def_Scheduler_HLR3_buffer_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Buffer_HLR3.def_Buffer_HLR3_Output bundle_Scheduler_HLR3_buffer.def_Scheduler_HLR3_buffer_Output
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_output_data_pattern). (channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Buffer_HLR3_Output.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR3_buffer_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Scheduler_HLR3_buffer_Output.SB.setter oo connector oo def_Buffer_HLR3_Output.SB.getter }"


end
