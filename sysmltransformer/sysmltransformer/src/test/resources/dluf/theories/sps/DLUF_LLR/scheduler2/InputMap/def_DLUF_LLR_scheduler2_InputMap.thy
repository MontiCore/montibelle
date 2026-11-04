theory def_DLUF_LLR_scheduler2_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLUF_LLR_scheduler2.def_DLUF_LLR_scheduler2_Input bundle_Scheduler_HLR2.def_Scheduler_HLR2_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_scheduler2_input_data_pattern). (channel_scheduler2_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DLUF_LLR_scheduler2_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR2_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Scheduler_HLR2_Input.SB.setter oo connector oo def_DLUF_LLR_scheduler2_Input.SB.getter }"


end
