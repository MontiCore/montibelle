theory def_DLUF_HLR3_scheduler1_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_DLUF_HLR3_scheduler1.def_DLUF_HLR3_scheduler1_Input bundle_Scheduler_HLR2.def_Scheduler_HLR2_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_scheduler1_input_data_pattern). (channel_scheduler1_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_DLUF_HLR3_scheduler1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR2_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Scheduler_HLR2_Input.SB.setter oo connector oo def_DLUF_HLR3_scheduler1_Input.SB.getter }"


end
