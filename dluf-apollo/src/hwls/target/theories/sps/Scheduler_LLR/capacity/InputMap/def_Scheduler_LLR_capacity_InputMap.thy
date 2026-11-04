theory def_Scheduler_LLR_capacity_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_LLR_capacity.def_Scheduler_LLR_capacity_Input bundle_Capacity_HLR3.def_Capacity_HLR3_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_capacity_input_data_pattern). (channel_capacity_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Scheduler_LLR_capacity_Input.channels\<^sup>\<Omega> \<rightarrow> def_Capacity_HLR3_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Capacity_HLR3_Input.SB.setter oo connector oo def_Scheduler_LLR_capacity_Input.SB.getter }"


end
