theory def_Scheduler_LLR_capacityComponent_InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Scheduler_LLR_capacityComponent.def_Scheduler_LLR_capacityComponent_Input bundle_Capacity_HLR3.def_Capacity_HLR3_Input
    (* Hwl  *)

begin


lift_definition connector :: "(Packet event stream) \<rightarrow> (Packet event stream)" is
"\<lambda> (channel_capacityComponent_input_data_pattern). (channel_capacityComponent_input_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Scheduler_LLR_capacityComponent_Input.channels\<^sup>\<Omega> \<rightarrow> def_Capacity_HLR3_Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Capacity_HLR3_Input.SB.setter oo connector oo def_Scheduler_LLR_capacityComponent_Input.SB.getter }"


end
