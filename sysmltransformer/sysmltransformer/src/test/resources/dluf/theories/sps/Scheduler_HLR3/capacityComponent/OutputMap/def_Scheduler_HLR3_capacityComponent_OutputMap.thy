theory def_Scheduler_HLR3_capacityComponent_OutputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) bundle_Capacity_HLR3.def_Capacity_HLR3_Output bundle_Scheduler_HLR3_capacityComponent.def_Scheduler_HLR3_capacityComponent_Output
    (* Hwl  *)

begin


lift_definition connector :: "(CtrlEnum event stream \<times> Packet event stream) \<rightarrow> (CtrlEnum event stream \<times> Packet event stream)" is
"\<lambda> (channel_control_data_pattern, channel_output_data_pattern). (channel_control_data_pattern, channel_output_data_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (def_Capacity_HLR3_Output.channels\<^sup>\<Omega> \<rightarrow> def_Scheduler_HLR3_capacityComponent_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { def_Scheduler_HLR3_capacityComponent_Output.SB.setter oo connector oo def_Capacity_HLR3_Output.SB.getter }"


end
