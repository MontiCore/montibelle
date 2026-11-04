theory code_Capacity_LLR
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Capacity_LLR.def_Capacity_LLR code_Capacity_HLR3.code_Capacity_HLR3_Input code_Capacity_HLR3.code_Capacity_HLR3_Output bundle_Capacity_HLR3.def_Capacity_HLR3_Input bundle_Capacity_HLR3.def_Capacity_HLR3_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern = [(StateConstr Substate.state__Send ((var_c - Packet_get_size channel_input_data_pattern)), [(channel_Capacity_HLR3_control_dataConstr (CtrlEnum.ACK))] @ [(channel_Capacity_HLR3_output_dataConstr (channel_input_data_pattern))])]"

fun executableTransitionH_00 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (executableExpression_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else [])"

fun executableExpression_01 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern = [(StateConstr Substate.state__Block (var_c), [(channel_Capacity_HLR3_control_dataConstr (CtrlEnum.NAK))])]"

fun executableTransitionH_01 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (executableExpression_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else [])"

fun executableExpression_02 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern = [(StateConstr Substate.state__Block (var_c), [])]"

fun executableTransitionH_02 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (executableExpression_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else [])"



fun executableExpressionT_0 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableExpressionT_0 (var_cap) (StateConstr s var_c) = [(StateConstr Substate.state__Send (var_cap), [])]"

fun executableTransitionTH_0 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionTH_0 (var_cap) (StateConstr s var_c) =
    (if (guardT_0 (var_cap) (StateConstr s var_c)) then (executableExpressionT_0 (var_cap) (StateConstr s var_c)) else [])"

fun executableExpressionT_1 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableExpressionT_1 (var_cap) (StateConstr s var_c) = [(StateConstr Substate.state__Send (var_cap), [])]"

fun executableTransitionTH_1 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionTH_1 (var_cap) (StateConstr s var_c) =
    (if (guardT_1 (var_cap) (StateConstr s var_c)) then (executableExpressionT_1 (var_cap) (StateConstr s var_c)) else [])"



fun executableEventTransition :: "(nat) \<Rightarrow> State \<Rightarrow> (def_Capacity_HLR3_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_input_data, PacketEVENTConstr channel_input_data_pattern) =
    executableTransitionH_00 para state channel_input_data_pattern @
    executableTransitionH_01 para state channel_input_data_pattern @
    executableTransitionH_02 para state channel_input_data_pattern"

fun executableTickTransition :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
    executableTransitionTH_0 para state @
    executableTransitionTH_1 para state"

definition executableInitialConfigs :: "(nat) \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> (var_cap) . [(StateConstr Substate.state__Send (var_cap), [])]"

global_interpretation executableBehavior:
    eventExecGen
      executableEventTransition
      executableTickTransition
      executableInitialConfigs
      True
      defines execsem = executableBehavior.rndSem
    and laut = executableBehavior.lsaut
    and transition = executableBehavior.transition
    and ndatransition = executableBehavior.ndaTransition
    and eventtransition = executableBehavior.ndaTransition_eventC
    and ticktransition = executableBehavior.ndaTransition_tickC
    and config = executableBehavior.config
    and configC = executableBehavior.ndaInitConfigC
  done



fun sb2stream::"def_Capacity_HLR3_Output.channels\<^sup>\<Omega> \<Rightarrow> (CtrlEnum event stream \<times> Packet event stream)" where
"sb2stream a = def_Capacity_HLR3_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Capacity_HLR3_Input.sbsetter" "sb2stream" in Scala module_name def_Capacity_LLR_scalaExec file_prefix "def_Capacity_LLR_scalaExec" (case_insensitive)


end
