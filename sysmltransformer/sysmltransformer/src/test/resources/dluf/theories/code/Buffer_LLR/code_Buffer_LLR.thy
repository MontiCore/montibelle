theory code_Buffer_LLR
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Buffer_LLR.def_Buffer_LLR code_Buffer_HLR3.code_Buffer_HLR3_Input code_Buffer_HLR3.code_Buffer_HLR3_Output bundle_Buffer_HLR3.def_Buffer_HLR3_Input bundle_Buffer_HLR3.def_Buffer_HLR3_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = [(StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), [(channel_Buffer_HLR3_output_dataConstr (channel_input_data_pattern))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern =
    (if (guard_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) then (executableExpression_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = [(StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), [])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern =
    (if (guard_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) then (executableExpression_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) else [])"

fun executableExpression_10 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = [(StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), [])]"

fun executableTransitionH_10 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (executableExpression_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else [])"

fun executableExpression_11 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = [(StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), (map channel_Buffer_HLR3_output_dataConstr (var_new_packets)))]"

fun executableTransitionH_11 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (executableExpression_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else [])"

fun executableExpression_12 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = [(StateConstr Substate.state__S ([]) ((append var_old_packets var_new_packets)), (map channel_Buffer_HLR3_output_dataConstr ((append var_old_packets var_new_packets))))]"

fun executableTransitionH_12 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (executableExpression_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else [])"

fun executableExpression_13 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpression_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = [(StateConstr Substate.state__S (var_old_packets) (var_new_packets), [])]"

fun executableTransitionH_13 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionH_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (executableExpression_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else [])"



fun executableExpressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableExpressionT_0 () (StateConstr s var_old_packets var_new_packets) = [(StateConstr Substate.state__S (var_new_packets) ([]), [])]"

fun executableTransitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTransitionTH_0 () (StateConstr s var_old_packets var_new_packets) =
    (if (guardT_0 () (StateConstr s var_old_packets var_new_packets)) then (executableExpressionT_0 () (StateConstr s var_old_packets var_new_packets)) else [])"



fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Buffer_HLR3_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_input_data, PacketEVENTConstr channel_input_data_pattern) =
    executableTransitionH_00 para state channel_input_data_pattern @
    executableTransitionH_01 para state channel_input_data_pattern" | 
"executableEventTransition para state (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern) =
    executableTransitionH_10 para state channel_control_data_pattern @
    executableTransitionH_11 para state channel_control_data_pattern @
    executableTransitionH_12 para state channel_control_data_pattern @
    executableTransitionH_13 para state channel_control_data_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
    executableTransitionTH_0 para state"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__S ([]) ([]), [])]"

global_interpretation executableBehavior:
    eventExecGen
      executableEventTransition
      executableTickTransition
      executableInitialConfigs
      False
      defines execsem = executableBehavior.rndSem
    and laut = executableBehavior.lsaut
    and transition = executableBehavior.transition
    and ndatransition = executableBehavior.ndaTransition
    and eventtransition = executableBehavior.ndaTransition_eventC
    and ticktransition = executableBehavior.ndaTransition_tickC
    and config = executableBehavior.config
    and configC = executableBehavior.ndaInitConfigC
  done



fun sb2stream::"def_Buffer_HLR3_Output.channels\<^sup>\<Omega> \<Rightarrow> (Packet event stream)" where
"sb2stream a = def_Buffer_HLR3_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Buffer_HLR3_Input.sbsetter" "sb2stream" in Scala module_name def_Buffer_LLR_scalaExec file_prefix "def_Buffer_LLR_scalaExec" (case_insensitive)


end
