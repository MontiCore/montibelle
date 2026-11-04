theory code_SecurityGate_LLR
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_SecurityGate_LLR.def_SecurityGate_LLR code_SecurityGate_LLR_Input code_SecurityGate_LLR_Output bundle_SecurityGate_LLR.def_SecurityGate_LLR_Input bundle_SecurityGate_LLR.def_SecurityGate_LLR_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Alice, [])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s) channel_input_data_pattern =
    (if (guard_00 () (StateConstr s) channel_input_data_pattern) then (executableExpression_00 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_01 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob, [])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s) channel_input_data_pattern =
    (if (guard_01 () (StateConstr s) channel_input_data_pattern) then (executableExpression_01 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_02 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_02 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice, [])]"

fun executableTransitionH_02 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_02 () (StateConstr s) channel_input_data_pattern =
    (if (guard_02 () (StateConstr s) channel_input_data_pattern) then (executableExpression_02 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_03 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_03 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice_Eve, [])]"

fun executableTransitionH_03 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_03 () (StateConstr s) channel_input_data_pattern =
    (if (guard_03 () (StateConstr s) channel_input_data_pattern) then (executableExpression_03 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_04 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_04 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice, [])]"

fun executableTransitionH_04 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_04 () (StateConstr s) channel_input_data_pattern =
    (if (guard_04 () (StateConstr s) channel_input_data_pattern) then (executableExpression_04 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_05 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_05 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Alarm_Eve_detected, [])]"

fun executableTransitionH_05 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_05 () (StateConstr s) channel_input_data_pattern =
    (if (guard_05 () (StateConstr s) channel_input_data_pattern) then (executableExpression_05 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_06 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_06 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob, [])]"

fun executableTransitionH_06 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_06 () (StateConstr s) channel_input_data_pattern =
    (if (guard_06 () (StateConstr s) channel_input_data_pattern) then (executableExpression_06 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_07 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_07 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice_Eve, [])]"

fun executableTransitionH_07 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_07 () (StateConstr s) channel_input_data_pattern =
    (if (guard_07 () (StateConstr s) channel_input_data_pattern) then (executableExpression_07 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_08 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_08 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice, [])]"

fun executableTransitionH_08 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_08 () (StateConstr s) channel_input_data_pattern =
    (if (guard_08 () (StateConstr s) channel_input_data_pattern) then (executableExpression_08 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_09 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_09 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Alarm_Eve_detected, [])]"

fun executableTransitionH_09 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_09 () (StateConstr s) channel_input_data_pattern =
    (if (guard_09 () (StateConstr s) channel_input_data_pattern) then (executableExpression_09 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_010 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_010 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Alice, [])]"

fun executableTransitionH_010 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_010 () (StateConstr s) channel_input_data_pattern =
    (if (guard_010 () (StateConstr s) channel_input_data_pattern) then (executableExpression_010 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_011 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_011 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Bob_Alice_Eve, [])]"

fun executableTransitionH_011 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_011 () (StateConstr s) channel_input_data_pattern =
    (if (guard_011 () (StateConstr s) channel_input_data_pattern) then (executableExpression_011 () (StateConstr s) channel_input_data_pattern) else [])"

fun executableExpression_012 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_012 () (StateConstr s) channel_input_data_pattern = [(StateConstr Substate.state__Alarm_Eve_detected, [])]"

fun executableTransitionH_012 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_012 () (StateConstr s) channel_input_data_pattern =
    (if (guard_012 () (StateConstr s) channel_input_data_pattern) then (executableExpression_012 () (StateConstr s) channel_input_data_pattern) else [])"



fun executableExpressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpressionT_0 () (StateConstr s) = [(StateConstr Substate.state__Bob_Alice, [])]"

fun executableTransitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (executableExpressionT_0 () (StateConstr s)) else [])"

fun executableExpressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpressionT_1 () (StateConstr s) = [(StateConstr Substate.state__Bob, [])]"

fun executableTransitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (executableExpressionT_1 () (StateConstr s)) else [])"

fun executableExpressionT_2 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpressionT_2 () (StateConstr s) = [(StateConstr Substate.state__Alice, [])]"

fun executableTransitionTH_2 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionTH_2 () (StateConstr s) =
    (if (guardT_2 () (StateConstr s)) then (executableExpressionT_2 () (StateConstr s)) else [])"

fun executableExpressionT_3 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpressionT_3 () (StateConstr s) = [(StateConstr Substate.state__Bob_Alice_Eve, [])]"

fun executableTransitionTH_3 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionTH_3 () (StateConstr s) =
    (if (guardT_3 () (StateConstr s)) then (executableExpressionT_3 () (StateConstr s)) else [])"

fun executableExpressionT_4 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableExpressionT_4 () (StateConstr s) = [(StateConstr Substate.state__Alarm_Eve_detected, [])]"

fun executableTransitionTH_4 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionTH_4 () (StateConstr s) =
    (if (guardT_4 () (StateConstr s)) then (executableExpressionT_4 () (StateConstr s)) else [])"



fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_SecurityGate_LLR_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_input_data, ActionEnumEVENTConstr channel_input_data_pattern) =
    executableTransitionH_00 para state channel_input_data_pattern @
    executableTransitionH_01 para state channel_input_data_pattern @
    executableTransitionH_02 para state channel_input_data_pattern @
    executableTransitionH_03 para state channel_input_data_pattern @
    executableTransitionH_04 para state channel_input_data_pattern @
    executableTransitionH_05 para state channel_input_data_pattern @
    executableTransitionH_06 para state channel_input_data_pattern @
    executableTransitionH_07 para state channel_input_data_pattern @
    executableTransitionH_08 para state channel_input_data_pattern @
    executableTransitionH_09 para state channel_input_data_pattern @
    executableTransitionH_010 para state channel_input_data_pattern @
    executableTransitionH_011 para state channel_input_data_pattern @
    executableTransitionH_012 para state channel_input_data_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
    executableTransitionTH_0 para state @
    executableTransitionTH_1 para state @
    executableTransitionTH_2 para state @
    executableTransitionTH_3 para state @
    executableTransitionTH_4 para state"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__Bob_Alice, [])]"

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



fun sb2stream::"def_SecurityGate_LLR_Output.channels\<^sup>\<Omega> \<Rightarrow> unit" where
"sb2stream a = ()"

export_code "execsem" "def_SecurityGate_LLR_Input.sbsetter" "sb2stream" in Scala module_name def_SecurityGate_LLR_scalaExec file_prefix "def_SecurityGate_LLR_scalaExec" (case_insensitive)


end
