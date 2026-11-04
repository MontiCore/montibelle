theory code_Inverter_LLR2
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Inverter_LLR2.def_Inverter_LLR2 code_Inverter_HLR1.code_Inverter_HLR1_Input code_Inverter_HLR1.code_Inverter_HLR1_Output bundle_Inverter_HLR1.def_Inverter_HLR1_Input bundle_Inverter_HLR1.def_Inverter_HLR1_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s) channel_input_val_pattern = [(StateConstr Substate.state__S, [(channel_Inverter_HLR1_output_valConstr (False))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s) channel_input_val_pattern =
    (if (guard_00 () (StateConstr s) channel_input_val_pattern) then (executableExpression_00 () (StateConstr s) channel_input_val_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableExpression_01 () (StateConstr s) channel_input_val_pattern = [(StateConstr Substate.state__S, [(channel_Inverter_HLR1_output_valConstr (True))])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s) channel_input_val_pattern =
    (if (guard_01 () (StateConstr s) channel_input_val_pattern) then (executableExpression_01 () (StateConstr s) channel_input_val_pattern) else [])"


fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Inverter_HLR1_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_input_val, boolEVENTConstr channel_input_val_pattern) =
    executableTransitionH_00 para state channel_input_val_pattern @
    executableTransitionH_01 para state channel_input_val_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__S, [])]"

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



fun sb2stream::"def_Inverter_HLR1_Output.channels\<^sup>\<Omega> \<Rightarrow> (bool event stream)" where
"sb2stream a = def_Inverter_HLR1_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Inverter_HLR1_Input.sbsetter" "sb2stream" in Scala module_name def_Inverter_LLR2_scalaExec file_prefix "def_Inverter_LLR2_scalaExec" (case_insensitive)


end
