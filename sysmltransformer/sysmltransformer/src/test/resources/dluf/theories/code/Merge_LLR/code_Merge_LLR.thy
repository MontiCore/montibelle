theory code_Merge_LLR
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Merge_LLR.def_Merge_LLR code_Merge_LLR_Input code_Merge_LLR_Output bundle_Merge_LLR.def_Merge_LLR_Input bundle_Merge_LLR.def_Merge_LLR_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s) channel_input1_data_pattern = [(StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input1_data_pattern))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s) channel_input1_data_pattern =
    (if (guard_00 () (StateConstr s) channel_input1_data_pattern) then (executableExpression_00 () (StateConstr s) channel_input1_data_pattern) else [])"

fun executableExpression_10 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_10 () (StateConstr s) channel_input2_data_pattern = [(StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input2_data_pattern))])]"

fun executableTransitionH_10 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_10 () (StateConstr s) channel_input2_data_pattern =
    (if (guard_10 () (StateConstr s) channel_input2_data_pattern) then (executableExpression_10 () (StateConstr s) channel_input2_data_pattern) else [])"

fun executableExpression_20 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_20 () (StateConstr s) channel_input3_data_pattern = [(StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input3_data_pattern))])]"

fun executableTransitionH_20 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_20 () (StateConstr s) channel_input3_data_pattern =
    (if (guard_20 () (StateConstr s) channel_input3_data_pattern) then (executableExpression_20 () (StateConstr s) channel_input3_data_pattern) else [])"

fun executableExpression_30 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableExpression_30 () (StateConstr s) channel_input4_data_pattern = [(StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input4_data_pattern))])]"

fun executableTransitionH_30 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableTransitionH_30 () (StateConstr s) channel_input4_data_pattern =
    (if (guard_30 () (StateConstr s) channel_input4_data_pattern) then (executableExpression_30 () (StateConstr s) channel_input4_data_pattern) else [])"


fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Merge_LLR_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_input1_data, PacketEVENTConstr channel_input1_data_pattern) =
    executableTransitionH_00 para state channel_input1_data_pattern" | 
"executableEventTransition para state (channel_input2_data, PacketEVENTConstr channel_input2_data_pattern) =
    executableTransitionH_10 para state channel_input2_data_pattern" | 
"executableEventTransition para state (channel_input3_data, PacketEVENTConstr channel_input3_data_pattern) =
    executableTransitionH_20 para state channel_input3_data_pattern" | 
"executableEventTransition para state (channel_input4_data, PacketEVENTConstr channel_input4_data_pattern) =
    executableTransitionH_30 para state channel_input4_data_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) list" where
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



fun sb2stream::"def_Merge_LLR_Output.channels\<^sup>\<Omega> \<Rightarrow> (Packet event stream)" where
"sb2stream a = def_Merge_LLR_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Merge_LLR_Input.sbsetter" "sb2stream" in Scala module_name def_Merge_LLR_scalaExec file_prefix "def_Merge_LLR_scalaExec" (case_insensitive)


end
