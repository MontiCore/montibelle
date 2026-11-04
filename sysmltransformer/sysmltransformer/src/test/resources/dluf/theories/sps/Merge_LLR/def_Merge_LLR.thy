theory def_Merge_LLR
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_Merge_LLR.def_Merge_LLR_Input bundle_Merge_LLR.def_Merge_LLR_Output def_Merge_LLR_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_00 () (StateConstr s) channel_input1_data_pattern = (s = Substate.state__S \<and> (True))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s) channel_input1_data_pattern = {
    (StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input1_data_pattern))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s) channel_input1_data_pattern =
    (if (guard_00 () (StateConstr s) channel_input1_data_pattern) then (expression_00 () (StateConstr s) channel_input1_data_pattern) else {})"


fun guard_10 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_10 () (StateConstr s) channel_input2_data_pattern = (s = Substate.state__S \<and> (True))"

fun expression_10 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"expression_10 () (StateConstr s) channel_input2_data_pattern = {
    (StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input2_data_pattern))])
}"

fun transitionH_10 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"transitionH_10 () (StateConstr s) channel_input2_data_pattern =
    (if (guard_10 () (StateConstr s) channel_input2_data_pattern) then (expression_10 () (StateConstr s) channel_input2_data_pattern) else {})"


fun guard_20 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_20 () (StateConstr s) channel_input3_data_pattern = (s = Substate.state__S \<and> (True))"

fun expression_20 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"expression_20 () (StateConstr s) channel_input3_data_pattern = {
    (StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input3_data_pattern))])
}"

fun transitionH_20 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"transitionH_20 () (StateConstr s) channel_input3_data_pattern =
    (if (guard_20 () (StateConstr s) channel_input3_data_pattern) then (expression_20 () (StateConstr s) channel_input3_data_pattern) else {})"


fun guard_30 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_30 () (StateConstr s) channel_input4_data_pattern = (s = Substate.state__S \<and> (True))"

fun expression_30 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"expression_30 () (StateConstr s) channel_input4_data_pattern = {
    (StateConstr Substate.state__S, [(channel_Merge_LLR_output_dataConstr (channel_input4_data_pattern))])
}"

fun transitionH_30 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"transitionH_30 () (StateConstr s) channel_input4_data_pattern =
    (if (guard_30 () (StateConstr s) channel_input4_data_pattern) then (expression_30 () (StateConstr s) channel_input4_data_pattern) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Merge_LLR_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_input1_data, PacketEVENTConstr channel_input1_data_pattern) =
    transitionH_00 para state channel_input1_data_pattern" | 
"eventTransition para state (channel_input2_data, PacketEVENTConstr channel_input2_data_pattern) =
    transitionH_10 para state channel_input2_data_pattern" | 
"eventTransition para state (channel_input3_data, PacketEVENTConstr channel_input3_data_pattern) =
    transitionH_20 para state channel_input3_data_pattern" | 
"eventTransition para state (channel_input4_data, PacketEVENTConstr channel_input4_data_pattern) =
    transitionH_30 para state channel_input4_data_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_Merge_LLR_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S, [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_Merge_LLR = struct
  val channel_Merge_LLR_input1_data_transitionList = [
    ("line 12 to 16", @{term guard_00}, @{term expression_00}, @{term transitionH_00})]
  val tick_transitionList = [
]
  val channel_Merge_LLR_input2_data_transitionList = [
    ("line 18 to 22", @{term guard_10}, @{term expression_10}, @{term transitionH_10})]
  val tick_transitionList = [
]
  val channel_Merge_LLR_input3_data_transitionList = [
    ("line 24 to 28", @{term guard_20}, @{term expression_20}, @{term transitionH_20})]
  val tick_transitionList = [
]
  val channel_Merge_LLR_input4_data_transitionList = [
    ("line 30 to 34", @{term guard_30}, @{term expression_30}, @{term transitionH_30})]
  val tick_transitionList = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_Merge_LLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Merge_LLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
