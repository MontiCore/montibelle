theory def_Buffer_LLR
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_Buffer_HLR3.def_Buffer_HLR3_Input bundle_Buffer_HLR3.def_Buffer_HLR3_Output def_Buffer_LLR_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = (s = Substate.state__S \<and> (((length var_old_packets) = 0)))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = {
    (StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), [(channel_Buffer_HLR3_output_dataConstr (channel_input_data_pattern))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern =
    (if (guard_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) then (expression_00 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = (s = Substate.state__S \<and> (((length var_old_packets) > 0)))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern = {
    (StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), [])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern =
    (if (guard_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) then (expression_01 () (StateConstr s var_old_packets var_new_packets) channel_input_data_pattern) else {})"


fun guard_10 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> bool" where
"guard_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = (s = Substate.state__S \<and> (((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) > 1))))"

fun expression_10 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = {
    (StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), [])
}"

fun transitionH_10 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (expression_10 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else {})"

fun guard_11 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> bool" where
"guard_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = (s = Substate.state__S \<and> (((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) = 1))))"

fun expression_11 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = {
    (StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), (map channel_Buffer_HLR3_output_dataConstr (var_new_packets)))
}"

fun transitionH_11 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (expression_11 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else {})"

fun guard_12 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> bool" where
"guard_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = (s = Substate.state__S \<and> (((channel_control_data_pattern = CtrlEnum.NAK) \<and> ((length var_old_packets) > 0))))"

fun expression_12 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = {
    (StateConstr Substate.state__S ([]) ((append var_old_packets var_new_packets)), (map channel_Buffer_HLR3_output_dataConstr ((append var_old_packets var_new_packets))))
}"

fun transitionH_12 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (expression_12 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else {})"

fun guard_13 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> bool" where
"guard_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = (s = Substate.state__S \<and> (((length var_old_packets) = 0)))"

fun expression_13 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expression_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern = {
    (StateConstr Substate.state__S (var_old_packets) (var_new_packets), [])
}"

fun transitionH_13 :: "unit \<Rightarrow> State \<Rightarrow> CtrlEnum \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern =
    (if (guard_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) then (expression_13 () (StateConstr s var_old_packets var_new_packets) channel_control_data_pattern) else {})"



fun guardT_0 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 () (StateConstr s var_old_packets var_new_packets) = (s = Substate.state__S \<and> (True))"

fun expressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"expressionT_0 () (StateConstr s var_old_packets var_new_packets) = {
    (StateConstr Substate.state__S (var_new_packets) ([]), [])
}"

fun transitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"transitionTH_0 () (StateConstr s var_old_packets var_new_packets) =
    (if (guardT_0 () (StateConstr s var_old_packets var_new_packets)) then (expressionT_0 () (StateConstr s var_old_packets var_new_packets)) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Buffer_HLR3_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_input_data, PacketEVENTConstr channel_input_data_pattern) =
    transitionH_00 para state channel_input_data_pattern \<union>
    transitionH_01 para state channel_input_data_pattern" | 
"eventTransition para state (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern) =
    transitionH_10 para state channel_control_data_pattern \<union>
    transitionH_11 para state channel_control_data_pattern \<union>
    transitionH_12 para state channel_control_data_pattern \<union>
    transitionH_13 para state channel_control_data_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_Buffer_HLR3_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S ([]) ([]), [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      False
  apply(unfold_locales)
  done

ML \<open>structure def_Buffer_LLR = struct
  val channel_Buffer_HLR3_input_data_transitionList = [
    ("line 22 to 30", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("line 32 to 37", @{term guard_01}, @{term expression_01}, @{term transitionH_01})]
  val tick_transitionList = [
    ("line 73 to 80", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0})]
  val channel_Buffer_HLR3_control_data_transitionList = [
    ("line 39 to 44", @{term guard_10}, @{term expression_10}, @{term transitionH_10}),
    ("line 46 to 54", @{term guard_11}, @{term expression_11}, @{term transitionH_11}),
    ("line 56 to 65", @{term guard_12}, @{term expression_12}, @{term transitionH_12}),
    ("line 67 to 71", @{term guard_13}, @{term expression_13}, @{term transitionH_13})]
  val tick_transitionList = [
    ("line 73 to 80", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0})]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<rightarrow> def_Buffer_HLR3_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
