theory def_Capacity_LLR
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_Capacity_HLR3.def_Capacity_HLR3_Input bundle_Capacity_HLR3.def_Capacity_HLR3_Output def_Capacity_LLR_States
    (* Hwl  *)

begin




fun guard_00 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern = (s = Substate.state__Send \<and> ((var_c >= Packet_get_size channel_input_data_pattern)))"

fun expression_00 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"expression_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern = {
    (StateConstr Substate.state__Send ((var_c - Packet_get_size channel_input_data_pattern)), [(channel_Capacity_HLR3_control_dataConstr (CtrlEnum.ACK))] @ [(channel_Capacity_HLR3_output_dataConstr (channel_input_data_pattern))])
}"

fun transitionH_00 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (expression_00 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else {})"

fun guard_01 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern = (s = Substate.state__Send \<and> ((var_c < Packet_get_size channel_input_data_pattern)))"

fun expression_01 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"expression_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern = {
    (StateConstr Substate.state__Block (var_c), [(channel_Capacity_HLR3_control_dataConstr (CtrlEnum.NAK))])
}"

fun transitionH_01 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (expression_01 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else {})"

fun guard_02 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> bool" where
"guard_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern = (s = Substate.state__Block \<and> (True))"

fun expression_02 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"expression_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern = {
    (StateConstr Substate.state__Block (var_c), [])
}"

fun transitionH_02 :: "(nat) \<Rightarrow> State \<Rightarrow> Packet \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"transitionH_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern =
    (if (guard_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern) then (expression_02 (var_cap) (StateConstr s var_c) channel_input_data_pattern) else {})"



fun guardT_0 :: "(nat) \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 (var_cap) (StateConstr s var_c) = (s = Substate.state__Send \<and> (True))"

fun expressionT_0 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"expressionT_0 (var_cap) (StateConstr s var_c) = {
    (StateConstr Substate.state__Send (var_cap), [])
}"

fun transitionTH_0 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"transitionTH_0 (var_cap) (StateConstr s var_c) =
    (if (guardT_0 (var_cap) (StateConstr s var_c)) then (expressionT_0 (var_cap) (StateConstr s var_c)) else {})"

fun guardT_1 :: "(nat) \<Rightarrow> State \<Rightarrow> bool" where
"guardT_1 (var_cap) (StateConstr s var_c) = (s = Substate.state__Block \<and> (True))"

fun expressionT_1 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"expressionT_1 (var_cap) (StateConstr s var_c) = {
    (StateConstr Substate.state__Send (var_cap), [])
}"

fun transitionTH_1 :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"transitionTH_1 (var_cap) (StateConstr s var_c) =
    (if (guardT_1 (var_cap) (StateConstr s var_c)) then (expressionT_1 (var_cap) (StateConstr s var_c)) else {})"



fun eventTransition :: "(nat) \<Rightarrow> State \<Rightarrow> (def_Capacity_HLR3_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_input_data, PacketEVENTConstr channel_input_data_pattern) =
    transitionH_00 para state channel_input_data_pattern \<union>
    transitionH_01 para state channel_input_data_pattern \<union>
    transitionH_02 para state channel_input_data_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "(nat) \<Rightarrow> State \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state \<union>
    transitionTH_1 para state"

definition initialConfigs :: "(nat) \<Rightarrow> (State \<times> (def_Capacity_HLR3_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> (var_cap) . {(StateConstr Substate.state__Send (var_cap), [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_Capacity_LLR = struct
  val channel_Capacity_HLR3_input_data_transitionList = [
    ("line 19 to 28", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("line 30 to 35", @{term guard_01}, @{term expression_01}, @{term transitionH_01}),
    ("line 37 to 40", @{term guard_02}, @{term expression_02}, @{term transitionH_02})]
  val tick_transitionList = [
    ("line 42 to 46", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0}),
    ("line 48 to 52", @{term guardT_1}, @{term expressionT_1}, @{term transitionTH_1})]
end\<close>

definition Sps :: "(nat) \<Rightarrow> (def_Capacity_HLR3_Input.channels\<^sup>\<Omega> \<rightarrow> def_Capacity_HLR3_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap). behavior.Sem (var_cap)"


end
