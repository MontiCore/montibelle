theory def_SecurityGate_LLR
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_SecurityGate_LLR.def_SecurityGate_LLR_Input bundle_SecurityGate_LLR.def_SecurityGate_LLR_Output def_SecurityGate_LLR_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_00 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob_Alice \<and> ((channel_input_data_pattern = ActionEnum.Bob_wants_to_exit_cockpit)))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Alice, [])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s) channel_input_data_pattern =
    (if (guard_00 () (StateConstr s) channel_input_data_pattern) then (expression_00 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_01 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob_Alice \<and> ((channel_input_data_pattern = ActionEnum.Alice_wants_to_exit_cockpit)))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_01 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob, [])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_01 () (StateConstr s) channel_input_data_pattern =
    (if (guard_01 () (StateConstr s) channel_input_data_pattern) then (expression_01 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_02 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_02 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob_Alice \<and> (((channel_input_data_pattern \<noteq> ActionEnum.Bob_wants_to_exit_cockpit) \<and> (channel_input_data_pattern \<noteq> ActionEnum.Alice_wants_to_exit_cockpit))))"

fun expression_02 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_02 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice, [])
}"

fun transitionH_02 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_02 () (StateConstr s) channel_input_data_pattern =
    (if (guard_02 () (StateConstr s) channel_input_data_pattern) then (expression_02 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_03 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_03 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob \<and> ((channel_input_data_pattern = ActionEnum.Alice_plus_Eve_request_Camera_accepts)))"

fun expression_03 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_03 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice_Eve, [])
}"

fun transitionH_03 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_03 () (StateConstr s) channel_input_data_pattern =
    (if (guard_03 () (StateConstr s) channel_input_data_pattern) then (expression_03 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_04 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_04 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob \<and> ((channel_input_data_pattern = ActionEnum.Alice_without_Eve_request_Camera_accepts)))"

fun expression_04 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_04 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice, [])
}"

fun transitionH_04 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_04 () (StateConstr s) channel_input_data_pattern =
    (if (guard_04 () (StateConstr s) channel_input_data_pattern) then (expression_04 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_05 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_05 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob \<and> ((channel_input_data_pattern = ActionEnum.Alice_plus_Eve_request_Camera_denies)))"

fun expression_05 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_05 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Alarm_Eve_detected, [])
}"

fun transitionH_05 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_05 () (StateConstr s) channel_input_data_pattern =
    (if (guard_05 () (StateConstr s) channel_input_data_pattern) then (expression_05 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_06 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_06 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob \<and> ((((channel_input_data_pattern \<noteq> ActionEnum.Alice_plus_Eve_request_Camera_accepts) \<or> (channel_input_data_pattern \<noteq> ActionEnum.Alice_without_Eve_request_Camera_accepts)) \<or> (channel_input_data_pattern \<noteq> ActionEnum.Alice_without_Eve_request_Camera_denies))))"

fun expression_06 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_06 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob, [])
}"

fun transitionH_06 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_06 () (StateConstr s) channel_input_data_pattern =
    (if (guard_06 () (StateConstr s) channel_input_data_pattern) then (expression_06 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_07 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_07 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Alice \<and> ((channel_input_data_pattern = ActionEnum.Bob_plus_Eve_request_Camera_accepts)))"

fun expression_07 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_07 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice_Eve, [])
}"

fun transitionH_07 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_07 () (StateConstr s) channel_input_data_pattern =
    (if (guard_07 () (StateConstr s) channel_input_data_pattern) then (expression_07 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_08 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_08 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Alice \<and> ((channel_input_data_pattern = ActionEnum.Bob_without_Eve_request_Camera_accepts)))"

fun expression_08 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_08 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice, [])
}"

fun transitionH_08 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_08 () (StateConstr s) channel_input_data_pattern =
    (if (guard_08 () (StateConstr s) channel_input_data_pattern) then (expression_08 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_09 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_09 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Alice \<and> ((channel_input_data_pattern = ActionEnum.Bob_plus_Eve_request_Camera_denies)))"

fun expression_09 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_09 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Alarm_Eve_detected, [])
}"

fun transitionH_09 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_09 () (StateConstr s) channel_input_data_pattern =
    (if (guard_09 () (StateConstr s) channel_input_data_pattern) then (expression_09 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_010 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_010 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Alice \<and> ((((channel_input_data_pattern \<noteq> ActionEnum.Bob_plus_Eve_request_Camera_accepts) \<or> (channel_input_data_pattern \<noteq> ActionEnum.Bob_without_Eve_request_Camera_accepts)) \<or> (channel_input_data_pattern \<noteq> ActionEnum.Bob_without_Eve_request_Camera_denies))))"

fun expression_010 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_010 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Alice, [])
}"

fun transitionH_010 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_010 () (StateConstr s) channel_input_data_pattern =
    (if (guard_010 () (StateConstr s) channel_input_data_pattern) then (expression_010 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_011 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_011 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Bob_Alice_Eve \<and> (True))"

fun expression_011 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_011 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Bob_Alice_Eve, [])
}"

fun transitionH_011 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_011 () (StateConstr s) channel_input_data_pattern =
    (if (guard_011 () (StateConstr s) channel_input_data_pattern) then (expression_011 () (StateConstr s) channel_input_data_pattern) else {})"

fun guard_012 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> bool" where
"guard_012 () (StateConstr s) channel_input_data_pattern = (s = Substate.state__Alarm_Eve_detected \<and> (True))"

fun expression_012 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expression_012 () (StateConstr s) channel_input_data_pattern = {
    (StateConstr Substate.state__Alarm_Eve_detected, [])
}"

fun transitionH_012 :: "unit \<Rightarrow> State \<Rightarrow> ActionEnum \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionH_012 () (StateConstr s) channel_input_data_pattern =
    (if (guard_012 () (StateConstr s) channel_input_data_pattern) then (expression_012 () (StateConstr s) channel_input_data_pattern) else {})"



fun guardT_0 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 () (StateConstr s) = (s = Substate.state__Bob_Alice \<and> (True))"

fun expressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expressionT_0 () (StateConstr s) = {
    (StateConstr Substate.state__Bob_Alice, [])
}"

fun transitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (expressionT_0 () (StateConstr s)) else {})"

fun guardT_1 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_1 () (StateConstr s) = (s = Substate.state__Bob \<and> (True))"

fun expressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expressionT_1 () (StateConstr s) = {
    (StateConstr Substate.state__Bob, [])
}"

fun transitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (expressionT_1 () (StateConstr s)) else {})"

fun guardT_2 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_2 () (StateConstr s) = (s = Substate.state__Alice \<and> (True))"

fun expressionT_2 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expressionT_2 () (StateConstr s) = {
    (StateConstr Substate.state__Alice, [])
}"

fun transitionTH_2 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionTH_2 () (StateConstr s) =
    (if (guardT_2 () (StateConstr s)) then (expressionT_2 () (StateConstr s)) else {})"

fun guardT_3 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_3 () (StateConstr s) = (s = Substate.state__Bob_Alice_Eve \<and> (True))"

fun expressionT_3 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expressionT_3 () (StateConstr s) = {
    (StateConstr Substate.state__Bob_Alice_Eve, [])
}"

fun transitionTH_3 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionTH_3 () (StateConstr s) =
    (if (guardT_3 () (StateConstr s)) then (expressionT_3 () (StateConstr s)) else {})"

fun guardT_4 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_4 () (StateConstr s) = (s = Substate.state__Alarm_Eve_detected \<and> (True))"

fun expressionT_4 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"expressionT_4 () (StateConstr s) = {
    (StateConstr Substate.state__Alarm_Eve_detected, [])
}"

fun transitionTH_4 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"transitionTH_4 () (StateConstr s) =
    (if (guardT_4 () (StateConstr s)) then (expressionT_4 () (StateConstr s)) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_SecurityGate_LLR_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_input_data, ActionEnumEVENTConstr channel_input_data_pattern) =
    transitionH_00 para state channel_input_data_pattern \<union>
    transitionH_01 para state channel_input_data_pattern \<union>
    transitionH_02 para state channel_input_data_pattern \<union>
    transitionH_03 para state channel_input_data_pattern \<union>
    transitionH_04 para state channel_input_data_pattern \<union>
    transitionH_05 para state channel_input_data_pattern \<union>
    transitionH_06 para state channel_input_data_pattern \<union>
    transitionH_07 para state channel_input_data_pattern \<union>
    transitionH_08 para state channel_input_data_pattern \<union>
    transitionH_09 para state channel_input_data_pattern \<union>
    transitionH_010 para state channel_input_data_pattern \<union>
    transitionH_011 para state channel_input_data_pattern \<union>
    transitionH_012 para state channel_input_data_pattern"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state \<union>
    transitionTH_1 para state \<union>
    transitionTH_2 para state \<union>
    transitionTH_3 para state \<union>
    transitionTH_4 para state"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_SecurityGate_LLR_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__Bob_Alice, [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_SecurityGate_LLR = struct
  val channel_SecurityGate_LLR_input_data_transitionList = [
    ("line 14 to 18", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("line 20 to 24", @{term guard_01}, @{term expression_01}, @{term transitionH_01}),
    ("line 26 to 30", @{term guard_02}, @{term expression_02}, @{term transitionH_02}),
    ("line 32 to 36", @{term guard_03}, @{term expression_03}, @{term transitionH_03}),
    ("line 38 to 42", @{term guard_04}, @{term expression_04}, @{term transitionH_04}),
    ("line 44 to 48", @{term guard_05}, @{term expression_05}, @{term transitionH_05}),
    ("line 50 to 54", @{term guard_06}, @{term expression_06}, @{term transitionH_06}),
    ("line 56 to 60", @{term guard_07}, @{term expression_07}, @{term transitionH_07}),
    ("line 62 to 66", @{term guard_08}, @{term expression_08}, @{term transitionH_08}),
    ("line 68 to 72", @{term guard_09}, @{term expression_09}, @{term transitionH_09}),
    ("line 74 to 78", @{term guard_010}, @{term expression_010}, @{term transitionH_010}),
    ("line 80 to 83", @{term guard_011}, @{term expression_011}, @{term transitionH_011}),
    ("line 85 to 88", @{term guard_012}, @{term expression_012}, @{term transitionH_012})]
  val tick_transitionList = [
    ("line 90 to 93", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0}),
    ("line 95 to 98", @{term guardT_1}, @{term expressionT_1}, @{term transitionTH_1}),
    ("line 100 to 103", @{term guardT_2}, @{term expressionT_2}, @{term transitionTH_2}),
    ("line 105 to 108", @{term guardT_3}, @{term expressionT_3}, @{term transitionTH_3}),
    ("line 110 to 113", @{term guardT_4}, @{term expressionT_4}, @{term transitionTH_4})]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_SecurityGate_LLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecurityGate_LLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
