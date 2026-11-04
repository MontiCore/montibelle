theory def_Inverter_LLR2
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_Inverter_HLR1.def_Inverter_HLR1_Input bundle_Inverter_HLR1.def_Inverter_HLR1_Output def_Inverter_LLR2_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s) channel_input_val_pattern = (s = Substate.state__S \<and> ((channel_input_val_pattern = True)))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s) channel_input_val_pattern = {
    (StateConstr Substate.state__S, [(channel_Inverter_HLR1_output_valConstr (False))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s) channel_input_val_pattern =
    (if (guard_00 () (StateConstr s) channel_input_val_pattern) then (expression_00 () (StateConstr s) channel_input_val_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_01 () (StateConstr s) channel_input_val_pattern = (s = Substate.state__S \<and> ((channel_input_val_pattern = False)))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"expression_01 () (StateConstr s) channel_input_val_pattern = {
    (StateConstr Substate.state__S, [(channel_Inverter_HLR1_output_valConstr (True))])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"transitionH_01 () (StateConstr s) channel_input_val_pattern =
    (if (guard_01 () (StateConstr s) channel_input_val_pattern) then (expression_01 () (StateConstr s) channel_input_val_pattern) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Inverter_HLR1_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_input_val, boolEVENTConstr channel_input_val_pattern) =
    transitionH_00 para state channel_input_val_pattern \<union>
    transitionH_01 para state channel_input_val_pattern"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_Inverter_HLR1_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S, [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_Inverter_LLR2 = struct
  val channel_Inverter_HLR1_input_val_transitionList = [
    ("line 11 to 16", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("line 18 to 23", @{term guard_01}, @{term expression_01}, @{term transitionH_01})]
  val tick_transitionList = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_Inverter_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_Inverter_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
