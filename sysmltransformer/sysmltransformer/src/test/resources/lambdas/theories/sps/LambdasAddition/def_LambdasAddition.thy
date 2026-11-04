theory def_LambdasAddition
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_LambdasAddition.def_LambdasAddition_Input bundle_LambdasAddition.def_LambdasAddition_Output def_LambdasAddition_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> nat \<Rightarrow> bool" where
"guard_00 () (StateConstr s var_Map) channel_i_val_pattern = (s = Substate.state__S \<and> (True))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> nat \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s var_Map) channel_i_val_pattern = {
    (StateConstr Substate.state__S ((\<lambda> var_i var_j. (var_i + var_j))), [])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> nat \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s var_Map) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_Map) channel_i_val_pattern) then (expression_00 () (StateConstr s var_Map) channel_i_val_pattern) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_LambdasAddition_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_i_val, natEVENTConstr channel_i_val_pattern) =
    transitionH_00 para state channel_i_val_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_LambdasAddition = struct
  val channel_LambdasAddition_i_val_transitionList = [
    ("line 17 to 24", @{term guard_00}, @{term expression_00}, @{term transitionH_00})]
  val tick_transitionList = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_LambdasAddition_Input.channels\<^sup>\<Omega> \<rightarrow> def_LambdasAddition_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
