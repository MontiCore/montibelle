theory def_Lambdas
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_Lambdas.def_Lambdas_Input bundle_Lambdas.def_Lambdas_Output def_Lambdas_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s var_Map) channel_i_val_pattern = (s = Substate.state__S \<and> (True))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s var_Map) channel_i_val_pattern = {
    (StateConstr Substate.state__S ((\<lambda> var_b. (Not var_b))), [])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s var_Map) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_Map) channel_i_val_pattern) then (expression_00 () (StateConstr s var_Map) channel_i_val_pattern) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Lambdas_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_i_val, boolEVENTConstr channel_i_val_pattern) =
    transitionH_00 para state channel_i_val_pattern"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_Lambdas = struct
  val channel_Lambdas_i_val_transitionList = [
    ("line 16 to 23", @{term guard_00}, @{term expression_00}, @{term transitionH_00})]
  val tick_transitionList = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_Lambdas_Input.channels\<^sup>\<Omega> \<rightarrow> def_Lambdas_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
