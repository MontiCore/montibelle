theory def_avionic_FairMedium
  imports eventcomponent.EventLocale stream.StreamCodegen expressions.UntimedExpressions liftedstreams.UntimedLiftedStream component.EventExecLocale
          bundle_avionic_UnfairMedium.def_avionic_UnfairMedium_Input bundle_avionic_UnfairMedium.def_avionic_UnfairMedium_Output bundle_avionic_UnfairMedium.def_avionic_UnfairMedium_Input_gen bundle_avionic_UnfairMedium.def_avionic_UnfairMedium_Output_gen def_avionic_FairMedium_States
          

begin



lift_definition channel_avionic_Booleans_val_o_valConstr :: "bool \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (channel_o_val, boolEVENTConstr x)"
  by (simp add: well_def)




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s var_counter) channel_i_val_pattern = (s = Substate.state__State \<and> (toBool (liftedEq (lift var_counter) (lift 0))))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s var_counter) channel_i_val_pattern = {
    (StateConstr Substate.state__State ((lift 10)), [(channel_avionic_Booleans_val_o_valConstr (channel_i_val_pattern))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s var_counter) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_counter) channel_i_val_pattern) then (expression_00 () (StateConstr s var_counter) channel_i_val_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_01 () (StateConstr s var_counter) channel_i_val_pattern = (s = Substate.state__State \<and> (toBool (liftedApplyTwo (>) (lift var_counter) (lift 0))))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"expression_01 () (StateConstr s var_counter) channel_i_val_pattern = {
    (StateConstr Substate.state__State (liftedApplyTwo (-) (lift var_counter) (lift 1)), [])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"transitionH_01 () (StateConstr s var_counter) channel_i_val_pattern =
    (if (guard_01 () (StateConstr s var_counter) channel_i_val_pattern) then (expression_01 () (StateConstr s var_counter) channel_i_val_pattern) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_avionic_UnfairMedium_Input.channels \<times> M_pure) \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"eventTransition para state (channel_i_val, boolEVENTConstr channel_i_val_pattern) =
    transitionH_00 para state channel_i_val_pattern \<union>
    transitionH_01 para state channel_i_val_pattern"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__State ((lift 0)), [(channel_avionic_Booleans_val_o_valConstr (True))])} \<union> {(StateConstr Substate.state__State ((lift 0)), [(channel_avionic_Booleans_val_o_valConstr (False))])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure def_avionic_FairMedium = struct
  val channel_avionic_Booleans_val_i_val_transitionList = [
    ("line 49 to 54", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("line 56 to 61", @{term guard_01}, @{term expression_01}, @{term transitionH_01})]
  val tick_transitionList = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (def_avionic_UnfairMedium_Input.channels\<^sup>\<Omega> \<rightarrow> def_avionic_UnfairMedium_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"



fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s var_counter) channel_i_val_pattern = [(StateConstr Substate.state__State ((lift 10)), [(channel_avionic_Booleans_val_o_valConstr (channel_i_val_pattern))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s var_counter) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_counter) channel_i_val_pattern) then (executableExpression_00 () (StateConstr s var_counter) channel_i_val_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableExpression_01 () (StateConstr s var_counter) channel_i_val_pattern = [(StateConstr Substate.state__State (liftedApplyTwo (-) (lift var_counter) (lift 1)), [])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s var_counter) channel_i_val_pattern =
    (if (guard_01 () (StateConstr s var_counter) channel_i_val_pattern) then (executableExpression_01 () (StateConstr s var_counter) channel_i_val_pattern) else [])"


fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_avionic_UnfairMedium_Input.channels \<times> M_pure) \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_i_val, boolEVENTConstr channel_i_val_pattern) =
    executableTransitionH_00 para state channel_i_val_pattern @
    executableTransitionH_01 para state channel_i_val_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_avionic_UnfairMedium_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__State ((lift 0)), [(channel_avionic_Booleans_val_o_valConstr (True))]) , (StateConstr Substate.state__State ((lift 0)), [(channel_avionic_Booleans_val_o_valConstr (False))])]"

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
end
