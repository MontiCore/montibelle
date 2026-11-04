theory def_automaton_Event
  imports eventcomponent.EventLocale stream.StreamCodegen expressions.UntimedExpressions liftedstreams.UntimedLiftedStream component.EventExecLocale
          io.EventInput io.EventOutput io.EventInput_gen io.EventOutput_gen Event_States

begin



lift_definition beOutChannelConstr :: "bool \<Rightarrow> channels eventWithChan" is
"\<lambda>x. (beOutChannel_rep, boolEVENTConstr x)"
  by (simp add: well_def)




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s) beInChannel_pattern = (s = Substate.state__S \<and> (beInChannel_pattern = False))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"expression_00 () (StateConstr s) beInChannel_pattern = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (False))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"transitionH_00 () (StateConstr s) beInChannel_pattern =
    (if (guard_00 () (StateConstr s) beInChannel_pattern) then (expression_00 () (StateConstr s) beInChannel_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_01 () (StateConstr s) beInChannel_pattern = (s = Substate.state__S \<and> (beInChannel_pattern = True))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"expression_01 () (StateConstr s) beInChannel_pattern = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (True))])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"transitionH_01 () (StateConstr s) beInChannel_pattern =
    (if (guard_01 () (StateConstr s) beInChannel_pattern) then (expression_01 () (StateConstr s) beInChannel_pattern) else {})"



fun guardT_0 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 () (StateConstr s) = (s = Substate.state__S \<and> (True))"

fun expressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"expressionT_0 () (StateConstr s) = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (False))])
}"

fun transitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"transitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (expressionT_0 () (StateConstr s)) else {})"

fun guardT_1 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_1 () (StateConstr s) = (s = Substate.state__S \<and> (True))"

fun expressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"expressionT_1 () (StateConstr s) = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (True))])
}"

fun transitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"transitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (expressionT_1 () (StateConstr s)) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (EventInput.channels \<times> M_pure) \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"eventTransition para state (beInChannel_rep, boolEVENTConstr beInChannel_pattern) =
    transitionH_00 para state beInChannel_pattern \<union>
    transitionH_01 para state beInChannel_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state \<union>
    transitionTH_1 para state"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S, [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure Event = struct
  val beInChannel_transitionList = [
    ("", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("", @{term guard_01}, @{term expression_01}, @{term transitionH_01})]
  val tick_transitionList = [
    ("", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0}),
    ("", @{term guardT_1}, @{term expressionT_1}, @{term transitionTH_1})]
end\<close>

definition Sps :: "unit \<Rightarrow> (EventInput.channels\<^sup>\<Omega> \<rightarrow> EventOutput.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableExpression_00 () (StateConstr s) beInChannel_pattern = [(StateConstr Substate.state__S, [(beOutChannelConstr (False))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s) beInChannel_pattern =
    (if (guard_00 () (StateConstr s) beInChannel_pattern) then (executableExpression_00 () (StateConstr s) beInChannel_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableExpression_01 () (StateConstr s) beInChannel_pattern = [(StateConstr Substate.state__S, [(beOutChannelConstr (True))])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s) beInChannel_pattern =
    (if (guard_01 () (StateConstr s) beInChannel_pattern) then (executableExpression_01 () (StateConstr s) beInChannel_pattern) else [])"



fun executableExpressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableExpressionT_0 () (StateConstr s) = [(StateConstr Substate.state__S, [(beOutChannelConstr (False))])]"

fun executableTransitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableTransitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (executableExpressionT_0 () (StateConstr s)) else [])"

fun executableExpressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableExpressionT_1 () (StateConstr s) = [(StateConstr Substate.state__S, [(beOutChannelConstr (True))])]"

fun executableTransitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableTransitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (executableExpressionT_1 () (StateConstr s)) else [])"



fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (EventInput.channels \<times> M_pure) \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableEventTransition para state (beInChannel_rep, boolEVENTConstr beInChannel_pattern) =
    executableTransitionH_00 para state beInChannel_pattern @
    executableTransitionH_01 para state beInChannel_pattern" |
"executableEventTransition _ _ _ = []"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
"executableTickTransition para state =
    executableTransitionTH_0 para state @
    executableTransitionTH_1 para state"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (EventOutput.channels eventWithChan) list) list" where
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

end
