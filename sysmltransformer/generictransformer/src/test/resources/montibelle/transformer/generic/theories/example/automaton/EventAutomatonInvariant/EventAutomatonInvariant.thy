theory EventAutomatonInvariant
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) io.EventInput io.EventOutput EventAutomatonInvariant_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s iTest) beInChannel_pattern = (s = Substate.state__S \<and> (True))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s iTest) beInChannel_pattern = {
    (StateConstr Substate.state__T (iTest), [])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s iTest) beInChannel_pattern =
    (if (guard_00 () (StateConstr s iTest) beInChannel_pattern) then (expression_00 () (StateConstr s iTest) beInChannel_pattern) else {})"



fun guardT_0 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 () (StateConstr s iTest) = (s = Substate.state__S \<and> (True))"

fun expressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"expressionT_0 () (StateConstr s iTest) = {
    (StateConstr Substate.state__T (iTest), [])
}"

fun transitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"transitionTH_0 () (StateConstr s iTest) =
    (if (guardT_0 () (StateConstr s iTest)) then (expressionT_0 () (StateConstr s iTest)) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (EventInput.channels \<times> msg) \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"eventTransition para state (beInChannel_rep, boolEVENTConstr beInChannel_pattern) =
    transitionH_00 para state beInChannel_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (EventOutput.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S (0), [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure EventAutomatonInvariant = struct
  val beInChannel_transitionList = [
    ("", @{term guard_00}, @{term expression_00}, @{term transitionH_00})]
  val tick_transitionList = [
    ("", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0})]
end\<close>

definition Sps :: "unit \<Rightarrow> (EventInput.channels\<^sup>\<Omega> \<rightarrow> EventOutput.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
