theory Event3
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) io.Event3Input io.Event3Output MultipleParameters.MultipleParameters_States
    (* Hwl  *)

begin




fun guard_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_00 () (StateConstr s) beInChannel_pattern = (s = Substate.state__S \<and> (beInChannel_pattern = False))"

fun expression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"expression_00 () (StateConstr s) beInChannel_pattern = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (False))])
}"

fun transitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"transitionH_00 () (StateConstr s) beInChannel_pattern =
    (if (guard_00 () (StateConstr s) beInChannel_pattern) then (expression_00 () (StateConstr s) beInChannel_pattern) else {})"

fun guard_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> bool" where
"guard_01 () (StateConstr s) beInChannel_pattern = (s = Substate.state__S \<and> (beInChannel_pattern = True))"

fun expression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"expression_01 () (StateConstr s) beInChannel_pattern = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (True))])
}"

fun transitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"transitionH_01 () (StateConstr s) beInChannel_pattern =
    (if (guard_01 () (StateConstr s) beInChannel_pattern) then (expression_01 () (StateConstr s) beInChannel_pattern) else {})"



fun guardT_0 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_0 () (StateConstr s) = (s = Substate.state__S \<and> (True))"

fun expressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"expressionT_0 () (StateConstr s) = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (False))])
}"

fun transitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"transitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (expressionT_0 () (StateConstr s)) else {})"

fun guardT_1 :: "unit \<Rightarrow> State \<Rightarrow> bool" where
"guardT_1 () (StateConstr s) = (s = Substate.state__S \<and> (True))"

fun expressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"expressionT_1 () (StateConstr s) = {
    (StateConstr Substate.state__S, [(beOutChannelConstr (True))])
}"

fun transitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"transitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (expressionT_1 () (StateConstr s)) else {})"



fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (Event3Input.channels \<times> msg) \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"eventTransition para state (beInChannel_rep, boolEVENTConstr beInChannel_pattern) =
    transitionH_00 para state beInChannel_pattern \<union>
    transitionH_01 para state beInChannel_pattern" |
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"tickTransition para state =
    transitionTH_0 para state \<union>
    transitionTH_1 para state"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S, [])}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      True
  apply(unfold_locales)
  done

ML \<open>structure Event3 = struct
  val beInChannel_transitionList = [
    ("", @{term guard_00}, @{term expression_00}, @{term transitionH_00}),
    ("", @{term guard_01}, @{term expression_01}, @{term transitionH_01})]
  val tick_transitionList = [
    ("", @{term guardT_0}, @{term expressionT_0}, @{term transitionTH_0}),
    ("", @{term guardT_1}, @{term expressionT_1}, @{term transitionTH_1})]
end\<close>

definition Sps :: "unit \<Rightarrow> (Event3Input.channels\<^sup>\<Omega> \<rightarrow> Event3Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
