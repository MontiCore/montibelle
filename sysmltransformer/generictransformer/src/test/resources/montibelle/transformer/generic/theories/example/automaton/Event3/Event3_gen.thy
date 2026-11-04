theory Event3_gen
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) Event3 io.Event3Input_gen io.Event3Output_gen io.Event3Input io.Event3Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s) beInChannel_pattern = [(StateConstr Substate.state__S, [(beOutChannelConstr (False))])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s) beInChannel_pattern =
    (if (guard_00 () (StateConstr s) beInChannel_pattern) then (executableExpression_00 () (StateConstr s) beInChannel_pattern) else [])"

fun executableExpression_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableExpression_01 () (StateConstr s) beInChannel_pattern = [(StateConstr Substate.state__S, [(beOutChannelConstr (True))])]"

fun executableTransitionH_01 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableTransitionH_01 () (StateConstr s) beInChannel_pattern =
    (if (guard_01 () (StateConstr s) beInChannel_pattern) then (executableExpression_01 () (StateConstr s) beInChannel_pattern) else [])"



fun executableExpressionT_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableExpressionT_0 () (StateConstr s) = [(StateConstr Substate.state__S, [(beOutChannelConstr (False))])]"

fun executableTransitionTH_0 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableTransitionTH_0 () (StateConstr s) =
    (if (guardT_0 () (StateConstr s)) then (executableExpressionT_0 () (StateConstr s)) else [])"

fun executableExpressionT_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableExpressionT_1 () (StateConstr s) = [(StateConstr Substate.state__S, [(beOutChannelConstr (True))])]"

fun executableTransitionTH_1 :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableTransitionTH_1 () (StateConstr s) =
    (if (guardT_1 () (StateConstr s)) then (executableExpressionT_1 () (StateConstr s)) else [])"



fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (Event3Input.channels \<times> msg) \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableEventTransition para state (beInChannel_rep, boolEVENTConstr beInChannel_pattern) =
    executableTransitionH_00 para state beInChannel_pattern @
    executableTransitionH_01 para state beInChannel_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
    executableTransitionTH_0 para state @
    executableTransitionTH_1 para state"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (Event3Output.channels msgWithChan) list) list" where
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



fun sb2stream::"Event3Output.channels\<^sup>\<Omega> \<Rightarrow> (bool event stream \<times> nat event stream \<times> string event stream)" where
"sb2stream a = Event3Output.sbgetter\<cdot>a"

export_code "execsem" "Event3Input.sbsetter" "sb2stream" in Scala module_name Event3_scalaExec file_prefix "Event3_scalaExec" (case_insensitive)


end
