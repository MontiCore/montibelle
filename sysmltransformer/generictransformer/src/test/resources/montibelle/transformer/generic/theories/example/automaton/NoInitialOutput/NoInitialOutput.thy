theory NoInitialOutput
  imports
    (* Core *) tscomponent.TsAutomaton tscomponent.TsAutomatonExec tscomponent.TsLocale tscomponent.TsExecLocale stream.StreamCodegen automaton.AREC
    (* Gen  *) io.Input io.Output NoInitialOutput_States
    (* Hwl  *)

begin



fun guard_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = (s = Substate.state__S \<and> (True))"

fun expression_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"expression_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = {
    (StateConstr Substate.state__T, (TSynMsg 11, TSynMsg False, TSynMsg ''TestOutput11''))
}"

fun transitionH_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"transitionH_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) =
(if (guard_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) then (expression_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) else {})"



definition transition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"transition para state input =
    transitionH_0 para state input"

definition initialStates :: "unit \<Rightarrow> State set" where
"initialStates \<equiv> \<lambda> (). {StateConstr Substate.state__S}    "

interpretation behavior:
    tsWeakGen
      transition
      initialStates
      Input.buildSBE
      Output.buildSBE
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)

ML \<open>structure NoInitialOutput : AUTOMATON = struct
  val transitionList  = [
    ("", @{term guard_0}, @{term expression_0}, @{term transitionH_0})]
end\<close>

definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"



fun executableExpression_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableExpression_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = [
    (StateConstr Substate.state__T, (TSynMsg 11, TSynMsg False, TSynMsg ''TestOutput11''))
]"

fun executableTransitionH_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableTransitionH_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) =
(if (guard_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) then (executableExpression_0 () (StateConstr s) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) else [])"

definition executableTransition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableTransition para state input =
    executableTransitionH_0 para state input    "

definition executableInitialStates :: "unit \<Rightarrow> State list" where
"executableInitialStates \<equiv> \<lambda> (). [StateConstr Substate.state__S]        "

global_interpretation executableBehavior:
    tsExecWeakGen
      executableTransition
      executableInitialStates
      Input.buildSBE
      Output.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)



end
