theory MultipleInitialStates
  imports
    (* Core *) tscomponent.TsAutomaton tscomponent.TsAutomatonExec tscomponent.TsLocale tscomponent.TsExecLocale stream.StreamCodegen automaton.AREC
    (* Gen  *) io.Input io.Output MultipleInitialStates_States
    (* Hwl  *)

begin



fun guard_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = (s = Substate.state__S \<and> (True))"

fun expression_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"expression_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = {
    (StateConstr Substate.state__S (1) (''Test''), (TSynMsg 10, TSynMsg False, TSynMsg ''TestOutput10''))
}"

fun transitionH_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"transitionH_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) =
(if (guard_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) then (expression_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) else {})"



definition transition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"transition para state input =
    transitionH_0 para state input"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S (-1) (''TestInitValue''), (TSynMsg 1, TSynMsg False, TSynMsg ''TestInitialOutput''))} \<union> {(StateConstr Substate.state__T (-2) (''TestInitValue2''), (TSynMsg 2, TSynMsg False, TSynMsg ''TestInitialOutput2''))}"

interpretation behavior:
    tsStrongGen
      transition
      initialConfigs
      Input.buildSBE
      Output.buildSBE
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)

ML \<open>structure MultipleInitialStates : AUTOMATON = struct
  val transitionList  = [
    ("", @{term guard_0}, @{term expression_0}, @{term transitionH_0})]
end\<close>

definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"



fun executableExpression_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableExpression_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) = [
    (StateConstr Substate.state__S (1) (''Test''), (TSynMsg 10, TSynMsg False, TSynMsg ''TestOutput10''))
]"

fun executableTransitionH_0 :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableTransitionH_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern) =
(if (guard_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) then (executableExpression_0 () (StateConstr s iVar sVar) (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern)) else [])"

definition executableTransition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableTransition para state input =
    executableTransitionH_0 para state input    "

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__S (-1) (''TestInitValue''), (TSynMsg 1, TSynMsg False, TSynMsg ''TestInitialOutput''))] @ [(StateConstr Substate.state__T (-2) (''TestInitValue2''), (TSynMsg 2, TSynMsg False, TSynMsg ''TestInitialOutput2''))]"

global_interpretation executableBehavior:
    tsExecStrongGen
      executableTransition
      executableInitialConfigs
      Input.buildSBE
      Output.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)



end
