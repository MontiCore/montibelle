theory NoTransition
  imports
    (* Core *) tscomponent.TsAutomaton tscomponent.TsAutomatonExec tscomponent.TsLocale tscomponent.TsExecLocale stream.StreamCodegen automaton.AREC
    (* Gen  *) io.Input io.Output NoTransition_States
    (* Hwl  *)

begin



definition transition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"transition para state input = {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) set" where
"initialConfigs  \<equiv> \<lambda> () . {(StateConstr Substate.state__S, (TSynMsg 1, TSynMsg False, TSynMsg ''TestInitialOutput''))}"

interpretation behavior:
    tsStrongGen
      transition
      initialConfigs
      Input.buildSBE
      Output.buildSBE
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)

ML \<open>structure NoTransition : AUTOMATON = struct
  val transitionList  = [
]
end\<close>

definition Sps :: "unit \<Rightarrow> (Input.channels\<^sup>\<Omega> \<rightarrow> Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"



definition executableTransition :: "unit \<Rightarrow> State \<Rightarrow> (nat tsyn \<times> bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableTransition para state input = []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (nat tsyn \<times> bool tsyn \<times> string tsyn)) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__S, (TSynMsg 1, TSynMsg False, TSynMsg ''TestInitialOutput''))]"

global_interpretation executableBehavior:
    tsExecStrongGen
      executableTransition
      executableInitialConfigs
      Input.buildSBE
      Output.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: Input.SBE.c_empty Output.SBE.c_empty)



end
