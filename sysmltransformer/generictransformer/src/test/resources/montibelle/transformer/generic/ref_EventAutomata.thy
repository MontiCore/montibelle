theory def_RefinedAutomaton_States
  imports
    (* Core *) automaton.AREC inc.TryTac
    (* Gen  *) def_RefinedAutomaton_States def_RefinedAutomaton_States    (* Hwl  *)

begin


fun stateInv:: "def_RefinedAutomaton_States.State \<Rightarrow> bool" where
"stateInv (def_RefinedAutomaton_States.StateConstr s S1 S2)
  = True"

fun paramMap:: "unit \<Rightarrow> unit" where
"paramMap () = ()"

fun stateMap :: "def_RefinedAutomaton_States.State \<Rightarrow> def_RefinedAutomaton_States.State" where
"stateMap (def_RefinedAutomaton_States.StateConstr  def_RefinedAutomaton_States.S1  attr)  = def_RefinedAutomaton_States.StateConstr  def_RefinedAutomaton_States.S1  attr"|
"stateMap (def_RefinedAutomaton_States.StateConstr  def_RefinedAutomaton_States.S2  attr)  = def_RefinedAutomaton_States.StateConstr  def_RefinedAutomaton_States.S2  attr"


lemma transition_refine_tick:
  assumes "(nextState, output) \<in> def_RefinedAutomaton_States.tickTransition p state"
    shows "(stateMap nextState, output) \<in> def_RefinedAutomaton_States.tickTransition (paramMap p) (stateMap state)
            \<or> def_RefinedAutomaton_States.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_RefinedAutomaton_States.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_tick:
  assumes "def_RefinedAutomaton_States.tickTransition p state = {}"
    shows "def_RefinedAutomaton_States.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_RefinedAutomaton_States.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> def_RefinedAutomaton_States.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> def_RefinedAutomaton_States.eventTransition (paramMap p) (stateMap state) sbe
            \<or> def_RefinedAutomaton_States.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only:)
  by simp_all?

lemma transition_notempty:
  assumes "def_RefinedAutomaton_States.eventTransition p state sbe = {}"
  shows "def_RefinedAutomaton_States.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only:)
  by simp_all?

lemma initials_refine:
  assumes "initState \<in> def_RefinedAutomaton_States.initialConfigs p"
    shows "apfst stateMap initState \<in> def_RefinedAutomaton_States.initialConfigs (paramMap p)
            \<or> def_RefinedAutomaton_States.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: def_RefinedAutomaton_States.initialConfigs_def def_RefinedAutomaton_States.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "def_RefinedAutomaton_States.initialConfigs p = {}"
    shows "def_RefinedAutomaton_States.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: def_RefinedAutomaton_States.initialConfigs_def def_RefinedAutomaton_States.initialConfigs_def)
  (* autosledgi *) sorry

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (def_RefinedAutomaton_States.behavior.eaut p) state
         \<subseteq> eStateSem (def_RefinedAutomaton_States.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
     apply (simp add: assms)
     (* autosledgi *) sorry

theorem sem_refine: "eSem (def_RefinedAutomaton_States.behavior.eaut p)
                   \<subseteq> eSem (def_RefinedAutomaton_States.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
    apply(rename_tac s; case_tac s; simp add: def_RefinedAutomaton_States.initialConfigs_def def_RefinedAutomaton_States.initialConfigs_def)+
    (* autosledgi *) sorry

theorem refinement[simp]: "def_RefinedAutomaton_States.behavior.Sem p \<subseteq> def_RefinedAutomaton_States.behavior.Sem (paramMap p)"
  apply(simp add: def_RefinedAutomaton_States.behavior.Sem_def def_RefinedAutomaton_States.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
