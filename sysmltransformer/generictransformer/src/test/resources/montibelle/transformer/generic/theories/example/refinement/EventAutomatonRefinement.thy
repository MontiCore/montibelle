theory EventAutomatonRefinement
  imports
    (* Core *) automaton.AREC inc.TryTac
    (* Gen  *) Event.Event Event.Event EventAutomatonRefinement_StateMapping EventAutomatonRefinement_ParamMapping EventAutomatonRefinement_StateInv
    (* Hwl  *)

begin



lemma transition_refine_beInChannel:
  assumes "(nextState, output) \<in> Event.eventTransition p state (beInChannel_rep, boolEVENTConstr sbe)"
    shows "(stateMap nextState, output) \<in> Event.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe)
            \<or> Event.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} Event.beInChannel_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_beInChannel:
  assumes "Event.eventTransition p state (beInChannel_rep, boolEVENTConstr sbe) = {}"
    shows "Event.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} Event.beInChannel_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine_tick:
  assumes "(nextState, output) \<in> Event.tickTransition p state"
    shows "(stateMap nextState, output) \<in> Event.tickTransition (paramMap p) (stateMap state)
            \<or> Event.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} Event.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_tick:
  assumes "Event.tickTransition p state = {}"
    shows "Event.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} Event.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> Event.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> Event.eventTransition (paramMap p) (stateMap state) sbe
            \<or> Event.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_refine_beInChannel)
  by simp_all?

lemma transition_notempty:
  assumes "Event.eventTransition p state sbe = {}"
  shows "Event.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_notempty_beInChannel)
  by simp_all?

lemma initials_refine:
  assumes "initState \<in> Event.initialConfigs p"
    shows "apfst stateMap initState \<in> Event.initialConfigs (paramMap p)
            \<or> Event.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: Event.initialConfigs_def Event.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "Event.initialConfigs p = {}"
    shows "Event.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: Event.initialConfigs_def Event.initialConfigs_def)
  (* autosledgi *) sorry

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (Event.behavior.eaut p) state
         \<subseteq> eStateSem (Event.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
     apply (simp add: assms)
     (* autosledgi *) sorry

theorem sem_refine: "eSem (Event.behavior.eaut p)
                   \<subseteq> eSem (Event.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
    apply(rename_tac s; case_tac s; simp add: Event.initialConfigs_def Event.initialConfigs_def)+
    (* autosledgi *) sorry

theorem refinement[simp]: "Event.behavior.Sem p \<subseteq> Event.behavior.Sem (paramMap p)"
  apply(simp add: Event.behavior.Sem_def Event.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
