theory RefinementInvariant
  imports
    (* Core *) automaton.AREC inc.TryTac
    (* Gen  *) EventAutomatonInvariant.EventAutomatonInvariant EventAutomatonInvariant.EventAutomatonInvariant RefinementInvariant_StateMapping RefinementInvariant_ParamMapping RefinementInvariant_StateInv requirement.StateInvariant
    (* Hwl  *)

begin



lemma transition_refine_beInChannel:
  assumes "(nextState, output) \<in> EventAutomatonInvariant.eventTransition p state (beInChannel_rep, boolEVENTConstr sbe)"
    shows "(stateMap nextState, output) \<in> EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe)
            \<or> EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} EventAutomatonInvariant.beInChannel_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_beInChannel:
  assumes "EventAutomatonInvariant.eventTransition p state (beInChannel_rep, boolEVENTConstr sbe) = {}"
    shows "EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) (beInChannel_rep, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} EventAutomatonInvariant.beInChannel_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine_tick:
  assumes "(nextState, output) \<in> EventAutomatonInvariant.tickTransition p state"
    shows "(stateMap nextState, output) \<in> EventAutomatonInvariant.tickTransition (paramMap p) (stateMap state)
            \<or> EventAutomatonInvariant.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} EventAutomatonInvariant.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_tick:
  assumes "EventAutomatonInvariant.tickTransition p state = {}"
    shows "EventAutomatonInvariant.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x1)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} EventAutomatonInvariant.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> EventAutomatonInvariant.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) sbe
            \<or> EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_refine_beInChannel)
  by simp_all?

lemma transition_notempty:
  assumes "EventAutomatonInvariant.eventTransition p state sbe = {}"
  shows "EventAutomatonInvariant.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_notempty_beInChannel)
  by simp_all?

lemma initials_refine:
  assumes "initState \<in> EventAutomatonInvariant.initialConfigs p"
    shows "apfst stateMap initState \<in> EventAutomatonInvariant.initialConfigs (paramMap p)
            \<or> EventAutomatonInvariant.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: EventAutomatonInvariant.initialConfigs_def EventAutomatonInvariant.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "EventAutomatonInvariant.initialConfigs p = {}"
    shows "EventAutomatonInvariant.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: EventAutomatonInvariant.initialConfigs_def EventAutomatonInvariant.initialConfigs_def)
  (* autosledgi *) sorry

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (EventAutomatonInvariant.behavior.eaut p) state
         \<subseteq> eStateSem (EventAutomatonInvariant.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
     apply (simp add: assms)
     (* autosledgi *) sorry

theorem sem_refine: "eSem (EventAutomatonInvariant.behavior.eaut p)
                   \<subseteq> eSem (EventAutomatonInvariant.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
    apply(rename_tac s; case_tac s; simp add: EventAutomatonInvariant.initialConfigs_def EventAutomatonInvariant.initialConfigs_def)+
    (* autosledgi *) sorry

theorem refinement[simp]: "EventAutomatonInvariant.behavior.Sem p \<subseteq> EventAutomatonInvariant.behavior.Sem (paramMap p)"
  apply(simp add: EventAutomatonInvariant.behavior.Sem_def EventAutomatonInvariant.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
