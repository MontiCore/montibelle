theory TimesliceAutomatonRefinement
  imports
    (* Gen *) MultipleInitialStates.MultipleInitialStates MultipleInitialStates.MultipleInitialStates TimesliceAutomatonRefinement_StateMapping TimesliceAutomatonRefinement_ParamMapping TimesliceAutomatonRefinement_StateInv
    (* Hwl  *)

begin



lemma transition_refine:
  assumes "(nextState, output) \<in> MultipleInitialStates.transition p state sbe"
    shows "(stateMap nextState, output) \<in> MultipleInitialStates.transition (paramMap p) (stateMap state) sbe
            \<or> MultipleInitialStates.transition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  unfolding MultipleInitialStates.transition_def
  apply(cases state; (cases p)?; (cases sbe)?; (case_tac x1)?)
  apply auto
  unfolding MultipleInitialStates.transition_def
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} MultipleInitialStates.transitionList) @{context}\<close>)
  (* autosledgi *) sorry

lemma transition_notempty:
  assumes "MultipleInitialStates.transition p state sbe = {}"
    shows "MultipleInitialStates.transition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  unfolding  MultipleInitialStates.transition_def
  apply(cases state) apply(cases p)? apply(cases sbe)?
  apply auto
  unfolding MultipleInitialStates.transition_def
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} MultipleInitialStates.transitionList) @{context}\<close>)
  (* autosledgi *) sorry

lemma initials_refine:
  assumes "initState \<in> MultipleInitialStates.initialConfigs p"
    shows "apfst stateMap initState \<in> MultipleInitialStates.initialConfigs (paramMap p)
            \<or> MultipleInitialStates.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: MultipleInitialStates.initialConfigs_def MultipleInitialStates.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "MultipleInitialStates.initialConfigs p = {}"
  shows "MultipleInitialStates.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: MultipleInitialStates.initialConfigs_def MultipleInitialStates.initialConfigs_def)
  (* autosledgi *) sorry


lemma statesem_refine: "MultipleInitialStates.behavior.StateSem p state
                      \<subseteq> MultipleInitialStates.behavior.StateSem (paramMap p) (stateMap state)"
  apply(rule ndastaterefine_inv__ndagen[where Inv="stateInv" and f="stateMap" and g="paramMap"])
  apply(simp_all only: transition_refine transition_notempty)
  apply(simp_all only: MultipleInitialStates.behavior.tsGen_axioms MultipleInitialStates.behavior.tsGen_axioms)
  apply(case_tac "nextState::MultipleInitialStates_States.State")
  (* autosledgi *) sorry

theorem sem_refine: "ndaSem (MultipleInitialStates.behavior.nda p)
                   \<subseteq> ndaSem (MultipleInitialStates.behavior.nda (paramMap p))"
  apply(rule ndastaterefineinv_ndagen_sem [where Inv="stateInv" and f="stateMap" and g="paramMap"])
  apply(simp_all only: initials_refine statesem_refine initials_notempty)
  apply(simp_all only: MultipleInitialStates.behavior.tsGen_axioms MultipleInitialStates.behavior.tsGen_axioms)
  (* autosledgi *) sorry

lemma refinement[simp]: "MultipleInitialStates.behavior.Sem p \<subseteq> MultipleInitialStates.behavior.Sem (paramMap p)"
  apply(simp add: MultipleInitialStates.behavior.nda_def MultipleInitialStates.behavior.nda_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
