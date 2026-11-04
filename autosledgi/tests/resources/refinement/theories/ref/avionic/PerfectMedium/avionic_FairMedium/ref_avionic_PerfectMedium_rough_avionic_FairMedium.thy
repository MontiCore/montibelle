theory ref_avionic_PerfectMedium_rough_avionic_FairMedium
  imports (* Core *) automaton.AREC inc.TryTac
           (* Gen *) sps_avionic_FairMedium.def_avionic_FairMedium sps_avionic_PerfectMedium.def_avionic_PerfectMedium ref_avionic_PerfectMedium_rough_avionic_FairMedium_StateMapping
           (* Hwl *) 

begin



fun paramMap:: "unit \<Rightarrow> unit" where
"paramMap () = ()"

lemma transition_refine_channel_avionic_Booleans_val_i_val:
  assumes "(nextState, output) \<in> def_avionic_PerfectMedium.eventTransition p state (channel_i_val, boolEVENTConstr sbe)"
    shows "(stateMap nextState, output) \<in> def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) (channel_i_val, boolEVENTConstr sbe)
            \<or> def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) (channel_i_val, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} def_avionic_FairMedium.channel_avionic_Booleans_val_i_val_transitionList) @{context}\<close>)
  apply trytac?
  (*autosledgi*) sorry

lemma transition_notempty_channel_avionic_Booleans_val_i_val:
  assumes "def_avionic_PerfectMedium.eventTransition p state (channel_i_val, boolEVENTConstr sbe) = {}"
    shows "def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) (channel_i_val, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} def_avionic_FairMedium.channel_avionic_Booleans_val_i_val_transitionList) @{context}\<close>)
  apply trytac?
  (*autosledgi*) sorry

lemma transition_refine_tick:
  assumes "(nextState, output) \<in> def_avionic_PerfectMedium.tickTransition p state"
    shows "(stateMap nextState, output) \<in> def_avionic_FairMedium.tickTransition (paramMap p) (stateMap state)
            \<or> def_avionic_FairMedium.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_avionic_FairMedium.tick_transitionList) @{context}\<close>)
  apply trytac?
  (*autosledgi*) sorry

lemma transition_notempty_tick:
  assumes "def_avionic_PerfectMedium.tickTransition p state = {}"
    shows "def_avionic_FairMedium.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_avionic_FairMedium.tick_transitionList) @{context}\<close>)
  apply trytac?
  (*autosledgi*) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> def_avionic_PerfectMedium.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) sbe
            \<or> def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_refine_channel_avionic_Booleans_val_i_val)
  by simp_all?

lemma transition_notempty:
  assumes "def_avionic_PerfectMedium.eventTransition p state sbe = {}"
  shows "def_avionic_FairMedium.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_notempty_channel_avionic_Booleans_val_i_val)
  by simp_all?

lemma initials_refine:
  assumes "(initState, initOut) \<in> def_avionic_PerfectMedium.initialConfigs p"
    shows "(stateMap initState, initOut) \<in> def_avionic_FairMedium.initialConfigs (paramMap p)
            \<or> def_avionic_FairMedium.initialConfigs (paramMap p) = {}"
  using assms apply(auto simp add: def_avionic_PerfectMedium.initialConfigs_def def_avionic_FairMedium.initialConfigs_def)
  (*autosledgi*) sorry

lemma initials_notempty:
  assumes "def_avionic_PerfectMedium.initialConfigs p = {}"
  shows "def_avionic_FairMedium.initialConfigs (paramMap p) = {}"
  using assms apply(auto simp add: def_avionic_PerfectMedium.initialConfigs_def def_avionic_FairMedium.initialConfigs_def)
  (*autosledgi*) sorry

fun stateInv:: "def_avionic_PerfectMedium_States.State \<Rightarrow> bool" where
"stateInv (def_avionic_PerfectMedium_States.StateConstr _) = True"

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (def_avionic_PerfectMedium.behavior.eaut p) state
         \<subseteq> eStateSem (def_avionic_FairMedium.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
      apply(cases state; simp)
     by(case_tac nextState, simp)+

theorem sem_refine: "eSem (def_avionic_PerfectMedium.behavior.eaut p)
                   \<subseteq> eSem (def_avionic_FairMedium.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
   by(rename_tac s; case_tac s; simp add: def_avionic_PerfectMedium.initialConfigs_def)+

theorem refinement[simp]: "def_avionic_PerfectMedium.behavior.Sem p \<subseteq> def_avionic_FairMedium.behavior.Sem (paramMap p)"
  apply(simp add: def_avionic_PerfectMedium.behavior.Sem_def def_avionic_FairMedium.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
