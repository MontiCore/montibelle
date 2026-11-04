theory ref_Inverter_LLR2_rough_Inverter_LLR1
  imports
    (* Core *) automaton.AREC inc.TryTac
    (* Gen  *) sps_Inverter_LLR1.def_Inverter_LLR1 sps_Inverter_LLR2.def_Inverter_LLR2    (* Hwl  *)

begin


fun stateInv:: "def_Inverter_LLR2_States.State \<Rightarrow> bool" where
"stateInv (def_Inverter_LLR2_States.StateConstr s)
  = True"

fun paramMap:: "unit \<Rightarrow> unit" where
"paramMap () = ()"

fun stateMap :: "def_Inverter_LLR2_States.State \<Rightarrow> def_Inverter_LLR1_States.State" where
"stateMap (def_Inverter_LLR2_States.StateConstr  def_Inverter_LLR2_States.state__S  )  = def_Inverter_LLR1_States.StateConstr  def_Inverter_LLR1_States.state__S  "


lemma transition_refine_channel_Inverter_HLR1_input_val:
  assumes "(nextState, output) \<in> def_Inverter_LLR2.eventTransition p state (channel_input_val, boolEVENTConstr sbe)"
    shows "(stateMap nextState, output) \<in> def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) (channel_input_val, boolEVENTConstr sbe)
            \<or> def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) (channel_input_val, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} def_Inverter_LLR1.channel_Inverter_HLR1_input_val_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_channel_Inverter_HLR1_input_val:
  assumes "def_Inverter_LLR2.eventTransition p state (channel_input_val, boolEVENTConstr sbe) = {}"
    shows "def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) (channel_input_val, boolEVENTConstr sbe) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} def_Inverter_LLR1.channel_Inverter_HLR1_input_val_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine_tick:
  assumes "(nextState, output) \<in> def_Inverter_LLR2.tickTransition p state"
    shows "(stateMap nextState, output) \<in> def_Inverter_LLR1.tickTransition (paramMap p) (stateMap state)
            \<or> def_Inverter_LLR1.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_Inverter_LLR1.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_tick:
  assumes "def_Inverter_LLR2.tickTransition p state = {}"
    shows "def_Inverter_LLR1.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)
  apply(cases p)?
  apply(case_tac x)?
  apply auto
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} def_Inverter_LLR1.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> def_Inverter_LLR2.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) sbe
            \<or> def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_refine_channel_Inverter_HLR1_input_val)
  by simp_all?

lemma transition_notempty:
  assumes "def_Inverter_LLR2.eventTransition p state sbe = {}"
  shows "def_Inverter_LLR1.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only: transition_notempty_channel_Inverter_HLR1_input_val)
  by simp_all?

lemma initials_refine:
  assumes "initState \<in> def_Inverter_LLR2.initialConfigs p"
    shows "apfst stateMap initState \<in> def_Inverter_LLR1.initialConfigs (paramMap p)
            \<or> def_Inverter_LLR1.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: def_Inverter_LLR2.initialConfigs_def def_Inverter_LLR1.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "def_Inverter_LLR2.initialConfigs p = {}"
    shows "def_Inverter_LLR1.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: def_Inverter_LLR2.initialConfigs_def def_Inverter_LLR1.initialConfigs_def)
  (* autosledgi *) sorry

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (def_Inverter_LLR2.behavior.eaut p) state
         \<subseteq> eStateSem (def_Inverter_LLR1.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
     apply (simp add: assms)
     (* autosledgi *) sorry

theorem sem_refine: "eSem (def_Inverter_LLR2.behavior.eaut p)
                   \<subseteq> eSem (def_Inverter_LLR1.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
    apply(rename_tac s; case_tac s; simp add: def_Inverter_LLR1.initialConfigs_def def_Inverter_LLR2.initialConfigs_def)+
    (* autosledgi *) sorry

theorem refinement[simp]: "def_Inverter_LLR2.behavior.Sem p \<subseteq> def_Inverter_LLR1.behavior.Sem (paramMap p)"
  apply(simp add: def_Inverter_LLR2.behavior.Sem_def def_Inverter_LLR1.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
