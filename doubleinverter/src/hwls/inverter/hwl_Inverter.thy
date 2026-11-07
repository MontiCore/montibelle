theory hwl_Inverter
  imports sps_LlrInverter.def_LlrInverter sps_HlrInverter.def_HlrInverter
          automaton.Nda2DaSet
begin

definition daset::"(State \<times> (def_HlrInverter_Input.channels msgWithChan event stream \<rightarrow> def_HlrInverter_Output.channels\<^sup>\<Omega>), def_HlrInverter_Input.channels msgWithChan event, def_HlrInverter_Output.channels\<^sup>\<Omega>) dAutomaton set" where
  "daset = nda2daset (behavior.eaut ())"

lemma usplit_step: "(uSplit\<cdot>(\<up>(Event (channel_BooleanInput_val_output_valConstr b)) \<bullet> s)) = 
    def_HlrInverter_Output.sbsetter\<cdot>(\<up>(Event b)) \<bullet>\<bullet> (uSplit\<cdot>s)"
  apply(rule sb_rep_eqI)
  apply(subst demerge_estep_rep[where cs=channel_output_val and m="boolEVENTConstr b"])
  apply(simp_all add: channel_BooleanInput_val_output_valConstr.rep_eq)
  apply(case_tac c,simp_all)
  by(simp add: conc_sb_def repsb_sbconc def_HlrInverter_Output.buildSB_def)

lemma behavior_trans:
  assumes "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr b)"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S) (Event a)) = 
      {(StateConstr state__S,
        def_HlrInverter_Output.sbsetter\<cdot>(\<up>(Event (HOL.Not b))))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms apply(simp)
  using usplit_step[where s=\<epsilon>] by(simp)

lemma da_trans_fst:
  assumes "da \<in> daset"
  and "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr b)"
  shows "\<exists>bar. fst (dautTransition da (StateConstr state__S, foo) (Event a)) =
    (StateConstr state__S, bar)"
proof(-)
  have "fst (apfst fst (dautTransition da (StateConstr state__S, foo) (Event a))) = StateConstr state__S"
    using assms daset_def behavior_trans nda2da_trans
    by(metis (no_types, lifting) prod.collapse prod.inject singletonD)
  then show ?thesis
    by(metis fst_apfst prod.exhaust_sel)
qed

lemma da_trans_snd:
  assumes "da \<in> daset"
  and "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr b)"
shows "snd (dautTransition da (StateConstr state__S, foo) (Event a)) =
    def_HlrInverter_Output.sbsetter\<cdot>(\<up>(Event (HOL.Not b)))"
  using assms daset_def behavior_trans nda2da_trans_snd by fastforce

lemma sbsetter_ticksb: "def_HlrInverter_Output.sbsetter\<cdot>(\<up>Tick) = ticksb"
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by(case_tac c;simp add: def_HlrInverter_Output.buildSB_def)

lemma da_trans_tick:
  assumes "da \<in> daset"
shows "\<exists>bar. dautTransition da (StateConstr state__S, foo) Tick =
  ((StateConstr state__S, bar), ticksb)"
proof(-)
  have "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S) Tick) = 
      {(StateConstr state__S, ticksb)}"
    apply(simp add: behavior.transition_def)
    by(simp add: EventLocale.outconv_def behavior.ndaTransition_tickC_def)
  then have "apfst fst (dautTransition da (StateConstr state__S, foo) Tick) =
       (StateConstr state__S, ticksb)"
    using assms daset_def nda2da_trans by fastforce
  then show ?thesis
    by(metis (no_types, lifting) fst_apfst fst_eqD prod.collapse snd_apfst snd_conv)
qed

lemma da_statesem_tick:
  assumes "da \<in> daset"
  shows "\<exists>bar. daStateSem stream_split da (StateConstr state__S, foo)\<cdot>(\<up>Tick \<bullet> s) =
        ticksb \<bullet>\<bullet> daStateSem stream_split da (StateConstr state__S, bar)\<cdot>s"
proof(-)
  obtain bar where bar_def: "dautTransition da (StateConstr state__S, foo) Tick =
  ((StateConstr state__S, bar), ticksb)"
    using assms da_trans_tick by blast
  then show ?thesis
    apply(subst dastatesem_step)
    by(auto)
qed

definition inputf::"def_HlrInverter_Input.channels msgWithChan list \<Rightarrow> bool list" where
 "inputf = (\<lambda>ls. map ((inv boolEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_input_val) (map Rep_msgWithChan ls)))"

lemma [simp]: "inputf [] = []"
  by(simp add: inputf_def)

lemma [simp]:
  assumes "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr b)"
  shows "inputf (a#ls) = b # inputf ls"
  by(simp add: assms inputf_def)

lemma inverts_slice:
  assumes "da \<in> daset"
  shows "\<exists>bar. multTransitionsInOne da (StateConstr state__S, foo) (map Event ls) =
   ((StateConstr state__S, bar),
     def_HlrInverter_Output.sbsetter\<cdot>(smap Event\<cdot>(<(map HOL.Not (inputf ls))>)))"
  apply(insert assms)
proof(induction ls arbitrary: da foo)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)

  obtain b where b_def: "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr b)"
    by (meson eventTransition.elims)

  then have "\<exists>bar. fst (dautTransition da (StateConstr state__S, foo) (Event a)) =
    (StateConstr state__S, bar)"
    using Cons.prems da_trans_fst by blast
  then obtain bar where bar_def: "fst (dautTransition da (StateConstr state__S, foo) (Event a)) =
    (StateConstr state__S, bar)"
    by blast

  obtain bar2 where bar2_def: "multTransitionsInOne da (StateConstr state__S, bar) (map Event ls) =
     ((StateConstr state__S, bar2), def_HlrInverter_Output.sbsetter\<cdot>(smap Event\<cdot>(<(map HOL.Not (inputf ls))>)))"
    using Cons.prems Cons.IH by blast

  show ?case
    using Cons.prems b_def apply(simp add: da_trans_snd bar_def bar2_def)
    by(simp add: conc_sb_def setter_conc2sbconc[symmetric])
qed

lemma inverts_step:
  assumes "#\<^sub>\<surd>i = \<infinity>"
  and "da \<in> daset"
shows "snthTs t\<cdot>(def_HlrInverter_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__S, foo)\<cdot>i)) =
    smap HOL.Not\<cdot>((smap (inv boolEVENTConstr)\<cdot>(smap snd\<cdot>
         ({m. fst m = channel_input_val} \<ominus> smap Rep_msgWithChan\<cdot>(snthTs t\<cdot>i)))))"
  apply(insert assms)
proof(induction t arbitrary: i da foo)
  case 0

  have input_eq: "<(inputf (s2list (shdTs\<cdot>i)))> = (smap (inv boolEVENTConstr)\<cdot>
     (smap snd\<cdot>({m. fst m = channel_input_val} \<ominus> smap Rep_msgWithChan\<cdot>(shdTs\<cdot>i))))"
    apply(simp add: inputf_def)
    apply(subst(2) s2list_id[where stream="shdTs\<cdot>i", symmetric])
    apply(metis "0.prems"(1) Inf'_neq_0_rev shdts_len tlentosvalues)
    by(metis (no_types, lifting) sfilter2filter map2smap smapsmap2smap)

  obtain bar where bar_def: "multTransitionsInOne da (StateConstr state__S, foo) (map Event (s2list (shdTs\<cdot>i))) =
     ((StateConstr state__S, bar), def_HlrInverter_Output.sbsetter\<cdot>(smap Event\<cdot>(<(map HOL.Not (inputf (s2list (shdTs\<cdot>i))))>)))"
    using "0.prems" inverts_slice by blast

  obtain bar2 where bar2_def: "daStateSem stream_split da (StateConstr state__S, bar)\<cdot>(\<up>Tick \<bullet> srtTs\<cdot>i) =
        ticksb \<bullet>\<bullet> daStateSem stream_split da (StateConstr state__S, bar2)\<cdot>(srtTs\<cdot>i)"
    using "0.prems" da_statesem_tick by blast

  show ?case
    apply(subst s_split_list[where s=i])
    apply(metis "0.prems"(1) Inf'_neq_0 tlentosvalues)
    apply(subst(2) s_split_list[where s=i])
    apply(metis "0.prems"(1) Inf'_neq_0 tlentosvalues)
    apply(simp)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps, simp add: case_prod_beta conc_sb_def)
    apply(simp add: bar_def bar2_def)
    apply(simp add: conc_sb_def getter_conc2sbconc[symmetric] sbsetter_ticksb[symmetric])
    apply(subst shdts_split_eq, simp_all)
    by(simp add: smaps2smap input_eq)
next
  case (Suc t)

  obtain bar where bar_def: "multTransitionsInOne da (StateConstr state__S, foo) (map Event (s2list (shdTs\<cdot>i))) =
     ((StateConstr state__S, bar), def_HlrInverter_Output.sbsetter\<cdot>(smap Event\<cdot>(<(map HOL.Not (inputf (s2list (shdTs\<cdot>i))))>)))"
    using Suc.prems inverts_slice by blast

  obtain bar2 where bar2_def: "daStateSem stream_split da (StateConstr state__S, bar)\<cdot>(\<up>Tick \<bullet> srtTs\<cdot>i) =
        ticksb \<bullet>\<bullet> daStateSem stream_split da (StateConstr state__S, bar2)\<cdot>(srtTs\<cdot>i)"
    using Suc.prems da_statesem_tick by blast
  
  show ?case
    apply(subst s_split_list[where s=i])
    apply(metis Suc.prems(1) Inf'_neq_0 tlentosvalues)
    apply(subst(3) s_split_list[where s=i])
    apply(metis Suc.prems(1) Inf'_neq_0 tlentosvalues)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps, simp add: case_prod_beta conc_sb_def)
    apply(simp add: bar_def bar2_def)
    apply(simp add: conc_sb_def getter_conc2sbconc[symmetric] sbsetter_ticksb[symmetric])
    apply(subst snthts_dropfst, simp_all)+
    apply(rule Suc.IH)
    apply(metis (no_types, opaque_lifting) Suc.prems(1) antisym_conv3 inf_great linorder_not_less ln_less lnsuc_lnle_emb srtts_tlen_leq)
    by(simp add: Suc.prems)
qed

lemma inverts:
  assumes "sb = def_HlrInverter_Input.sbsetter\<cdot>input"
  and "wellformed sb"
  and "#sb = \<infinity>"
  and "spf \<in> def_LlrInverter.Sps ()"
shows "snthTs t\<cdot>(def_HlrInverter_Output.sbgetter\<cdot>(spf\<cdot>sb)) =
       smap HOL.Not\<cdot>(snthTs t\<cdot>(def_HlrInverter_Input.sbgetter\<cdot>sb))"
  using assms apply(simp add: def_LlrInverter.Sps_def behavior.Sem_def)
proof(rule bundlemergepred[where SPS="eSem (behavior.eaut ())"];simp)
  fix i and g
  assume a1: "sb = def_HlrInverter_Input.sbsetter\<cdot>input"
  assume a2: "wellformed (def_HlrInverter_Input.sbsetter\<cdot>input)"
  assume a3: "#input = \<infinity>"
  assume a4: "spf \<in> mergeTimed \<then> eSem (behavior.eaut ())"
  assume a5: "g \<in> eSem (behavior.eaut ())"
  assume a6: "uSplit\<cdot>i \<sqsubseteq> def_HlrInverter_Input.sbsetter\<cdot>input"
  assume a7: "#\<^sub>\<surd> input = #\<^sub>\<surd> i"
  
  have i_inf: "#\<^sub>\<surd> i = \<infinity>"
    by(metis a1 a7 assms(2) assms(3) def_HlrInverter_Input.SB.setter_tlen somechannotempty well_tlen)

  have input_eq:
    "\<forall>t. (snthTs t\<cdot>input) = (smap (inv boolEVENTConstr)\<cdot>(smap snd\<cdot>
           ({m. fst m = channel_input_val} \<ominus> smap Rep_msgWithChan\<cdot>(snthTs t\<cdot>i))))"
    apply(subst ssplit_snthts_eq[where sb="def_HlrInverter_Input.sbsetter\<cdot>input"])
    apply(simp_all add: a6 i_inf smap_snthts def_HlrInverter_Input.buildSB_def)
    apply(subgoal_tac "input = (emap (inv boolEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>
      (smap (Timed \<circ> TLive \<circ> map_event boolEVENTConstr)\<cdot>input)))", simp)
    apply(induction input;simp)
    by(case_tac a;simp)

  have "g \<in> daSem stream_split ` daset"
    using a5 apply(simp add: eSem_def)
    apply(subst(asm) nda2daset[where conv=sup'])
    apply(simp_all add: daset_def)
    using stream_split_eps streamind by blast
    
  then obtain da where da_def: "da \<in> daset \<and> g = daSem stream_split da"
    using a5 by blast

  obtain foo where foo_def: "foo = fst (apfst snd (dautInitConfig da))"
    by blast

  have "autInitConfig\<cdot>(behavior.eaut ()) = {(StateConstr state__S, \<bottom>)}"
    apply(simp add: behavior.config_def)
    by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)
  then have "apfst fst (dautInitConfig da) = (StateConstr state__S, \<bottom>)"
    using daset_def da_def nda2da_init by blast
  then have da_init: "(dautInitConfig da) = ((StateConstr state__S, foo), \<bottom>)"
    by(metis foo_def fst_apfst fst_conv prod.collapse snd_apfst snd_conv)

  show "snthTs t\<cdot>(def_HlrInverter_Output.sbgetter\<cdot>(g\<cdot>i)) = smap HOL.Not\<cdot>(snthTs t\<cdot>input)"
    apply(simp add: da_def dasem_unfold da_init)
    apply(subst inverts_step)
    by(simp_all add: i_inf da_def input_eq)
qed

lemma wellformed_isetter:
assumes "wellformed input"
shows "wellformed (def_HlrInverter_Input.sbsetter\<cdot>(input))"
  apply(auto simp add: wellformed_sb_def)
  apply(case_tac c)
  using assms apply(simp add: wellformed_stream_def)
  by(metis(full_types) def_HlrInverter_Input.SB.c_lenex def_HlrInverter_Input.SB.c_tlenex
     def_HlrInverter_Input.channels.exhaust def_HlrInverter_Input.channels_chdom empty_not_insert)

lemma refinement[simp]: "def_LlrInverter.Sps () \<subseteq> def_HlrInverter.Sps ()"
  apply(subst def_HlrInverter.Sps_def)
  apply(subgoal_tac "\<And>spf sb. spf \<in> def_LlrInverter.Sps () \<Longrightarrow> wholePredicate () (def_HlrInverter_Input.sbgetter\<cdot>sb) (def_HlrInverter_Output.sbgetter\<cdot>(spf\<cdot>sb))")
  apply(simp add: Nitpick.case_unit_unfold subsetI) 
  apply(simp add: wholePredicate_def assumption_0_def predicate_0_def causality_def weakpred_def
    len_stream_def[symmetric] DefinitionOfNot.Not_def)
  apply(auto)
  using inverts apply(metis def_HlrInverter_Input.SB.set_get wellformed_isetter)
  by (metis a def_LlrInverter.Sps_def eventGen.sem_weak weak_def)

end