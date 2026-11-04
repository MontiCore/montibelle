theory ref_Inverter_LLR1_rough_Inverter_HLR2
  imports
    (* Gen *) Smart_Isabelle.Smart_Isabelle
              sps_Inverter_HLR2.def_Inverter_HLR2 sps_Inverter_LLR1.def_Inverter_LLR1
    (* Hwl  *)

begin

declare [[names_short = false]]



(* channel lemmas *)

lemma[simp]:"def_Inverter_HLR1_Input.buildSB (channel_input_val_pattern) channel_input_val = (Rep_cfun (smap (Timed o TLive o map_event boolEVENTConstr))) channel_input_val_pattern"
  by(simp add: def_Inverter_HLR1_Input.buildSB_def)

lemma[simp]:"def_Inverter_HLR1_Output.buildSB (channel_output_val_pattern) channel_output_val = (Rep_cfun (smap (Timed o TLive o map_event boolEVENTConstr))) channel_output_val_pattern"
  by(simp add: def_Inverter_HLR1_Output.buildSB_def)

lemma channel_input_val_imp_bool:
  assumes "fst (Rep_msgWithChan a) = channel_input_val"
  shows "\<exists>m. Rep_msgWithChan a = (channel_input_val, boolEVENTConstr m)"
  by(metis msg.exhaust assms prod.collapse)

lemma channel_output_val_imp_bool:
  assumes "fst (Rep_msgWithChan a) = channel_output_val"
  shows "\<exists>m. Rep_msgWithChan a = (channel_output_val, boolEVENTConstr m)"
  by(metis msg.exhaust assms prod.collapse)


(* input channel abbreviations *)

abbreviation channel_input_valAbbr::"def_Inverter_HLR1_Input.channels\<^sup>\<Omega> \<Rightarrow> bool event stream" where
  "channel_input_valAbbr sb \<equiv> (def_Inverter_HLR1_Input.sbgetter\<cdot>sb)"

abbreviation channel_input_val_efilter::"def_Inverter_HLR1_Input.channels msgWithChan event stream \<rightarrow> bool event stream" where
  "channel_input_val_efilter \<equiv> (emap (inv boolEVENTConstr)) oo (eventFilter channel_input_val)"

definition channel_input_val_sfilter::"def_Inverter_HLR1_Input.channels msgWithChan stream \<Rightarrow> bool stream" where
  "channel_input_val_sfilter s = smap (inv boolEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_input_val} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition channel_input_valf::"def_Inverter_HLR1_Input.channels msgWithChan list \<Rightarrow> bool list" where
  "channel_input_valf = (\<lambda>ls. map ((inv boolEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_input_val) (map Rep_msgWithChan ls)))"


(* lemmas over abbreviations *)

lemma channel_input_valf_empty[simp]:"channel_input_valf [] = []"
  by(simp add: channel_input_valf_def)

lemma channel_input_valf_channel_input_val[simp]:
  assumes "Rep_msgWithChan a = (channel_input_val, boolEVENTConstr m)"
  shows "channel_input_valf (a#ls) = m # channel_input_valf ls"
  by(simp add: assms channel_input_valf_def)

lemma channel_input_val_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "channel_input_val_sfilter s = <(channel_input_valf (s2list s))>"
  apply(simp add: channel_input_val_sfilter_def channel_input_valf_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)


(* filter_input_noop lemmas *)

lemma efilter_input_noop:
  "efilter (\<lambda>(c,m). (c = channel_input_val))
    \<cdot>(emap Rep_msgWithChan\<cdot>i) = emap Rep_msgWithChan\<cdot>i"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;case_tac ab;simp)
  by (simp add: Abs_msgWithChan_inverse2)+

lemma efilter_input_noop2:
  "(efilter (\<lambda>m. (fst m = channel_input_val))
    \<cdot>(emap Rep_msgWithChan\<cdot>i)) = (emap Rep_msgWithChan\<cdot>i)"
  using efilter_input_noop by(simp add: case_prod_beta')

lemma sfilter_input_noop:
  "\<forall>t. {m. (fst m = channel_input_val)}
  \<ominus> smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i) = smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i)"
  by(simp add: efilter_input_noop2 smap_esnth filter_esnth)


(* input eq lemmas *)

lemma channel_input_val_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "channel_input_val_efilter\<cdot>i \<sqsubseteq> channel_input_valAbbr sb"
proof(-)
  have h1: "emap (inv boolEVENTConstr)\<cdot>(emap boolEVENTConstr\<cdot>(channel_input_valAbbr sb)) = (channel_input_valAbbr sb)"
      by(simp add: emaps2emap)

  obtain x1 where ab_def: "sb = def_Inverter_HLR1_Input.sbsetter\<cdot>(x1)"
    by(metis def_Inverter_HLR1_Input.SB.set_get prod.exhaust_sel)
  have "(sb \<^enum> channel_input_val) = (smap (Timed o TLive )\<cdot>(emap boolEVENTConstr\<cdot>(channel_input_valAbbr sb)))"
    apply(simp add: ab_def)
    apply(induction x1;simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_input_val)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> emap boolEVENTConstr\<cdot>(channel_input_valAbbr sb)"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma channel_input_val_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(channel_input_val_efilter\<cdot>i) \<subseteq> eValues\<cdot>(channel_input_valAbbr sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms channel_input_val_prefix_eq by simp

lemma channel_input_val_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(channel_input_valAbbr sb)) = channel_input_val_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain x1 where ab_def: "sb = def_Inverter_HLR1_Input.sbsetter\<cdot>(x1)"
    by(metis def_Inverter_HLR1_Input.SB.set_get prod.exhaust_sel)
  have "channel_input_valAbbr sb = emap (inv boolEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> channel_input_val))"
    apply(simp add: ab_def)
    apply(induction x1;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: channel_input_val_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed


(* ticksb output lemmas *)

lemma sbsetter_ticksb:"def_Inverter_HLR1_Output.sbsetter\<cdot>(\<up>Tick) = ticksb"
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb: "def_Inverter_HLR1_Output.sbgetter\<cdot>ticksb = (\<up>Tick)"
  apply(subst(2) def_Inverter_HLR1_Output.SB.get_set[symmetric])
  apply(rule cfun_arg_cong)
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb2[simp]: "def_Inverter_HLR1_Output.sbgetter\<cdot>(ticksb \<Zcat>\<Zcat> s) =
  (\<up>Tick) \<Zcat>\<Zcat> def_Inverter_HLR1_Output.sbgetter\<cdot>s"
  by(simp add: sbgetter_ticksb conc_sb_def getter_conc2sbconc[symmetric])


(* usplit out lemmas *)

lemma usplit_event_sbsetter_channel_output_val_list:
  "uSplit\<cdot>(smap EventMsg\<cdot>(smap channel_Inverter_HLR1_output_valConstr\<cdot>(<ls>))) =
    def_Inverter_HLR1_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<ls>))"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= channel_output_val and m="boolEVENTConstr a"])
  apply(simp_all add: channel_Inverter_HLR1_output_valConstr.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_channel_output_val:
  "uSplit\<cdot>(\<up>(EventMsg (channel_Inverter_HLR1_output_valConstr a)) \<Zcat> s) =
    def_Inverter_HLR1_Output.sbsetter\<cdot>(\<up>(EventMsg a)) \<Zcat>\<Zcat> (uSplit\<cdot>s)"
  using usplit_event_sbsetter_channel_output_val_list[where ls="[a]"] apply simp
  by(simp add: usplit_conc)?

lemma somethingexists[simp]:
  "(\<exists>m1::bool. Rep_msgWithChan aa = (channel_input_val, boolEVENTConstr m1))"
  apply(auto)?
  apply(cases aa;case_tac y;case_tac a;case_tac b;simp add: well_def)?
  apply(metis (full_types) msg.exhaust def_Inverter_HLR1_Input.channels.exhaust surj_pair)?
  apply(blast+)?
  by((subst Abs_msgWithChan_inverse, simp_all add: well_def)+)?


(* automaton transition lemmas *)

lemma init0_nda:"autInitConfig\<cdot>(behavior.eaut ()) = {(StateConstr Substate.state__S, ticksb)}"
  apply(simp add:behavior.config_def)
  by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)

lemma init0_da:
  assumes "da \<in> (behavior.daset ())"
  shows "\<exists>foo. (dautInitConfig da) = ((StateConstr Substate.state__S, foo), ticksb)"
proof(-)
  have "apfst fst (dautInitConfig da) = (StateConstr Substate.state__S, ticksb)"
    using init0_nda nda2da_init eventGen.daset_def assms by(metis singleton_iff)
  then show ?thesis
    by(metis eq_fst_iff snd_conv tuple_to_apfst)
qed

lemma transitionE00_nda:
  assumes "Rep_msgWithChan m = (channel_input_val, boolEVENTConstr channel_input_val_pattern)"
  and "(channel_input_val_pattern = True)"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S)) (EventMsg m)) =
         {(StateConstr Substate.state__S, def_Inverter_HLR1_Output.sbsetter\<cdot>(\<up>(EventMsg False)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms usplit_event_sbsetter_channel_output_val apply(simp)
  apply(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)?
    (* autosledgi *) sorry

lemma transitionE00_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_input_val, boolEVENTConstr channel_input_val_pattern)"
  and "(channel_input_val_pattern = True)"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S), foo) (EventMsg m) =
         ((StateConstr Substate.state__S, bar), def_Inverter_HLR1_Output.sbsetter\<cdot>(\<up>(EventMsg False)))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S), foo) (EventMsg m)) =
          (StateConstr Substate.state__S, def_Inverter_HLR1_Output.sbsetter\<cdot>(\<up>(EventMsg False)))"
    using transitionE00_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed


lemma getch_to_getter_1:
  "(out \<^enum> channel_output_val)
 = (Rep_cfun (smap (Timed o TLive o map_event boolEVENTConstr))) ((def_Inverter_HLR1_Output.sbgetter\<cdot>(out)))"
  proof -
    obtain s1 
      where s_def: "(s1) = def_Inverter_HLR1_Output.sbgetter\<cdot>(out)"
      using prod.collapse by blast
    have setter_def:"out = SB.setter\<cdot>(s1)"
      by(simp add: s_def)
    show ?thesis
      apply(subst setter_def)
      apply(subst SB.setter_getch)
      apply(subst buildSB_def)
      apply(subst channelsChan.simps(1))
      using s_def by (metis fst_conv snd_conv)
  qed

lemma svalues_getch_subset_sbvalues:
"\<And> c::channels. sValues\<cdot>(out \<^enum> c) \<subseteq> (snd ` sbValues\<cdot>(out))"
  apply(case_tac c)
  proof -
    fix c assume c_def: "c = channel_output_val"
    have "Pair channel_output_val ` sValues\<cdot>
            ((Rep_cfun (smap (Timed o TLive o map_event boolEVENTConstr)))
              ((def_Inverter_HLR1_Output.sbgetter\<cdot>(out))))
          \<subseteq> sbValues\<cdot>(out)"
      apply(simp add: getch_to_getter_1[symmetric])
      apply(rule subsetI)
      apply(subst sbValues_def)
      apply(subst Abs_cfun_inverse2)
      using sbvalues_cont apply blast
      apply(subst Union_iff)
      using chdom_in somechannotempty by blast

    thus "sValues\<cdot>(out \<^enum> c) \<subseteq> (snd ` sbValues\<cdot>(out))"
    apply(subst c_def)
    apply(simp add:getch_to_getter_1[symmetric])
    by (metis (mono_tags, lifting) image_subset_iff snd_conv subsetI)
  qed

lemma getter_preserves_no_tick:
  assumes "\<And> m. m \<in> (snd ` sbValues\<cdot>(out)) \<Longrightarrow> #\<^sub>\<surd> m = 0"
    shows "Tick \<notin> sValues\<cdot>((def_Inverter_HLR1_Output.sbgetter\<cdot>out))"
  apply auto
  proof -
    assume tick: "Tick \<in> sValues\<cdot>((def_Inverter_HLR1_Output.sbgetter\<cdot>out))"
    hence "(Timed (TLive (Tick))) \<in> sValues\<cdot>(out \<^enum> channel_output_val)"
      apply(subst getch_to_getter_1)
      by(simp add: smap_sValues)
    hence "(Timed (TLive (Tick))) \<in> (snd ` sbValues\<cdot>(out))"
      using svalues_getch_subset_sbvalues by blast
    with assms show False
      by (metis tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlent)
  qed

lemma getter_preserves_len_finite:
  assumes "\<And>c. #(out \<^enum> c) < \<infinity>"
    shows "#((def_Inverter_HLR1_Output.sbgetter\<cdot>out)) < \<infinity>"
  apply(rule conjI)?
  by(metis assms getch_to_getter_1 slen_smap)

lemma no_tick_from_eventgen:
  assumes "da \<in> (behavior.daset ())"
    shows "Tick \<notin> sValues\<cdot>((def_Inverter_HLR1_Output.sbgetter\<cdot>(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))"
  apply(rule conjI)?
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param="()"])
  apply(simp_all add:assms)
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
  apply(simp_all add:assms)?
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param="()"])?
  by(simp_all add:assms)?

lemma not_inf_from_eventgen:
  assumes "da \<in> (behavior.daset ())"
    shows "#((def_Inverter_HLR1_Output.sbgetter\<cdot>(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i))))))) < \<infinity>"
  apply(rule conjI)?
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param="()"])
  using assms apply blast apply simp+
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne da (StateConstr state , foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
  apply(simp_all add:assms)?
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param="()"])?
  using assms apply blast? by (simp+)?


method admissibility_wrapup uses definitions =
  (simp_all add: SetPcpo.less_set_def[symmetric] eventFilter_def eValues_def
      )

strategy SolveSubgoals =
    Ors[
      User <admissibility_wrapup>,
      Repeat(Ors[Fastforce,Hammer])
    ]

strategy AdmRules = Ors[User <rule adm_imp>, User <rule adm_all>, User <rule adm_imp>,
    User <rule adm_below, User <rule adm_eq, User <rule adm_subst>, User <rule adm_not_below>]

strategy AdmStrat = Thens[Repeat(Ors[AdmRules,Simp]), SolveSubgoals, IsSolved]

lemma predicate_0_llr:
  assumes "spf \<in> def_Inverter_LLR1.Sps ()"
      and "wellformed (def_Inverter_HLR1_Input.sbgetter\<cdot>sb)"
    shows "assumption_0 () (def_Inverter_HLR1_Input.sbgetter\<cdot>sb) (def_Inverter_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<and>
           assumption_1 () (def_Inverter_HLR1_Input.sbgetter\<cdot>sb) (def_Inverter_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<longrightarrow>
           predicate_0 () (def_Inverter_HLR1_Input.sbgetter\<cdot>sb) (def_Inverter_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: def_Inverter_LLR1.Sps_def behavior.Sem_def)
  apply(rule bundlemergepred[where SPS="eSem (behavior.eaut ())"])
  apply(simp)
  apply(simp add: predicate_0_def)
  apply(simp add: case_prod_beta)?
  (* autosledgi *) sorry

lemma causality_llr:
  assumes "spf \<in> def_Inverter_LLR1.Sps ()"
    shows "causality (def_Inverter_HLR1_Input.sbgetter\<cdot>sb) (def_Inverter_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  apply(simp add: causality_def strongpred_def)
  using assms by(metis case_unit behavior.sem_strong def_Inverter_LLR1.Sps_def strong2pred strongpred_def)

lemma wholePredicate_llr:
  assumes "spf \<in> def_Inverter_LLR1.Sps ()"
    shows "wholePredicate () (def_Inverter_HLR1_Input.sbgetter\<cdot>sb) (def_Inverter_HLR1_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: wholePredicate_def)
  by(simp add: predicate_0_llr causality_llr)

(* General refinement skeleton *)
lemma refinement[simp]: "def_Inverter_LLR1.Sps () \<subseteq> def_Inverter_HLR2.Sps ()"
  by(simp add: def_Inverter_HLR2.Sps_def subsetI wholePredicate_llr)


end
