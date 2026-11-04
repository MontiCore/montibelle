theory hwl_Buffer
  imports
    sps_Buffer_LLR.def_Buffer_LLR
    sps_Buffer_HLR3.def_Buffer_HLR3
    automaton.Nda2DaSet
  Smart_Isabelle.Smart_Isabelle
begin


(* channel lemmas *)

lemma not_input_ctrl:"Rep_msgWithChan z \<noteq> (channel_input_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_control_packet:"Rep_msgWithChan z \<noteq> (channel_control_data, PacketEVENTConstr y)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_output_ctrl:"Rep_msgWithChan z \<noteq> (channel_output_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma[simp]:"def_Buffer_HLR3_Input.buildSB (control,input) channel_input_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) input"
  by (simp add: def_Buffer_HLR3_Input.buildSB_def)

lemma[simp]:"def_Buffer_HLR3_Input.buildSB (control,input) channel_control_data = (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr))) control"
  by (simp add: def_Buffer_HLR3_Input.buildSB_def)

lemma[simp]:"def_Buffer_HLR3_Output.buildSB (output) channel_output_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) output"
  by (simp add: def_Buffer_HLR3_Output.buildSB_def)

lemma input_imp_packet:
  assumes "fst (Rep_msgWithChan a) = channel_input_data"
  shows "\<exists>pckt. Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)"
  by (metis msg.exhaust assms not_input_ctrl prod.collapse)

lemma control_imp_ctrl:
  assumes "fst (Rep_msgWithChan a) = channel_control_data"
  shows "\<exists>ctrl. Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
  by (metis msg.exhaust assms not_control_packet prod.collapse)

lemma output_imp_packet:
  assumes "fst (Rep_msgWithChan a) = channel_output_data"
  shows "\<exists>pckt. Rep_msgWithChan a = (channel_output_data, PacketEVENTConstr pckt)"
  by (metis msg.exhaust assms not_output_ctrl prod.collapse)


(* input channel abbreviations *)

abbreviation input::"def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<Rightarrow> Packet event stream" where
  "input sb \<equiv> snd (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"

abbreviation control::"def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<Rightarrow> CtrlEnum event stream" where
  "control sb \<equiv> fst (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"

abbreviation input_efilter::"def_Buffer_HLR3_Input.channels msgWithChan event stream \<rightarrow> Packet event stream" where
  "input_efilter \<equiv> (emap (inv PacketEVENTConstr)) oo (eventFilter channel_input_data)"

abbreviation control_efilter::"def_Buffer_HLR3_Input.channels msgWithChan event stream \<rightarrow> CtrlEnum event stream" where
  "control_efilter \<equiv> (emap (inv CtrlEnumEVENTConstr)) oo (eventFilter channel_control_data)"

definition input_sfilter::"def_Buffer_HLR3_Input.channels msgWithChan stream \<Rightarrow> Packet stream" where
  "input_sfilter s = smap (inv PacketEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_input_data} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition control_sfilter::"def_Buffer_HLR3_Input.channels msgWithChan stream \<Rightarrow> CtrlEnum stream" where
  "control_sfilter s = smap (inv CtrlEnumEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_control_data} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition inputf::"def_Buffer_HLR3_Input.channels msgWithChan list \<Rightarrow> Packet list" where
 "inputf = (\<lambda>ls. map ((inv PacketEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_input_data) (map Rep_msgWithChan ls)))"

definition controlf::"def_Buffer_HLR3_Input.channels msgWithChan list \<Rightarrow> CtrlEnum list" where
 "controlf = (\<lambda>ls. map ((inv CtrlEnumEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_control_data) (map Rep_msgWithChan ls)))"

(* lemmas over abbreviations *)

lemma inputf_empty[simp]: "inputf [] = []"
  by(simp add: inputf_def)

lemma inputf_control[simp]:
  assumes "Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
  shows "inputf (a#ls) = inputf ls"
  by(simp add: assms inputf_def)

lemma inputf_input[simp]:
  assumes "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)"
  shows "inputf (a#ls) = pckt # inputf ls"
  by(simp add: assms inputf_def)

lemma input_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "input_sfilter s = <(inputf (s2list s))>"
  apply(simp add: input_sfilter_def inputf_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)

lemma controlf_empty[simp]: "controlf [] = []"
  by(simp add: controlf_def)

lemma controlf_control[simp]:
  assumes "Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
  shows "controlf (a#ls) = ctrl # controlf ls"
  by(simp add: assms controlf_def)

lemma controlf_input[simp]:
  assumes "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)"
  shows "controlf (a#ls) = controlf ls"
  by(simp add: assms controlf_def)

lemma control_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "control_sfilter s = <(controlf (s2list s))>"
  apply(simp add: control_sfilter_def controlf_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)

(* filter_input_noop lemmas *)

lemma efilter_input_noop:"efilter (\<lambda>(c,m). (c = channel_input_data) \<or> (c = channel_control_data))
   \<cdot>(emap Rep_msgWithChan\<cdot>i) =
    emap Rep_msgWithChan\<cdot>i"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;case_tac ab;simp)
  by (simp add: Abs_msgWithChan_inverse2)+

lemma efilter_input_noop2:
  "(efilter (\<lambda>m. (fst m = channel_input_data) \<or> (fst m = channel_control_data))
    \<cdot>(emap Rep_msgWithChan\<cdot>i)) = (emap Rep_msgWithChan\<cdot>i)"
  using efilter_input_noop by(simp add: case_prod_beta')

lemma sfilter_input_noop:
 "\<forall>t. {m. (fst m = channel_input_data) \<or> (fst m = channel_control_data)}
  \<ominus> smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i) =
    smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i)"
  by(simp add: efilter_input_noop2 smap_esnth filter_esnth)

(* input eq lemmas *)

lemma input_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "input_efilter\<cdot>i \<sqsubseteq> input sb"
proof(-)
  have h1: "emap (inv PacketEVENTConstr)\<cdot>(emap PacketEVENTConstr\<cdot>(input sb)) = (input sb)"
    by(simp add: emaps2emap)

  obtain x y where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x,y)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "(sb  \<^enum>  channel_input_data) = (smap (Timed o TLive)\<cdot>(emap PacketEVENTConstr\<cdot>(input sb)))"
    apply(simp add: ab_def)
    apply(induction y;simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_input_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq>
            (emap PacketEVENTConstr\<cdot>(input sb))"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma input_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(input_efilter\<cdot>i) \<subseteq> eValues\<cdot>(input sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms input_prefix_eq by simp

lemma input_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(input sb)) = input_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain x y where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x,y)"
     by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "input sb = emap (inv PacketEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  channel_input_data))"
    apply(simp add: ab_def)
    apply(induction y;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: input_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed

lemma control_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "control_efilter\<cdot>i \<sqsubseteq> control sb"
proof(-)
  have h1: "emap (inv CtrlEnumEVENTConstr)\<cdot>(emap CtrlEnumEVENTConstr\<cdot>(control sb)) = (control sb)"
    by(simp add: emaps2emap)

  obtain x y where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x,y)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "(sb  \<^enum>  channel_control_data) = (smap (Timed o TLive)\<cdot>(emap CtrlEnumEVENTConstr\<cdot>(control sb)))"
    apply(simp add: ab_def)
    apply(induction x;simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_control_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> emap CtrlEnumEVENTConstr\<cdot>(control sb)"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma control_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(control_efilter\<cdot>i) \<subseteq> eValues\<cdot>(control sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms control_prefix_eq by simp

lemma control_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(control sb)) = control_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain x y where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x,y)"
     by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "control sb = emap (inv CtrlEnumEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  channel_control_data))"
    apply(simp add: ab_def)
    apply(induction x;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: control_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed

(* ticksb output lemmas *)

lemma sbsetter_ticksb: "def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>Tick) = ticksb"
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb: "def_Buffer_HLR3_Output.sbgetter\<cdot>ticksb = (\<up>Tick)"
  apply(subst(2) def_Buffer_HLR3_Output.SB.get_set[symmetric])
  apply(rule cfun_arg_cong)
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb2[simp]: "def_Buffer_HLR3_Output.sbgetter\<cdot>(ticksb \<Zcat>\<Zcat> s) =
  \<up>Tick \<Zcat>\<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>s"
  by(simp add: sbgetter_ticksb conc_sb_def getter_conc2sbconc[symmetric])

(* usplit out lemmas *)

lemma usplit_event_sbsetter_output_list:
"uSplit\<cdot>(smap EventMsg\<cdot>(smap channel_Buffer_HLR3_output_dataConstr\<cdot>(<ls>))) =
    def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<ls>))"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= channel_output_data and m="PacketEVENTConstr a"])
  apply(simp_all add: channel_Buffer_HLR3_output_dataConstr.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_output:
"uSplit\<cdot>(\<up>(EventMsg (channel_Buffer_HLR3_output_dataConstr a))) =
    def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg a))"
  using usplit_event_sbsetter_output_list[where ls="[a]"] apply simp
  by (simp add: usplit_conc)?

lemma somethingexists[simp]:"(\<exists>ctrl::CtrlEnum. Rep_msgWithChan aa = (channel_control_data, CtrlEnumEVENTConstr ctrl)) \<or>
       (\<exists>packet. Rep_msgWithChan aa = (channel_input_data, PacketEVENTConstr packet))"
  apply(auto)
  apply(cases aa;case_tac y;case_tac a;case_tac b;simp add: well_def)
  using not_input_ctrl not_control_packet
  apply (metis (full_types) msg.exhaust def_Buffer_HLR3_Input.channels.exhaust surj_pair) apply blast+
  by(subst Abs_msgWithChan_inverse,simp_all add: well_def, subst(asm) Abs_msgWithChan_inverse,simp_all add: well_def)+

(* automaton transition lemmas *)

lemma init_nda: "autInitConfig\<cdot>(behavior.eaut ()) = {(StateConstr state__S [] [], \<bottom>)}"
  apply(simp add: behavior.config_def)
  by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)

lemma init_da:
  assumes "da \<in> (behavior.daset ())"
shows "\<exists>foo. (dautInitConfig da) = ((StateConstr state__S [] [], foo), bottom)"
proof(-)
  have "apfst fst (dautInitConfig da) = (StateConstr state__S [] [], \<bottom>)"
    using init_nda nda2da_init eventGen.daset_def assms by fastforce
  then show ?thesis
    by(metis eq_fst_iff snd_conv tuple_to_apfst)
qed

lemma packet_old_empty_nda:
  assumes "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr x)"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S [] new) (EventMsg pckt)) =
      {((StateConstr state__S [] (new @ [x])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg x)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp add: usplit_event_sbsetter_output)

lemma packet_old_empty_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr x)"
shows "\<exists>bar. dautTransition da (StateConstr state__S [] new, foo) (EventMsg pckt) =
       ((StateConstr state__S [] (new @ [x]), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg x)))"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S [] new, foo) (EventMsg pckt)) =
    ((StateConstr state__S [] (new @ [x])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg x)))"
    using packet_old_empty_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma packet_old_nonempty_nda:
  assumes "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr x)"
  and "old \<noteq> []"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S old new) (EventMsg pckt)) =
      {((StateConstr state__S old (new @ [x])), \<bottom>)}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp add: usplit_event_sbsetter_output)

lemma packet_old_nonempty_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr x)"
  and "old \<noteq> []"
shows "\<exists>bar. dautTransition da (StateConstr state__S old new, foo) (EventMsg pckt) =
       ((StateConstr state__S old (new @ [x]), bar), bottom)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S old new, foo) (EventMsg pckt)) =
    ((StateConstr state__S old (new @ [x])), \<bottom>)"
    using packet_old_nonempty_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma ack_old_gt_1_nda:
  assumes "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr ACK)"
  and "length old > 1"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S old new) (EventMsg ctrl)) =
      {((StateConstr state__S (tl old) new), \<bottom>)}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp add: usplit_event_sbsetter_output)

lemma ack_old_gt_1_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr ACK)"
  and "length old > 1"
shows "\<exists>bar. dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl) =
       ((StateConstr state__S (tl old) new, bar), bottom)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl)) =
    ((StateConstr state__S (tl old) new), \<bottom>)"
     using ack_old_gt_1_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma ack_old_eq_1_nda:
  assumes "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr ACK)"
  and "length old = 1"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S old new) (EventMsg ctrl)) =
      {((StateConstr state__S [] new), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<new>)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms apply(simp add: smapsmap2smap[symmetric] usplit_event_sbsetter_output_list)
  by(metis diff_Suc_1 length_0_conv length_tl)

lemma ack_old_eq_1_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr ACK)"
  and "length old = 1"
shows "\<exists>bar. dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl) =
      ((StateConstr state__S [] new, bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<new>)))"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl)) =
    ((StateConstr state__S [] new), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<new>)))"
    using ack_old_eq_1_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma nak_old_nonempty_nda:
  assumes "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr NAK)"
  and "old \<noteq> []"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S old new) (EventMsg ctrl)) =
      {((StateConstr state__S [] (old @ new)), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(old @ new)>)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms apply(simp add: append2sconc smap_split[symmetric])
  by(simp add: append2sconc[symmetric] smapsmap2smap[symmetric] usplit_event_sbsetter_output_list)

lemma nak_old_nonempty_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr NAK)"
  and "old \<noteq> []"
shows "\<exists>bar. dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl) =
      ((StateConstr state__S [] (old @ new), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(old @ new)>)))"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S old new, foo) (EventMsg ctrl)) =
    ((StateConstr state__S [] (old @ new)), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(old @ new)>)))"
    using nak_old_nonempty_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma ctrl_old_empty_nda:
  assumes "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr x)"
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S [] new) (EventMsg ctrl)) =
      {((StateConstr state__S [] new), \<bottom>)}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp)

lemma ctrl_old_empty_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan ctrl = (channel_control_data, CtrlEnumEVENTConstr x)"
shows "\<exists>bar. dautTransition da (StateConstr state__S [] new, foo) (EventMsg ctrl) =
      ((StateConstr state__S [] new, bar), bottom)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S [] new, foo) (EventMsg ctrl)) =
      ((StateConstr state__S [] new), \<bottom>)"
    using ctrl_old_empty_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma tick_nda:
shows "((autTransition\<cdot>(behavior.eaut ())) (StateConstr state__S old new) Tick) =
      {((StateConstr state__S new []), ticksb)}"
  apply(simp add: behavior.transition_def)
  by(simp add: EventLocale.outconv_def behavior.ndaTransition_tickC_def)

lemma tick_da:
  assumes "da \<in> (behavior.daset ())"
shows "\<exists>bar. dautTransition da (StateConstr state__S old new, foo) Tick =
       ((StateConstr state__S new [], bar), ticksb)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__S old new, foo) Tick) =
          ((StateConstr state__S new []), ticksb)"
    using tick_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed


lemma mult_trans_old_empty:
  assumes "da \<in> (behavior.daset ())"
  shows "\<exists>bar. multTransitionsInOne da (StateConstr state__S [] new, foo) (map EventMsg ls) =
    ((StateConstr state__S [] (new @ inputf ls), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf ls)>)))"
  using assms
proof(induction ls arbitrary: new foo)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)

  obtain pckt ctrl where a_def:
    "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt) \<or>
     Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
    by(meson somethingexists)

  show ?case
  proof(cases "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)")
    case True

    obtain bar where bar_def: "dautTransition da (StateConstr state__S [] new, foo) (EventMsg a) =
       ((StateConstr state__S [] (new @ [pckt]), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg pckt)))"
      using packet_old_empty_da True Cons.prems(1) by blast

    obtain baz where baz_def: "multTransitionsInOne da (StateConstr state__S [] (new @ [pckt]), bar) (map EventMsg ls) =
      ((StateConstr state__S [] ((new @ [pckt]) @ inputf ls), baz), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf ls)>)))"
      using Cons.IH Cons.prems by blast

    show ?thesis
      apply(simp add: bar_def baz_def True)
      by(simp add: conc_sb_def setter_conc2sbconc[symmetric])
  next
    case False

    obtain bar where bar_def: "dautTransition da (StateConstr state__S [] new, foo) (EventMsg a) =
       ((StateConstr state__S [] new, bar), \<bottom>)"
      using ctrl_old_empty_da a_def False Cons.prems(1) by blast

    obtain baz where baz_def: "multTransitionsInOne da (StateConstr state__S [] new, bar) (map EventMsg ls) =
      ((StateConstr state__S [] (new @ inputf ls), baz), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf ls)>)))"
      using Cons.IH Cons.prems by blast

    show ?thesis
      using a_def by(simp add: bar_def False baz_def)
  qed
qed

lemma mult_trans_no_nak:
  assumes "da \<in> (behavior.daset ())"
  and "NAK \<notin> set (controlf ls)"
  and "length old \<le> length (controlf ls)"
  and "old = [] \<Longrightarrow> new = []"
  and "old \<noteq> [] \<Longrightarrow> inc = []"
shows "\<exists>bar. multTransitionsInOne da (StateConstr state__S old (inc @ new), foo) (map EventMsg ls) =
         ((StateConstr state__S [] (inc @ new @ inputf ls), bar),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(new @ inputf ls)>)))"
  using assms
proof(induction ls arbitrary: old new inc foo)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)
  show ?case
  proof(cases "old = []")
    case True
    then show ?thesis
      using mult_trans_old_empty Cons.prems by(metis append_Nil append_Nil2)
  next
    case old_nonempty: False

    obtain pckt ctrl where a_def:
      "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt) \<or>
     Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
      by(meson somethingexists)

    then show ?thesis
    proof(cases "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)")
      case True

      obtain bar where bar_def: "dautTransition da (StateConstr state__S old (inc @ new), foo) (EventMsg a) =
       ((StateConstr state__S old ((inc @ new) @ [pckt]), bar), \<bottom>)"
        using packet_old_nonempty_da old_nonempty True Cons.prems by blast

      obtain baz where baz_def:
        "multTransitionsInOne da (StateConstr state__S old (inc @ new @ [pckt]), bar) (map EventMsg ls) =
          ((StateConstr state__S [] (inc @ (new @ [pckt]) @ inputf ls), baz),
            def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<((new @ [pckt]) @ inputf ls)>)))"
        using Cons.IH[where old=old and new="new @ [pckt]"] old_nonempty a_def True Cons.prems by(auto)

      show ?thesis
        by(simp add: bar_def baz_def a_def True)
    next
      case is_ctrl: False

      have ctrl_def: "ctrl = ACK"
        using a_def is_ctrl Cons.prems(2) by(cases ctrl;simp)

      show ?thesis
      proof(cases "length old = 1")
        case True

        obtain bar where bar_def:
          "dautTransition da (StateConstr state__S old new, foo) (EventMsg a) =
            ((StateConstr state__S [] new, bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<new>)))"
          using ack_old_eq_1_da a_def is_ctrl ctrl_def True Cons.prems by blast

        obtain baz where baz_def:
          "(multTransitionsInOne da (StateConstr state__S [] new, bar) (map EventMsg ls)) =
            ((StateConstr state__S [] (new @ inputf ls), baz),
              def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf ls)>)))"
          using Cons.IH[where old="[]" and inc=new and new="[]"] Cons.prems a_def
          apply(simp add: ctrl_def is_ctrl True)
          by(blast)

        show ?thesis
          using a_def apply(simp add: is_ctrl ctrl_def True bar_def baz_def Cons.prems old_nonempty)
          apply(simp add: conc_sb_def setter_conc2sbconc[symmetric])
          by(simp add: append2sconc smap_split)
      next
        case False

        have "length old > 1"
          using False not_less_iff_gr_or_eq old_nonempty by auto
        then obtain bar where bar_def:
          "dautTransition da (StateConstr state__S old new, foo) (EventMsg a) =
                ((StateConstr state__S (tl old) new, bar), \<bottom>)"
          using ack_old_gt_1_da a_def is_ctrl ctrl_def Cons.prems by blast

        have "tl old \<noteq> []"
          by(metis False Nitpick.size_list_simp(2) One_nat_def old_nonempty)
        then have "tl old \<noteq> [] \<and> length (tl old) \<le> length (controlf ls)"
          using Cons.prems(3) a_def by(simp add: is_ctrl False)
        then obtain baz where baz_def:
          "(multTransitionsInOne da (StateConstr state__S (tl old) new, bar) (map EventMsg ls)) =
            ((StateConstr state__S [] (new @ inputf ls), baz),
              def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(new @ inputf ls)>)))"
          using Cons.IH[where old="tl old" and inc="[]" and new=new and foo=bar] Cons.prems a_def
          apply(simp add: ctrl_def is_ctrl False)
          by(blast)

        show ?thesis
          using a_def by(simp add: is_ctrl ctrl_def False bar_def baz_def Cons.prems old_nonempty)
      qed
    qed
  qed
qed

lemma mult_trans_fewer_acks:
  assumes "da \<in> (behavior.daset ())"
  and "NAK \<notin> set (controlf ls)"
  and "length old > length (controlf ls)"
shows "\<exists>bar. multTransitionsInOne da (StateConstr state__S old new, foo) (map EventMsg ls) =
       ((StateConstr state__S (drop (length (controlf ls)) old) (new @ inputf ls), bar), bottom)"
  apply(insert assms)
proof(induction ls arbitrary: old new foo)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)

  obtain pckt ctrl where a_def:
    "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt) \<or>
     Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
    by(meson somethingexists)

  show ?case
  proof(cases "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)")
    case True

    have "old \<noteq> []"
      using Cons.prems(3) by fastforce
    then obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) (EventMsg a) =
       ((StateConstr state__S old (new @ [pckt]), bar), \<bottom>)"
      using packet_old_nonempty_da True Cons.prems by blast

    obtain baz where baz_def:
      "multTransitionsInOne da (StateConstr state__S old (new @ [pckt]), bar) (map EventMsg ls) =
          ((StateConstr state__S (drop (length (controlf ls)) old) ((new @ [pckt]) @ inputf ls), baz), \<bottom>)"
      using Cons.IH[where new="new @ [pckt]"] True Cons.prems by auto

    show ?thesis
      by(simp add: bar_def baz_def True)
  next
    case False

    have ctrl_def: "ctrl = ACK"
      apply(cases ctrl;simp)
      using a_def Cons.prems(2) False by auto

    have "length (controlf (a#ls)) \<ge> 1"
      using False a_def by simp
    then have "length old > 1"
      using Cons.prems(3) by linarith

    then obtain bar where bar_def:
      "dautTransition da (StateConstr state__S old new, foo) (EventMsg a) =
         ((StateConstr state__S (tl old) new, bar), \<bottom>)"
      using ack_old_gt_1_da a_def False ctrl_def Cons.prems by blast

    have "length (controlf ls) < ((length old) - 1::nat)"
      using Cons.prems(3) a_def False by(simp)
    then obtain baz where baz_def:
      "multTransitionsInOne da (StateConstr state__S (tl old) new, bar) (map EventMsg ls) =
          ((StateConstr state__S (drop (length (controlf ls)) (tl old)) (new @ inputf ls), baz), \<bottom>)"
      using Cons.IH[where old="tl old"] a_def False Cons.prems by auto

    show ?thesis
      using a_def by(simp add: bar_def baz_def False drop_Suc)
  qed
qed

lemma mult_trans_nak:
  assumes "da \<in> (behavior.daset ())"
  and "Some (no_nak, nak, rest) =
    List.extract (\<lambda>m. Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr NAK)) ls"
  and "repeated = drop (length (controlf no_nak)) old"
  and "old = [] \<Longrightarrow> new = []"
shows "\<exists>bar. multTransitionsInOne da (StateConstr state__S old new, foo) (map EventMsg ls) =
       ((StateConstr state__S [] (repeated @ new @ inputf ls), bar),
         def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(repeated @ new @ inputf ls)>)))"
proof(-)
  have ls_nak_split: "ls = no_nak @ (nak # rest)"
    using assms by (metis extract_SomeE)

  have nak_def: "Rep_msgWithChan nak = (channel_control_data, CtrlEnumEVENTConstr NAK)"
    by (metis (mono_tags) assms(2) extract_SomeE)

  have no_nak_def: "NAK \<notin> set (controlf no_nak)"
    apply(insert assms(2))
    apply(simp add: controlf_def)
    using control_imp_ctrl apply auto
    by (metis (mono_tags, lifting) extract_SomeE f_inv_into_f rangeI snd_conv)

  have input_ls_split: "inputf ls = inputf no_nak @ inputf rest"
    by(simp add: inputf_def ls_nak_split nak_def)

  show ?thesis
  proof(cases "length (controlf no_nak) \<ge> length old")
    case length_greater_old:True
    show ?thesis
    proof(cases "old = []")
      case True
      have newempty: "new = []" using assms(4) True by simp

      obtain bar1 where bar1_def:
      "multTransitionsInOne da (StateConstr state__S old new, foo) (map EventMsg no_nak) =
        ((StateConstr state__S [] (new @ inputf no_nak), bar1),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf no_nak)>)))"
        using mult_trans_old_empty assms True no_nak_def by(metis append_self_conv2)

      obtain bar2 where bar2_def:
        "dautTransition da (StateConstr state__S [] (new @ inputf no_nak), bar1) (EventMsg nak) =
          ((StateConstr state__S [] (new @ inputf no_nak), bar2), \<bottom>)"
      using ctrl_old_empty_da nak_def True assms by blast

      obtain bar3 where bar3_def:
        "multTransitionsInOne da (StateConstr state__S [] (new @ inputf no_nak), bar2) (map EventMsg rest) =
          ((StateConstr state__S [] ((new @ inputf no_nak) @ inputf rest), bar3),
            def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf rest)>)))"
        using mult_trans_old_empty assms by blast

      show ?thesis
        apply(subst ls_nak_split)
        apply(simp add: multtransition_split bar1_def bar2_def bar3_def length_greater_old assms)
        apply(simp add: input_ls_split)
        by(simp add: conc_sb_def setter_conc2sbconc[symmetric] append2sconc smap_split newempty)

    next
      case False

    obtain bar1 where bar1_def:
      "multTransitionsInOne da (StateConstr state__S old new, foo) (map EventMsg no_nak) =
        ((StateConstr state__S [] (new @ inputf no_nak), bar1),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(new @ inputf no_nak)>)))"
      using mult_trans_no_nak assms length_greater_old no_nak_def by(metis append_self_conv2)

    obtain bar2 where bar2_def:
      "dautTransition da (StateConstr state__S [] (new @ inputf no_nak), bar1) (EventMsg nak) =
        ((StateConstr state__S [] (new @ inputf no_nak), bar2), \<bottom>)"
      using ctrl_old_empty_da nak_def length_greater_old assms by blast

    obtain bar3 where bar3_def:
      "multTransitionsInOne da (StateConstr state__S [] (new @ inputf no_nak), bar2) (map EventMsg rest) =
        ((StateConstr state__S [] ((new @ inputf no_nak) @ inputf rest), bar3),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf rest)>)))"
      using mult_trans_old_empty assms by blast

    show ?thesis
      apply(subst ls_nak_split)
      apply(simp add: multtransition_split bar1_def bar2_def bar3_def length_greater_old assms)
      apply(simp add: input_ls_split)
      by(simp add: conc_sb_def setter_conc2sbconc[symmetric] append2sconc smap_split)
    qed

  next
    case False

    obtain bar1 where bar1_def:
      "multTransitionsInOne da (StateConstr state__S old new, foo) (map EventMsg no_nak) =
        ((StateConstr state__S (drop (length (controlf no_nak)) old) (new @ inputf no_nak), bar1), \<bottom>)"
      using mult_trans_fewer_acks assms False no_nak_def linorder_not_less by blast

    obtain bar2 where bar2_def:
      "dautTransition da (StateConstr state__S (drop (length (controlf no_nak)) old) (new @ inputf no_nak), bar1) (EventMsg nak) =
        ((StateConstr state__S [] ((drop (length (controlf no_nak)) old) @ (new @ inputf no_nak)), bar2),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<((drop (length (controlf no_nak)) old) @ (new @ inputf no_nak))>)))"
      using nak_old_nonempty_da nak_def False assms by(meson drop_eq_Nil)

    obtain bar3 where bar3_def:
      "multTransitionsInOne da (StateConstr state__S [] (drop (length (controlf no_nak)) old @ new @ inputf no_nak), bar2) (map EventMsg rest) =
        ((StateConstr state__S [] ((drop (length (controlf no_nak)) old @ new @ inputf no_nak) @ inputf rest), bar3),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf rest)>)))"
      using mult_trans_old_empty assms by blast

    show ?thesis
      apply(subst ls_nak_split)
      apply(subst map_append)
      apply(subst multtransition_split)
      apply(simp add: bar1_def bar2_def bar3_def no_nak_def assms)
      apply(simp add: input_ls_split)
      by(simp add: conc_sb_def setter_conc2sbconc[symmetric] append2sconc smap_split)
  qed
qed

lemma alwaysTransmit_single_timestep:
  assumes "da \<in> (behavior.daset ())"
  and "inputf ls \<noteq> []"
  and "length old = length (controlf ls) \<or> NAK \<in> set (controlf ls)"
shows "\<exists>out bar. out \<noteq> [] \<and> multTransitionsInOne da (StateConstr state__S old [], foo) ((map EventMsg ls) @ [Tick]) =
       ((StateConstr state__S out [], bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(out)>) \<Zcat> (\<up>Tick)))"
proof(cases "NAK \<in> set (controlf ls)")
  case True

  have "\<exists>m \<in> set ls. Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr NAK)"
    using True apply(simp add: controlf_def)
    using control_imp_ctrl by fastforce

  then obtain no_nak nak rest where extract_def: "Some(no_nak, nak, rest) =
      List.extract (\<lambda>m. Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr NAK)) ls"
    by(metis (full_types) extract_None_iff option.exhaust prod.collapse)

  then obtain bar1 where bar1_def: "multTransitionsInOne da (StateConstr state__S old [], foo) (map EventMsg ls) =
       ((StateConstr state__S [] (drop (length (controlf no_nak)) old @ inputf ls), bar1),
         def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(drop (length (controlf no_nak)) old @ inputf ls)>)))"
    using mult_trans_nak True assms by(metis append_self_conv2)

  obtain bar2 where bar2_def:
    "dautTransition da (StateConstr state__S [] (drop (length (controlf no_nak)) old @ inputf ls), bar1) Tick =
      ((StateConstr state__S (drop (length (controlf no_nak)) old @ inputf ls) [], bar2), ticksb)"
    using tick_da assms by blast

  show ?thesis
    apply(simp add: multtransition_split bar1_def bar2_def assms)
    by(simp add: sbsetter_ticksb[symmetric] conc_sb_def setter_conc2sbconc[symmetric])
next
  case False

  obtain bar1 where bar1_def: "multTransitionsInOne da (StateConstr state__S old [], foo) (map EventMsg ls) =
       ((StateConstr state__S [] (inputf ls), bar1),
           def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf ls)>)))"
    using mult_trans_no_nak False assms by(metis append_self_conv2 eq_imp_le)

  obtain bar2 where bar2_def:
    "dautTransition da (StateConstr state__S [] (inputf ls), bar1) Tick =
      ((StateConstr state__S (inputf ls) [], bar2), ticksb)"
    using tick_da assms by blast

  show ?thesis
    apply(simp add: multtransition_split bar1_def bar2_def assms)
    by(simp add: sbsetter_ticksb[symmetric] conc_sb_def setter_conc2sbconc[symmetric])
qed

lemma alwaysTransmit_induction:
  assumes "da \<in> (behavior.daset ())"
  and "#\<^sub>\<surd>i = \<infinity>"
  and "\<And>n. input_sfilter (esnth n\<cdot>i) \<noteq> \<epsilon>"
  and "old \<noteq> []"
  and "\<And>n. (#(control_sfilter (esnth n\<cdot>i)) =
              #((esnth n\<cdot>(smap EventMsg\<cdot>(<(old)>) \<Zcat> \<up>Tick \<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>
                (daStateSem stream_split da (StateConstr state__S old [], foo)\<cdot>i))))) \<or>
            NAK \<in> sValues\<cdot>(control_sfilter (esnth n\<cdot>i))"
shows "0 < #((esnth n\<cdot>(smap EventMsg\<cdot>(<(old)>) \<Zcat> \<up>Tick \<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>
      (daStateSem stream_split da (StateConstr state__S old [], foo)\<cdot>i))))"
apply(insert assms)
proof(induction n arbitrary: old i foo)
  case 0
  then show ?case
    by(simp add: eshdts_split_eq not_le_imp_less)
next
  case (Suc n)

  have eshdts_fin: "#(eshdts\<cdot>i) < \<infinity>"
    using Suc.prems(2) eshdts_len by force

  have input_notempty: "(inputf (s2list (eshdts\<cdot>i))) \<noteq> []"
    using Suc.prems(3)[where n=0] input_sfilter2filter eshdts_fin by auto

  have control_semantics:
      "length old = length (controlf (s2list (eshdts\<cdot>i))) \<or> NAK \<in> set (controlf (s2list (eshdts\<cdot>i)))"
    using Suc.prems(5)[where n=0] apply(simp add: eshdts_split_eq)
    using control_sfilter2filter eshdts_fin by auto

  obtain out bar where out_def:  "out \<noteq> [] \<and> multTransitionsInOne da
       (StateConstr state__S old [], foo) ((map EventMsg (s2list (eshdts\<cdot>i))) @ [Tick]) =
       ((StateConstr state__S out [], bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(out)>) \<Zcat> (\<up>Tick)))"
    using alwaysTransmit_single_timestep[where old=old and ls="s2list (eshdts\<cdot>i)"]
      input_notempty control_semantics assms(1) by blast

  have unfold_step: "(def_Buffer_HLR3_Output.sbgetter\<cdot>
          (daStateSem stream_split da (StateConstr state__S old [], foo)\<cdot>i) =
        smap EventMsg\<cdot>(<(out)>) \<Zcat> \<up>Tick \<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>
          (daStateSem stream_split da (StateConstr state__S out [], bar)\<cdot>(tsrt\<cdot>i)))"
    apply(subst s_split_list[where s=i])
    using "Suc.prems"(2) notitckstlen apply force
    apply(subst smap2map)
    apply(subst assoc_sconc[symmetric])
    apply(subst slistl5[symmetric])
    apply(subst dastatesem_x_steps)
    by(simp add: out_def conc_sb_def getter_conc2sbconc[symmetric])

  show ?case
    apply(simp add: esnth_tsrt)
    apply(subst unfold_step)
    apply(rule Suc.IH)
    using assms(1) apply blast
    apply(simp_all add: Suc.prems out_def)
    apply(metis fold_inf lnat.sel_rews(2))
    apply(metis Suc.prems(3) esnth_tsrt)
    using Suc.prems(5) esnth_tsrt unfold_step
    by(metis (no_types, lifting) l2stream_finitelen slen_smap smapevent_tlen srtsplit)
qed

lemma alwaysTransmit_first_step:
  assumes "da \<in> (behavior.daset ())"
  and "#\<^sub>\<surd>i = \<infinity>"
  and "\<And>n. input_sfilter (esnth n\<cdot>i) \<noteq> \<epsilon>"
  and "spf = daStateSem stream_split da (StateConstr state__S [] [], foo)"
  and "\<And>n. (#(control_sfilter (esnth (Suc n)\<cdot>i)) = #(esnth n\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>i)))) \<or>
         NAK \<in> sValues\<cdot>(control_sfilter (esnth (Suc n)\<cdot>i))"
shows "0 < #(esnth n\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>i)))"
proof(-)
  obtain input0 where input0_def: "input0 = inputf (s2list (eshdts\<cdot>i))" by blast

  have "#(eshdts\<cdot>i) < \<infinity>"
    using assms(2) eshdts_len by force
  then have input0_notempty: "input0 \<noteq> []"
    using assms(3)[where n=0] input0_def input_sfilter2filter by auto

  obtain bar1 where bar1_def:
    "multTransitionsInOne da (StateConstr state__S [] [], foo) (map EventMsg (s2list (eshdts\<cdot>i))) =
        ((StateConstr state__S [] (inputf (s2list (eshdts\<cdot>i))), bar1),
          def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(inputf (s2list (eshdts\<cdot>i)))>)))"
    using mult_trans_old_empty assms by(metis self_append_conv2)

  obtain bar2 where bar2_def:
    "dautTransition da (StateConstr state__S [] (inputf (s2list (eshdts\<cdot>i))), bar1) Tick =
      ((StateConstr state__S (inputf (s2list (eshdts\<cdot>i))) [], bar2), ticksb)"
    using tick_da assms by blast

  have first_step: "def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>i) =
        smap EventMsg\<cdot>(<input0>) \<Zcat> \<up>Tick \<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>
          (daStateSem stream_split da (StateConstr state__S input0 [], bar2)\<cdot>(tsrt\<cdot>i))"
    using assms(4) apply(simp)
    apply(subst s_split_list[where s=i])
    apply(metis Inf'_neq_0 assms(2) tlentosvalues)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps)
    apply(simp add: bar1_def)
    apply(subst dastatesem_step)
    apply(simp add: bar2_def)
    apply(simp add: conc_sb_def getter_conc2sbconc[symmetric] sbsetter_ticksb[symmetric])
    by(simp add: input0_def)

  show ?thesis
    apply(subst first_step)
    apply(rule alwaysTransmit_induction)
    apply(simp_all add: assms input0_notempty)
    apply(metis fold_inf lnat.sel_rews(2))
    apply(metis assms(3) esnth_tsrt)
    apply(insert assms(5))
    by(simp add: first_step esnth_tsrt)
qed

lemma alwaysTransmit_after_bundlemergepred:
  assumes "spf \<in> mergeTimed \<then> eSem (behavior.eaut ())"
      and "wellformed (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"
      and "g \<in> eSem (behavior.eaut ())"
      and "uSplit\<cdot>i \<sqsubseteq> sb"
      and "#\<^sub>\<surd>sb = #\<^sub>\<surd>i"
      and "#(control sb) = \<infinity> \<and> #(input sb) = \<infinity>"
      and "\<forall>t. 0 < #(esnth t\<cdot>(input sb))"
    shows "(\<forall>t. #(esnth (Suc t)\<cdot>(control sb)) = #(esnth t\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(g\<cdot>i))) \<or>
               NAK \<in> sValues\<cdot>(esnth (Suc t)\<cdot>(control sb))) \<longrightarrow>
             (\<forall>t. 0 < #(esnth t\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(g\<cdot>i))))"
proof(-)
  have "g \<in> daSem stream_split ` (behavior.daset ())"
    by(metis eventGen.daset_sem_eq_esem assms(3))

  then obtain da where da_def: "da \<in> (behavior.daset ()) \<and> g = daSem stream_split da" by blast
  obtain foo where foo_def: "(dautInitConfig da) = ((StateConstr state__S [] [], foo), \<bottom>)"
    using init_da da_def by blast

  have "#sb = \<infinity>"
    apply(subst def_Buffer_HLR3_Input.SB.getter_len[symmetric])
    apply simp
    using assms(2) assms(6) by(simp add: len_prod_def)

  then have i_inf: "#\<^sub>\<surd>i = \<infinity>"
    using assms(2) assms(5) well_tlen by fastforce

  show ?thesis
    apply(simp add: da_def dasem_unfold foo_def)
    apply(auto)
    apply(rule alwaysTransmit_first_step)
    using assms(4) apply(simp_all add: da_def i_inf control_esnth_eq)
    using assms(7) input_esnth_eq by(metis empty_is_shortest fin_zero i_inf)
qed

method admissibility_wrapup uses definitions =
  (simp_all add: SetPcpo.less_set_def[symmetric] eventFilter_def eValues_def
      )

lemma outputSubsetInput_stream_induction:
  assumes "da \<in> (behavior.daset ())"
    and "set old \<subseteq> eValues\<cdot>(input sb)"
    and "set new \<subseteq> eValues\<cdot>(input sb)"
    and "eValues\<cdot>(input_efilter\<cdot>i) \<subseteq> eValues\<cdot>(input sb)"

  shows "eValues\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da
    (StateConstr state__S old new, foo)\<cdot>i)) \<subseteq> eValues\<cdot>(input sb)"
  using assms
proof(induction i arbitrary: old new foo sb)
  case adm
  then show ?case
    apply (rule adm_imp )
    apply simp
    apply (rule adm_all )
    apply (rule adm_all )
    apply (rule adm_all )
    apply (rule adm_all )
    apply (rule adm_imp )
    apply simp
    apply (rule adm_imp )
    apply simp
    apply (rule adm_imp )
    apply simp
    apply (admissibility_wrapup )
    done
next
  case bottom
  then show ?case
    by simp
next
  case (step a i)

  show ?case
  proof(cases a)
    case Tick

    obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) Tick =
       ((StateConstr state__S new [], bar), ticksb)"
      using tick_da step.prems(1) by blast

    show ?thesis
      apply(subst dastatesem_step,simp add: Tick bar_def)
apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])?
          apply(simp add: EventStream.eValues_sconc2un image_Un step.prems)?
      apply(rule step.IH)
      using assms(1) apply blast
      apply(simp_all add: step.prems)
      using step.prems(4) by(simp add: emap_def Tick)
  next
    case (EventMsg aa)

    obtain pckt ctrl where aa_def:
      "(Rep_msgWithChan aa = (channel_input_data, PacketEVENTConstr pckt)) \<or>
       (Rep_msgWithChan aa = (channel_control_data, CtrlEnumEVENTConstr ctrl))"
      by(meson somethingexists)

    then show ?thesis
    proof(cases "(Rep_msgWithChan aa = (channel_input_data, PacketEVENTConstr pckt))")
      case aa_case: True

      have pckt_in_input: "pckt \<in> eValues\<cdot>(input sb)"
        using step.prems(4) EventMsg aa_case by(auto)

      show ?thesis
      proof(cases "old = []")
        case True

        obtain bar where bar_def: "dautTransition da (StateConstr state__S [] new, foo) (EventMsg aa) =
          ((StateConstr state__S [] (new @ [pckt]), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg pckt)))"
          using packet_old_empty_da aa_case step.prems(1) by blast

        then show ?thesis
          apply(subst dastatesem_step,simp add: EventMsg True bar_def)
apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])?
              apply(simp add: EventStream.eValues_sconc2un image_Un step.prems)?
          apply(simp add: conc_sb_def getter_conc2sbconc[symmetric] pckt_in_input)
          apply(rule step.IH)
          using assms(1) apply blast
          apply(simp_all add: step.prems pckt_in_input)
          using step.prems(4) by(simp add: emap_def EventMsg aa_case)
      next
        case False

        obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) (EventMsg aa) =
          ((StateConstr state__S old (new @ [pckt]), bar), \<bottom>)"
          using packet_old_nonempty_da aa_case False step.prems(1) by blast

        show ?thesis
          apply(subst dastatesem_step,simp add: EventMsg False bar_def)
apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])?
              apply(simp add: EventStream.eValues_sconc2un image_Un step.prems)?
          apply(rule step.IH)
          using assms(1) apply blast
          apply(simp_all add: step.prems pckt_in_input)
          using step.prems(4) by(simp add: emap_def EventMsg aa_case)
      qed
    next
      case aa_case: False
      show ?thesis
      proof(cases "old = []")
        case True

        obtain bar where bar_def: "dautTransition da (StateConstr state__S [] new, foo) (EventMsg aa) =
          ((StateConstr state__S [] new, bar), \<bottom>)"
          using ctrl_old_empty_da aa_case aa_def True step.prems(1) by blast

        show ?thesis
          apply(subst dastatesem_step,simp add: EventMsg True bar_def)
          apply(rule step.IH)
          using assms(1) apply blast
          apply(simp_all add: step.prems)
          using step.prems(4) aa_def aa_case by(simp add: emap_def EventMsg)
      next
        case old_not_empty: False
        show ?thesis
        proof(cases ctrl)
          case ACK
          show ?thesis
          proof(cases "length old = 1")
            case True

            obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) (EventMsg aa) =
              ((StateConstr state__S [] new, bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<new>)))"
              using ack_old_eq_1_da True ACK aa_def aa_case step.prems(1) by blast

            show ?thesis
              apply(subst dastatesem_step,simp add: EventMsg bar_def)
              apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])?
              apply(simp add: EventStream.eValues_sconc2un image_Un step.prems)?
              apply(rule step.IH)
              using assms(1) apply blast
              apply(simp_all add: step.prems)
              using step.prems(4) aa_def aa_case by(simp add: emap_def EventMsg)
          next
            case False
            have "length old > 1"
              using False not_less_iff_gr_or_eq old_not_empty by auto
            then obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) (EventMsg aa) =
                ((StateConstr state__S (tl old) new, bar), \<bottom>)"
              using ack_old_gt_1_da ACK aa_def aa_case step.prems(1) by blast
            show ?thesis
              apply(subst dastatesem_step,simp add: EventMsg bar_def)
              apply(rule step.IH)
              using assms(1) apply blast
              apply(simp_all add: step.prems)
              using step.prems(2) apply(auto simp add: image_subset_iff list.set_sel(2) old_not_empty)
              using step.prems(4) aa_def aa_case by(auto simp add: emap_def EventMsg)
          qed
        next
          case NAK

          obtain bar where bar_def: "dautTransition da (StateConstr state__S old new, foo) (EventMsg aa) =
            ((StateConstr state__S [] (old @ new), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<(old @ new)>)))"
            using nak_old_nonempty_da NAK old_not_empty aa_def aa_case step.prems(1) by blast

          show ?thesis
            apply(subst dastatesem_step,simp add: EventMsg bar_def)
            apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])
            apply(simp add: EventStream.eValues_sconc2un image_Un step.prems)
            apply(rule step.IH)
            apply(simp_all add: step.prems)
            using step.prems apply(auto simp add: image_Un)
            using step.prems(4) aa_def aa_case by(auto simp add: emap_def EventMsg)
        qed
      qed
    qed
  qed
qed

lemma outputSubsetInput_after_bundlemergepred:
  assumes "spf \<in> mergeTimed \<then> eSem (behavior.eaut ())"
    and "wellformed (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"
    and "g \<in> eSem (behavior.eaut ())"
    and "uSplit\<cdot>i \<sqsubseteq> sb"
    and "#\<^sub>\<surd> sb = #\<^sub>\<surd> i"
    and "#(snd (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)) = \<infinity> \<and>
       #(fst (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)) = \<infinity>"
    and "(\<forall>t::nat. (0::lnat) < #(esnth t\<cdot>(snd (def_Buffer_HLR3_Input.sbgetter\<cdot>sb))))"
  shows "eValues\<cdot>(def_Buffer_HLR3_Output.sbgetter\<cdot>(g\<cdot>i)) \<subseteq> eValues\<cdot>(input sb)"
proof(-)
  have "g \<in> daSem stream_split ` (behavior.daset ())"
    by (metis eventGen.daset_sem_eq_esem assms)

  then obtain da where da_def: "da \<in> (behavior.daset ()) \<and> g = daSem stream_split da" by blast
  obtain foo where foo_def: "(dautInitConfig da) = ((StateConstr state__S [] [], foo), \<bottom>)"
    using init_da da_def by blast

  have "eValues\<cdot>(input_efilter\<cdot>i) \<subseteq> eValues\<cdot>(input sb)"
    using input_prefix_eq by(metis SetPcpo.less_set_def assms(4) monofun_cfun_arg)

  then show ?thesis
    apply(simp add: da_def dasem_unfold foo_def)
    apply(rule outputSubsetInput_stream_induction)
    by(simp_all add: da_def)
qed

end
