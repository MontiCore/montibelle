theory hwl_Capacity
  imports sps_Capacity_LLR.def_Capacity_LLR sps_Capacity_HLR3.def_Capacity_HLR3 automaton.Nda2DaSet
  Smart_Isabelle.Smart_Isabelle
begin


lemma msg_in_svalues_of_conc_eshdts:
  assumes "EventMsg x \<in> sValues\<cdot>s1"
  and "Tick \<notin> sValues\<cdot>s1"
shows "x \<in> sValues\<cdot>(eshdts\<cdot>(s1 \<Zcat> s2))"
  apply(simp add: assms EventStream.eshdts_conc_eq)
  by(metis assms(1) imageI inj_EventMsg inv_f_f sValues_sconc smap_sValues subset_iff)

lemma eventFilter_tsrt_subset: "eValues\<cdot>(eventFilter ch\<cdot>(tsrt\<cdot>i)) \<subseteq>
          eValues\<cdot>(eventFilter ch\<cdot>i)"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;simp)
  by (metis evalues_event eventfilter_in eventfilter_notin subset_insertI2)


(* channel lemmas *)

lemma not_input_ctrl:"Rep_msgWithChan z \<noteq> (channel_input_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_output_ctrl:"Rep_msgWithChan z \<noteq> (channel_output_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_control_packet:"Rep_msgWithChan z \<noteq> (channel_control_data, PacketEVENTConstr y)"
  by(cases z,case_tac y;auto simp add: well_def Abs_msgWithChan_inverse)

lemma[simp]:"def_Capacity_HLR3_Input.buildSB (input) channel_input_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) input"
  by (simp add: def_Capacity_HLR3_Input.buildSB_def)

lemma[simp]:"def_Capacity_HLR3_Output.buildSB (control,output)channel_output_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) output"
  by (simp add: def_Capacity_HLR3_Output.buildSB_def)

lemma[simp]:"def_Capacity_HLR3_Output.buildSB (control,output)channel_control_data = (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr))) control"
  by (simp add: def_Capacity_HLR3_Output.buildSB_def)

lemma input_imp_packet:
  assumes "fst (Rep_msgWithChan a) = channel_input_data"
  shows "\<exists>pckt. Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr pckt)"
  by (metis msg.exhaust assms not_input_ctrl prod.collapse)

lemma output_imp_packet:
  assumes "fst (Rep_msgWithChan a) = channel_output_data"
  shows "\<exists>pckt. Rep_msgWithChan a = (channel_output_data, PacketEVENTConstr pckt)"
  by (metis msg.exhaust assms not_output_ctrl prod.collapse)

lemma control_imp_ctrl:
  assumes "fst (Rep_msgWithChan a) = channel_control_data"
  shows "\<exists>ctrl. Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr ctrl)"
  by (metis msg.exhaust assms not_control_packet prod.collapse)

(* input channel abbreviations *)

abbreviation input::"def_Capacity_HLR3_Input.channels\<^sup>\<Omega> \<Rightarrow> Packet event stream" where
  "input sb \<equiv> (def_Capacity_HLR3_Input.sbgetter\<cdot>sb)"

abbreviation input_efilter::"def_Capacity_HLR3_Input.channels msgWithChan event stream \<rightarrow> Packet event stream" where
  "input_efilter \<equiv> (emap (inv PacketEVENTConstr)) oo (eventFilter channel_input_data)"

definition input_sfilter::"def_Capacity_HLR3_Input.channels msgWithChan stream \<Rightarrow> Packet stream" where
  "input_sfilter s = smap (inv PacketEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_input_data} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition inputf::"def_Capacity_HLR3_Input.channels msgWithChan list \<Rightarrow> Packet list" where
 "inputf = (\<lambda>ls. map ((inv PacketEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_input_data) (map Rep_msgWithChan ls)))"

(* lemmas over abbreviations *)

lemma inputf_empty[simp]: "inputf [] = []"
  by(simp add: inputf_def)

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

(* filter_input_noop lemmas *)

lemma efilter_input_noop:"efilter (\<lambda>(c,m). c = channel_input_data)\<cdot>(emap Rep_msgWithChan\<cdot>i) =
    emap Rep_msgWithChan\<cdot>i"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;case_tac ab;simp)
  by (simp add: Abs_msgWithChan_inverse2)

lemma efilter_input_noop2:
  "(efilter (\<lambda>m. fst m = channel_input_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) = (emap Rep_msgWithChan\<cdot>i)"
  using efilter_input_noop by(simp add: case_prod_beta')

lemma sfilter_input_noop:
 "\<forall>t. {m. fst m = channel_input_data} \<ominus> smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i) =
    smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i)"
  by(simp add: efilter_input_noop2 smap_esnth filter_esnth)

(* input eq lemmas *)

lemma input_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "input_efilter\<cdot>i \<sqsubseteq> input sb"
proof(-)
  have h1: "emap (inv PacketEVENTConstr)\<cdot>(emap PacketEVENTConstr\<cdot>(input sb)) = (input sb)"
    by(simp add: emaps2emap)

  obtain x where ab_def: "sb = def_Capacity_HLR3_Input.sbsetter\<cdot>(x)"
    by(metis def_Capacity_HLR3_Input.SB.set_get)
  have "(sb  \<^enum>  channel_input_data) = (smap (Timed o TLive)\<cdot>(emap PacketEVENTConstr\<cdot>(input sb)))"
    apply(simp add: ab_def)
    apply(induction x; simp)
    by(case_tac a; simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_input_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq>
     emap PacketEVENTConstr\<cdot>(input sb)"
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
  obtain x where ab_def: "sb = def_Capacity_HLR3_Input.sbsetter\<cdot>(x)"
     by(metis def_Capacity_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "input sb = emap (inv PacketEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  channel_input_data))"
    apply(simp add: ab_def)
    apply(induction x;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: input_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed

(* ticksb output lemmas *)

lemma sbsetter_ticksb: "def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>Tick, \<up>Tick) = ticksb"
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb: "def_Capacity_HLR3_Output.sbgetter\<cdot>ticksb = (\<up>Tick, \<up>Tick)"
  apply(subst(2) def_Capacity_HLR3_Output.SB.get_set[symmetric])
  apply(rule cfun_arg_cong)
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb2[simp]: "def_Capacity_HLR3_Output.sbgetter\<cdot>(ticksb \<Zcat>\<Zcat> s) =
  (\<up>Tick, \<up>Tick) \<Zcat>\<Zcat> def_Capacity_HLR3_Output.sbgetter\<cdot>s"
  by(simp add: sbgetter_ticksb conc_sb_def getter_conc2sbconc[symmetric])

(* usplit out lemmas *)

lemma usplit_event_sbsetter_output_list:
"uSplit\<cdot>(smap EventMsg\<cdot>(smap channel_Capacity_HLR3_output_dataConstr\<cdot>(<ls>))) =
def_Capacity_HLR3_Output.sbsetter\<cdot>(\<epsilon>, smap EventMsg\<cdot>(<ls>))"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= channel_output_data and m="PacketEVENTConstr a"])
  apply(simp_all add: channel_Capacity_HLR3_output_dataConstr.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_output:"(uSplit\<cdot>(\<up>(EventMsg (channel_Capacity_HLR3_output_dataConstr a)) \<Zcat> s)) =
def_Capacity_HLR3_Output.sbsetter\<cdot>(\<epsilon>,\<up>(EventMsg a)) \<Zcat>\<Zcat> (uSplit\<cdot>s)"
  using usplit_event_sbsetter_output_list[where ls="[a]"] apply simp
  by (simp add: usplit_conc)?

lemma usplit_event_sbsetter_control_list:
"uSplit\<cdot>(smap EventMsg\<cdot>(smap channel_Capacity_HLR3_control_dataConstr\<cdot>(<ls>))) =
def_Capacity_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<ls>), \<epsilon>)"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= channel_control_data and m="CtrlEnumEVENTConstr a"])
  apply(simp_all add: channel_Capacity_HLR3_control_dataConstr.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_control:"(uSplit\<cdot>(\<up>(EventMsg (channel_Capacity_HLR3_control_dataConstr a)) \<Zcat> s)) =
def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg a),\<epsilon>) \<Zcat>\<Zcat> (uSplit\<cdot>s)"
  using usplit_event_sbsetter_control_list[where ls="[a]"] apply simp
  by (simp add: usplit_conc)?

lemma somethingexists[simp]:"(\<exists>packet. Rep_msgWithChan aa = (channel_input_data, PacketEVENTConstr packet))"
  apply(cases aa;case_tac y;case_tac a;case_tac b;simp add: well_def)
  using not_input_ctrl not_control_packet apply blast?
  by(subst Abs_msgWithChan_inverse,simp_all add: well_def)+

(* automaton transition lemmas *)

lemma init_nda: "autInitConfig\<cdot>(behavior.eaut param) = {(StateConstr state__Send param, ticksb)}"
  apply(simp add: behavior.config_def)
  by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)

lemma init_da:
  assumes "da \<in> (behavior.daset param)"
shows "\<exists>foo. (dautInitConfig da) = ((StateConstr state__Send param, foo), ticksb)"
proof(-)
  have "apfst fst (dautInitConfig da) = (StateConstr state__Send param, ticksb)"
    using init_nda nda2da_init eventGen.daset_def assms by (metis singleton_iff)
  then show ?thesis
    by(metis eq_fst_iff snd_conv tuple_to_apfst)
qed

lemma size_le_cap_nda:
  assumes "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
  and "x \<le> cap"
shows "((autTransition\<cdot>(behavior.eaut param)) (StateConstr state__Send cap) (EventMsg pckt)) =
      {((StateConstr state__Send (cap-x)),
        def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg ACK), \<up>(EventMsg (PacketConstr x))))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms apply(simp)
  using usplit_event_sbsetter_control usplit_event_sbsetter_output[where a="(PacketConstr x)" and s=\<epsilon>] apply(simp)
  by(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)

lemma size_le_cap_da:
  assumes "da \<in> (behavior.daset param)"
  and "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
  and "x \<le> cap"
shows "\<exists>bar. dautTransition da (StateConstr state__Send cap, foo) (EventMsg pckt) =
       ((StateConstr state__Send (cap - x), bar),
        def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg ACK), \<up>(EventMsg (PacketConstr x))))"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__Send cap, foo) (EventMsg pckt)) =
    (StateConstr state__Send (cap-x),
       def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg ACK), \<up>(EventMsg (PacketConstr x))))"
    using size_le_cap_nda nda2da_trans eventGen.daset_def assms by fastforce

  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma size_gt_cap_nda:
  assumes "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
  and "x > cap"
shows "((autTransition\<cdot>(behavior.eaut param)) (StateConstr state__Send cap) (EventMsg pckt)) =
      {((StateConstr state__Block (cap)),
        def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg NAK), \<epsilon>))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms usplit_event_sbsetter_control[where s=\<epsilon>] by(simp)

lemma size_gt_cap_da:
  assumes "da \<in> (behavior.daset param)"
  and "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
  and "x > cap"
shows "\<exists>bar. dautTransition da (StateConstr state__Send cap, foo) (EventMsg pckt) =
       ((StateConstr state__Block cap, bar), def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg NAK), \<epsilon>))"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__Send cap, foo) (EventMsg pckt)) =
    (StateConstr state__Block cap,
       def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg NAK), \<epsilon>))"
    using size_gt_cap_nda nda2da_trans eventGen.daset_def assms by fastforce

  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma block_nda:
  assumes "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
shows "((autTransition\<cdot>(behavior.eaut param)) (StateConstr state__Block cap) (EventMsg pckt)) =
      {((StateConstr state__Block cap), \<bottom>)}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  by(simp add: assms)

lemma block_da:
  assumes "da \<in> (behavior.daset param)"
  and "Rep_msgWithChan pckt = (channel_input_data, PacketEVENTConstr (PacketConstr x))"
shows "\<exists>bar. dautTransition da (StateConstr state__Block cap, foo) (EventMsg pckt) =
       ((StateConstr state__Block cap, bar), bottom)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state__Block cap, foo) (EventMsg pckt)) =
    (StateConstr state__Block cap, \<bottom>)"
    using block_nda nda2da_trans eventGen.daset_def assms by fastforce

  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

lemma tick_nda:
shows "((autTransition\<cdot>(behavior.eaut param)) (StateConstr state cap) Tick) =
      {((StateConstr state__Send param), ticksb)}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_tickC_def)
  by(case_tac state;simp)

lemma tick_da:
  assumes "da \<in> (behavior.daset param)"
shows "\<exists>bar. dautTransition da (StateConstr state cap, foo) Tick =
       ((StateConstr state__Send param, bar), ticksb)"
proof(-)
   have "apfst fst (dautTransition da (StateConstr state cap, foo) Tick) =
          ((StateConstr state__Send param), ticksb)"
    using tick_nda nda2da_trans eventGen.daset_def assms by fastforce

  then show ?thesis
    by (metis Pair_inject prod.collapse tuple_to_apfst)
qed


lemma getch_to_getter_fst:"(out \<^enum> channel_control_data) =
  (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr)))
  (fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))"
proof -
  obtain s1 s2 where s12_def:"(s1,s2) = (def_Capacity_HLR3_Output.sbgetter\<cdot>(out))"
    using prod.collapse by blast

  have setter_def:"out = SB.setter\<cdot>(s1,s2)"
    by (simp add: s12_def)

  show ?thesis
    apply(subst setter_def)
    apply(subst SB.setter_getch)
    apply(subst buildSB_def)
    apply(subst channelsChan.simps(1))
    using s12_def  by (metis fst_conv)
qed

lemma getch_to_getter_snd:"(out \<^enum> channel_output_data) =
  (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr)))
  (snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))"
proof -
  obtain s1 s2 where s12_def:"(s1,s2) = (def_Capacity_HLR3_Output.sbgetter\<cdot>(out))"
    using prod.collapse by blast

  have setter_def:"out = SB.setter\<cdot>(s1,s2)"
    by (simp add: s12_def)

  show ?thesis
    apply(subst setter_def)
    apply(subst SB.setter_getch)
    apply(subst buildSB_def)
    apply(subst channelsChan.simps(2))
    using s12_def by (metis snd_conv)
qed

lemma svalues_getch_subset_sbvalues:
"\<And> c::channels. sValues\<cdot>(out \<^enum> c) \<subseteq> (snd ` sbValues\<cdot>(out))"
  apply(case_tac c)
proof -
  fix c assume c_def:"c = channel_control_data"
  have "Pair channel_control_data ` sValues\<cdot>(
    (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr))
    (fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))))
    \<subseteq> sbValues\<cdot>(out)"
    apply(simp add:getch_to_getter_fst[symmetric])
    apply(rule subsetI)
    apply(subst sbValues_def)
    apply(subst Abs_cfun_inverse2)
    using sbvalues_cont apply blast
    apply(subst Union_iff)
    using chdom_in somechannotempty by blast

  thus "sValues\<cdot>(out \<^enum> c)
    \<subseteq> (snd ` sbValues\<cdot>(out))"
    apply(subst c_def)
    apply(simp add:getch_to_getter_fst[symmetric])
    by (metis (mono_tags, lifting) image_subset_iff snd_conv subsetI)
next
  fix c assume c_def:"c = channel_output_data"
  have "Pair channel_output_data ` sValues\<cdot>(
    (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))
    (snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))))
    \<subseteq> sbValues\<cdot>(out)"
    apply(simp add:getch_to_getter_snd[symmetric])
    apply (rule subsetI)
    apply(subst sbValues_def)
    apply(subst Abs_cfun_inverse2)
    using sbvalues_cont apply blast
    apply(subst Union_iff)
    using chdom_in somechannotempty by blast

  thus "sValues\<cdot>(out \<^enum> c)
    \<subseteq> (snd ` sbValues\<cdot>(out))"
    apply(subst c_def)
    apply(simp add:getch_to_getter_snd[symmetric])
    by (metis (mono_tags, lifting) image_subset_iff snd_conv subsetI)
qed

lemma getter_preserves_no_tick:
  assumes "\<And> m. m \<in> (snd ` sbValues\<cdot>(out)) \<Longrightarrow> #\<^sub>\<surd> m = 0"
  shows "Tick \<notin> sValues\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>out)) \<and>
         Tick \<notin> sValues\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>out))"
  apply auto
proof -
  assume tick:"Tick \<in> sValues\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))"
  hence "(Timed (TLive (Tick))) \<in> sValues\<cdot>(out \<^enum> channel_control_data)"
    apply(subst getch_to_getter_fst)
    by (simp add: smap_sValues)
  hence "(Timed (TLive (Tick))) \<in> (snd ` sbValues\<cdot>(out))"
    using svalues_getch_subset_sbvalues by blast
  with assms show False
    by (metis tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlent)
next
  assume tick:"Tick \<in> sValues\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(out)))"
  hence "(Timed (TLive (Tick))) \<in> sValues\<cdot>(out \<^enum> channel_output_data)"
    apply(subst getch_to_getter_snd)
    by (simp add: smap_sValues)
  hence "(Timed (TLive (Tick))) \<in> (snd ` sbValues\<cdot>(out))"
    using svalues_getch_subset_sbvalues by blast
  with assms show False
    by (metis tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlent)
qed

lemma getter_preserves_len_finite:
  assumes "\<And>c. #(out  \<^enum> c) < \<infinity>"
  shows "#(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>out)) < \<infinity> \<and>
         #(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>out)) < \<infinity> "
  apply (rule conjI)
  apply (metis assms getch_to_getter_fst slen_smap)
  by (metis assms getch_to_getter_snd slen_smap)


lemma no_tick_from_eventgen:
  assumes "da \<in> (behavior.daset param)"
  shows "Tick \<notin> sValues\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))
      \<and> Tick \<notin> sValues\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))"
  apply(rule conjI)
  apply(subst getter_preserves_no_tick[where out="(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param=param])
    apply(simp_all add:assms)
  apply(subst getter_preserves_no_tick[where out="(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param=param])
  by(simp_all add:assms)

lemma not_inf_from_eventgen:
  assumes "da \<in> (behavior.daset param)"
  shows "#(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))
      < \<infinity>
    \<and> #(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))
      < \<infinity>"
  apply(rule conjI)
  apply(subst getter_preserves_len_finite[where out="(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param=param])
  using assms apply blast
    apply simp+
  apply(subst getter_preserves_len_finite[where out="(snd
      (multTransitionsInOne da (StateConstr state cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param=param])
  using assms apply blast
  by simp+

lemma acks_match_input_len:
  assumes "da \<in> (behavior.daset param)"
    and "EventMsg NAK \<notin> sValues\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
    (multTransitionsInOne da (StateConstr state__Send cap, foo) (map EventMsg ls)))))"
  shows "fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(snd
    (multTransitionsInOne da (StateConstr state__Send cap, foo) (map EventMsg ls)))) =
   (smap EventMsg\<cdot>(list2s (replicate (length ls) ACK)))"
  apply(insert assms)
proof(induction ls arbitrary: cap foo)
  case Nil
  then show ?case by simp
next
  case (Cons a ls)

  obtain x where x_def: "Rep_msgWithChan a = (channel_input_data,PacketEVENTConstr (PacketConstr x))"
    by(metis Packet_get_size.cases somethingexists)

  show ?case
  proof(cases "x \<le> cap")
    case True

    obtain bar where bar_def:
      "dautTransition da (StateConstr state__Send cap, foo) (EventMsg a) =
        ((StateConstr state__Send (cap - x), bar),
         def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg ACK), \<up>(EventMsg (PacketConstr x))))"
      using size_le_cap_da True Cons.prems x_def
      by(blast)

    have unfold_step: "fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
        (snd (multTransitionsInOne da (StateConstr state__Send cap, foo) (map EventMsg (a # ls))))) =
      \<up>(EventMsg ACK) \<Zcat> fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
        (snd (multTransitionsInOne da (StateConstr state__Send (cap - x), bar) (map EventMsg ls))))"
      apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])
      by(simp add: bar_def)

    show ?thesis
      apply(subst unfold_step)
      apply(subst Cons.IH)
      apply(simp_all add: Cons.prems)
      using Cons.prems(2) by(subst(asm) unfold_step,simp)
  next
    case False

    obtain bar where bar_def:
      "dautTransition da (StateConstr state__Send cap, foo) (EventMsg a) =
        ((StateConstr state__Block cap, bar),
         def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg NAK), \<epsilon>))"
      using size_gt_cap_da False Cons.prems x_def by(meson linorder_le_less_linear)

    have unfold_step: "fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
        (snd (multTransitionsInOne da (StateConstr state__Send cap, foo) (map EventMsg (a # ls))))) =
      \<up>(EventMsg NAK) \<Zcat> fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
        (snd (multTransitionsInOne da (StateConstr state__Block cap, bar) (map EventMsg ls))))"
      apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])
      by(simp add: bar_def)

    show ?thesis
      apply(subst unfold_step)
      using Cons.prems(2) by(subst(asm) unfold_step,simp)
  qed
qed

lemma da_tick_output:
  assumes "da \<in> (behavior.daset param)"
shows "\<exists>bar. def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state cap, foo)\<cdot>(\<up>Tick \<Zcat> tsrt\<cdot>i)) =
  (\<up>Tick, \<up>Tick) \<Zcat>\<Zcat> def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send param, bar)\<cdot>(tsrt\<cdot>i))"
proof(-)
  obtain bar where bar_def:
    "dautTransition da (StateConstr state cap, foo) Tick = ((StateConstr state__Send param, bar), ticksb)"
    using tick_da assms by metis

  show ?thesis
    apply(subst dastatesem_step)
    apply(simp add: bar_def)
    by blast
qed

lemma controlMessageSemantics_induction:
  assumes "da \<in> (behavior.daset param)"
    and "spf = daStateSem stream_split da (StateConstr state__Send param, foo)"
    and "#\<^sub>\<surd> i = \<infinity>"
shows "#(esnth t\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>i)))) =
       #(esnth t\<cdot>i) \<or>
       NAK \<in> sValues\<cdot>(esnth t\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>i))))"
  using assms apply(auto)
proof(induction t arbitrary: i spf foo)
  case 0

  have h1: "EventMsg NAK \<in> sValues\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
             (snd (multTransitionsInOne da (StateConstr state__Send param, foo)
                    (map EventMsg (s2list (eshdts\<cdot>i))))))) \<Longrightarrow>
    NAK \<in> sValues\<cdot>(esnth 0\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
              (daStateSem stream_split da (StateConstr state__Send param, foo)\<cdot>i))))"
    apply(subst s_split_list[where s=i])
    apply(metis "0.prems"(3) Inf'_neq_0 tlentosvalues)
    apply(simp)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps)
    apply(simp add: case_prod_beta conc_sb_def getter_conc2sbconc[symmetric] conc_prod_def)
    apply(rule msg_in_svalues_of_conc_eshdts)
     apply simp
    by(simp add: "0.prems" no_tick_from_eventgen[where param=param])

  obtain a b where ab_def: "fst (multTransitionsInOne da (StateConstr state__Send param, foo) (map EventMsg (s2list (eshdts\<cdot>i)))) = (a, b)"
    by fastforce

  then obtain bar where bar_def: "fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (a, b)\<cdot>(\<up>Tick \<Zcat> tsrt\<cdot>i))) =
    \<up>Tick \<Zcat> fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send param, bar)\<cdot>(tsrt\<cdot>i)))"
    apply(cases a;simp)
    using da_tick_output assms conc_prod_fst by(metis(no_types) conc_stream_def)

  show ?case
    apply(subst s_split_list[where s=i])
    apply(metis "0.prems"(3) Inf'_neq_0 tlentosvalues)
    apply(simp)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps)
    apply(simp add: case_prod_beta conc_sb_def getter_conc2sbconc[symmetric] conc_prod_def)
    apply(subst acks_match_input_len[where param=param])
    apply(simp add: "0.prems")
    using "0.prems"(4) h1 apply(blast)
    apply(simp add: ab_def bar_def)
    apply(subst eshdts_split_eq, simp_all)
    by(metis "0.prems"(3) Inf'_neq_0 list2streamFin s2l2s_eq eshdts_len tlentosvalues)
next
  case (Suc t)

  obtain a b where ab_def: "fst (multTransitionsInOne da (StateConstr state__Send param, foo) (map EventMsg (s2list (eshdts\<cdot>i)))) = (a, b)"
    by fastforce

  then obtain bar where bar_def: "fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (a, b)\<cdot>(\<up>Tick \<Zcat> tsrt\<cdot>i))) =
    \<up>Tick \<Zcat> fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send param, bar)\<cdot>(tsrt\<cdot>i)))"
    apply(cases a;simp)
    using da_tick_output assms conc_prod_fst by(metis(no_types) conc_stream_def)

  have unfold_step:
  "esnth (Suc t)\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
     (daStateSem stream_split da (StateConstr state__Send param, foo)\<cdot>i))) =
   esnth t\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>
     (daStateSem stream_split da (StateConstr state__Send param, bar)\<cdot>(tsrt\<cdot>i))))"
    apply(subst s_split_list[where s=i])
    apply(metis Inf'_neq_0 Suc.prems(3) tlentosvalues)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps)
    apply(simp add: case_prod_beta conc_sb_def getter_conc2sbconc[symmetric] conc_prod_def)
    apply(subst esnth_dropfst)
    using no_tick_from_eventgen Suc.prems apply(blast)+
    using Suc.prems(1) not_inf_from_eventgen apply blast
    by(simp add: ab_def bar_def)

  show ?case
    apply(subst unfold_step)
    apply(subst(2) s_split_list[where s=i])
    apply(metis Inf'_neq_0 Suc.prems(3) tlentosvalues)
    apply(subst esnth_dropfst;simp)
    apply(rule Suc.IH)
    using assms(1) apply blast
    apply(simp_all add: Suc.prems)
    apply(metis Inf'_neq_0 Suc.prems(3) fold_inf lnat.sel_rews(2) tsrt_tlen tlentosvalues)
    using Suc.prems unfold_step by fastforce
qed

lemma controlMessageSemantics_after_bundlemergepred:
  assumes "spf \<in> mergeTimed \<then> eSem (behavior.eaut cap)"
      and "wellformed (input sb)"
      and "g \<in> eSem (behavior.eaut cap)"
      and "uSplit\<cdot>i \<sqsubseteq> sb"
      and "#\<^sub>\<surd>sb = #\<^sub>\<surd>i"
      and "#sb = \<infinity>"
      and "(\<forall>v::Packet \<in> eValues\<cdot>(input sb). Packet_get_size v < cap)"
shows "\<forall>t. #(esnth (Suc t)\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(g\<cdot>i)))) =
            #(esnth t\<cdot>(input sb)) \<or>
        NAK \<in> sValues\<cdot>(esnth (Suc t)\<cdot>(fst (def_Capacity_HLR3_Output.sbgetter\<cdot>(g\<cdot>i))))"
proof(-)
  have i_inf: "#\<^sub>\<surd>i = \<infinity>"
    by (metis assms(2) assms(5) assms(6) def_Capacity_HLR3_Input.SB.getter_len
        def_Capacity_HLR3_Input.SB.getter_tlen somechannotempty wellformed_stream_def)

  have "g \<in> daSem stream_split ` (behavior.daset cap)"
    by (metis eventGen.daset_sem_eq_esem assms(3))

  then obtain da where da_def: "da \<in> (behavior.daset cap) \<and> g = daSem stream_split da"
    using assms(3) by blast
  obtain foo where foo_def: "(dautInitConfig da) = ((StateConstr state__Send cap, foo), ticksb)"
    using init_da da_def by blast

  show ?thesis
    apply(subst da_def)+
    apply(simp add: dasem_unfold foo_def)
    apply(simp add: input_esnth_eq[where i=i and sb=sb] i_inf assms(4))
    apply(subst input_sfilter_def)
    apply(simp add: sfilter_input_noop)
    apply(subst controlMessageSemantics_induction)
    by(simp_all add: i_inf da_def)
qed

lemma infManyOutputMessages_induction:
  assumes "da \<in> (behavior.daset cap)"
  and "#\<^sub>\<surd> i = \<infinity>"
  and "\<And>v. v \<in> eValues\<cdot>(input_efilter\<cdot>i) \<Longrightarrow> Packet_get_size v \<le> cap"
  and "\<And>n. 0 < #(esnth n\<cdot>i)"
  and "state = (StateConstr state__Send cap, foo)"
shows "0 < #(esnth n\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>((daStateSem stream_split da state)\<cdot>i))))"
  using assms apply auto
proof(induction n arbitrary: i foo state)
  case 0

  obtain a rest where a_def: "i = \<up>a \<Zcat> rest"
    using "0.prems"(2) by (metis eventlenleqlen inf_less_eq inf_scase)
  then obtain aa where aa_def: "a = EventMsg aa"
    apply(cases a;simp)
    using "0.prems"(4)[of 0] by simp
  obtain nat where nat_def:
      "Rep_msgWithChan aa = (channel_input_data,PacketEVENTConstr (PacketConstr nat))"
    by (metis Packet.exhaust somethingexists)

  show ?case
  proof(cases "nat \<le> cap")
    case True

    obtain bar where bar_def:
      "dautTransition da (StateConstr state__Send cap, foo) (EventMsg aa) =
          ((StateConstr state__Send (cap-nat), bar),
           def_Capacity_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg ACK), \<up>(EventMsg (PacketConstr nat))))"
      using size_le_cap_da True nat_def "0.prems"(1) by metis

    then show ?thesis
      apply(simp add: a_def aa_def)
      apply(subst dastatesem_step)
      apply(simp add: bar_def)
      apply(simp add: conc_sb_def getter_conc2sbconc[symmetric])
      by(simp add: eshdts_event)
  next
    case False
    have "PacketConstr nat \<in> eValues\<cdot>(input_efilter\<cdot>i)"
      using a_def aa_def nat_def by simp
    then show ?thesis
      using "0.prems"(3)[where v="(PacketConstr nat)"] "0.prems" False by auto
  qed
next
  case (Suc n)

  obtain a b where ab_def: "fst (multTransitionsInOne da (StateConstr state__Send cap, foo) (map EventMsg (s2list (eshdts\<cdot>i)))) = (a, b)"
    by fastforce

  then obtain bar where bar_def: "snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (a, b)\<cdot>(\<up>Tick \<Zcat> tsrt\<cdot>i))) =
    \<up>Tick \<Zcat> snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send cap, bar)\<cdot>(tsrt\<cdot>i)))"
    apply(cases a;simp)
    using da_tick_output Suc.prems conc_prod_snd  by(metis(no_types) conc_stream_def)

  show ?case
    apply(subst s_split_list[where s=i])
    apply(metis Inf'_neq_0 Suc.prems(2) tlentosvalues)
    apply(subst smap2map)
    apply(subst dastatesem_x_steps)
    apply(simp add: case_prod_beta conc_sb_def getter_conc2sbconc[symmetric] conc_prod_def)
    apply(subst esnth_dropfst)
    prefer 3
    apply(simp add: ab_def bar_def)
    apply(rule Suc.IH)
    using assms(1) apply blast
    apply(metis Inf'_neq_0 Suc.prems(2) fold_inf inject_lnsuc tsrt_tlen tlentosvalues)
    using Suc.prems(3) apply (simp add:emap_evalues)
    using eventFilter_tsrt_subset apply blast
       apply(metis Suc.prems(4) esnth_tsrt)
    apply blast
    using assms(1) no_tick_from_eventgen apply blast
    using assms(1) not_inf_from_eventgen by blast
qed

lemma infManyOutputMessages_after_bundlemergepred:
  assumes "spf \<in> mergeTimed \<then> eSem (behavior.eaut cap)"
      and "wellformed (input sb)"
      and "g \<in> eSem (behavior.eaut cap)"
      and "uSplit\<cdot>i \<sqsubseteq> sb"
      and "#\<^sub>\<surd>sb = #\<^sub>\<surd>i"
      and "#(input sb) = \<infinity>"
      and "\<forall>v \<in> eValues\<cdot>(input sb). Packet_get_size v < cap"
      and "\<forall>t. 0 < #(esnth t\<cdot>(input sb))"
  shows "#(e2ustream\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(g\<cdot>i)))) = \<infinity>"
proof(-)
  have "g \<in> daSem stream_split ` (behavior.daset cap)"
    by (metis eventGen.daset_sem_eq_esem assms(3))

  then obtain da where da_def: "da \<in> (behavior.daset cap) \<and> g = daSem stream_split da" by blast
  obtain foo where foo_def: "(dautInitConfig da) = ((StateConstr state__Send cap, foo), ticksb)"
    using init_da da_def by blast

  have "#\<^sub>\<surd> sb = \<infinity>"
      by (metis assms(2) assms(6)
        def_Capacity_HLR3_Input.SB.getter_tlen somechannotempty wellformed_stream_def)
  then have i_inf: "#\<^sub>\<surd> i = \<infinity>"
    using assms(5) by simp

  then have "#\<^sub>\<surd>(g\<cdot>i) = \<infinity>"
    using assms(3) behavior.eaut_strong strong_def
    by(metis fold_inf inf_less_eq)
  then have output_inf_ticks: "#\<^sub>\<surd> (snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(g\<cdot>i))) = \<infinity>"
    by(metis def_Capacity_HLR3_Output.SB.getter_tlen inf_less_eq tlen_prod_le_tlen_snd somechannotempty)

  have ass0_induction: "#\<^sub>\<surd> i = \<infinity>"
    by (metis assms(2) assms(5) assms(6)
        def_Capacity_HLR3_Input.SB.getter_tlen somechannotempty wellformed_stream_def)

  have ass1_induction:"\<And>v. v \<in> eValues\<cdot>(input_efilter\<cdot>i) \<Longrightarrow>
          Packet_get_size v \<le> cap"
    using assms(4) input_evalues_subset assms(7) less_or_eq_imp_le
      by blast

  have ass2_induction:"\<And>n. 0 < #(esnth n\<cdot>i)"
    proof -
      have "\<And>n. input_sfilter (esnth n\<cdot>i) = (esnth n\<cdot>(input sb))"
        apply (subst input_esnth_eq)
        by(simp_all add:assms i_inf)
      moreover have "\<And>n. #(esnth n\<cdot>i) = #(input_sfilter (esnth n\<cdot>i))"
        apply(subst input_sfilter_def;simp)
        using sfilter_input_noop by simp
      ultimately have "\<And>n. #(esnth n\<cdot>i) = #(esnth n\<cdot>(input sb))"
        by simp

      thus "\<And>n. 0 < #(esnth n\<cdot>i)" using assms(8) by simp
    qed

  have "#\<^sub>\<surd>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send cap, foo)\<cdot>i))) \<le>
        #(e2ustream\<cdot>(snd (def_Capacity_HLR3_Output.sbgetter\<cdot>(daStateSem stream_split da (StateConstr state__Send cap, foo)\<cdot>i))))"
    apply(rule tlen2e2ustreamlen)
    apply(rule infManyOutputMessages_induction)
    apply(simp_all add: i_inf da_def)
    by(simp_all add:ass0_induction ass1_induction ass2_induction)


  then show ?thesis
    using output_inf_ticks apply(simp add: da_def dasem_unfold foo_def)
    by(metis inf_less_eq lnat_suc_plus lnsuc_inf)
qed


lemma predicate_0_llr:
  assumes "spf \<in> def_Capacity_LLR.Sps cap"
    and "wellformed (def_Capacity_HLR3_Input.sbgetter\<cdot>sb)"
  shows "assumption_0 cap (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<and>
         assumption_1 cap (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<and>
         assumption_2 cap (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<longrightarrow>
         predicate_0 cap (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: def_Capacity_LLR.Sps_def behavior.Sem_def)
  apply(rule bundlemergepred[where SPS="eSem (behavior.eaut cap)"])
  apply(simp)
  apply(simp add: assumption_0_def assumption_1_def assumption_2_def predicate_0_def)
  apply(simp add: case_prod_beta len_stream_def[symmetric])?
  using infManyOutputMessages_after_bundlemergepred controlMessageSemantics_after_bundlemergepred
  by simp

lemma causality_llr:
  assumes "spf \<in> def_Capacity_LLR.Sps cap"
  shows "causality (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  apply(simp add: causality_def strongpred_def)
  using assms by(metis behavior.sem_strong def_Capacity_LLR.Sps_def strong2pred strongpred_def)

lemma wholePredicate_llr:
  assumes "spf \<in> def_Capacity_LLR.Sps cap"
  shows "wholePredicate cap (def_Capacity_HLR3_Input.sbgetter\<cdot>sb) (def_Capacity_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: wholePredicate_def)
  by(simp add: predicate_0_llr causality_llr)

lemma refinement[simp]: "def_Capacity_LLR.Sps (cap) \<subseteq> def_Capacity_HLR3.Sps (cap)"
  by(simp add: def_Capacity_HLR3.Sps_def subsetI wholePredicate_llr)

end
