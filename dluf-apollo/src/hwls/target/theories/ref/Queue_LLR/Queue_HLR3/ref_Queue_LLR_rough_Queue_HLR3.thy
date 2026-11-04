theory ref_Queue_LLR_rough_Queue_HLR3
  imports
    (* Gen *) Smart_Isabelle.Smart_Isabelle
              sps_Buffer_HLR3.def_Buffer_HLR3 sps_Buffer_LLR.def_Buffer_LLR
    (* Hwl  *) hwl_Buffer.hwl_Buffer

begin



(* channel lemmas *)

lemma not_channel_control_data_Packet: "Rep_msgWithChan z \<noteq> (channel_control_data, PacketEVENTConstr x)"
  by(cases z,case_tac x;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_channel_input_data_CtrlEnum: "Rep_msgWithChan z \<noteq> (channel_input_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac x;auto simp add: well_def Abs_msgWithChan_inverse)

lemma not_channel_output_data_CtrlEnum: "Rep_msgWithChan z \<noteq> (channel_output_data, CtrlEnumEVENTConstr x)"
  by(cases z,case_tac x;auto simp add: well_def Abs_msgWithChan_inverse)

lemma[simp]:"def_Buffer_HLR3_Input.buildSB (channel_control_data_pattern, channel_input_data_pattern) channel_control_data = (Rep_cfun (smap (Timed o TLive o map_event CtrlEnumEVENTConstr))) channel_control_data_pattern"
  by(simp add: def_Buffer_HLR3_Input.buildSB_def)

lemma[simp]:"def_Buffer_HLR3_Input.buildSB (channel_control_data_pattern, channel_input_data_pattern) channel_input_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) channel_input_data_pattern"
  by(simp add: def_Buffer_HLR3_Input.buildSB_def)

lemma[simp]:"def_Buffer_HLR3_Output.buildSB (channel_output_data_pattern) channel_output_data = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) channel_output_data_pattern"
  by(simp add: def_Buffer_HLR3_Output.buildSB_def)

lemma channel_control_data_imp_CtrlEnum:
  assumes "fst (Rep_msgWithChan a) = channel_control_data"
  shows "\<exists>m. Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr m)"
  by(metis msg.exhaust assms prod.collapse not_channel_control_data_Packet not_channel_input_data_CtrlEnum not_channel_output_data_CtrlEnum)

lemma channel_input_data_imp_Packet:
  assumes "fst (Rep_msgWithChan a) = channel_input_data"
  shows "\<exists>m. Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr m)"
  by(metis msg.exhaust assms prod.collapse not_channel_control_data_Packet not_channel_input_data_CtrlEnum not_channel_output_data_CtrlEnum)

lemma channel_output_data_imp_Packet:
  assumes "fst (Rep_msgWithChan a) = channel_output_data"
  shows "\<exists>m. Rep_msgWithChan a = (channel_output_data, PacketEVENTConstr m)"
  by(metis msg.exhaust assms prod.collapse not_channel_control_data_Packet not_channel_input_data_CtrlEnum not_channel_output_data_CtrlEnum)


(* input channel abbreviations *)

abbreviation channel_control_dataAbbr::"def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<Rightarrow> CtrlEnum event stream" where
  "channel_control_dataAbbr sb \<equiv> (fst (def_Buffer_HLR3_Input.sbgetter\<cdot>sb))"

abbreviation channel_control_data_efilter::"def_Buffer_HLR3_Input.channels msgWithChan event stream \<rightarrow> CtrlEnum event stream" where
  "channel_control_data_efilter \<equiv> (emap (inv CtrlEnumEVENTConstr)) oo (eventFilter channel_control_data)"

definition channel_control_data_sfilter::"def_Buffer_HLR3_Input.channels msgWithChan stream \<Rightarrow> CtrlEnum stream" where
  "channel_control_data_sfilter s = smap (inv CtrlEnumEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_control_data} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition channel_control_dataf::"def_Buffer_HLR3_Input.channels msgWithChan list \<Rightarrow> CtrlEnum list" where
  "channel_control_dataf = (\<lambda>ls. map ((inv CtrlEnumEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_control_data) (map Rep_msgWithChan ls)))"

abbreviation channel_input_dataAbbr::"def_Buffer_HLR3_Input.channels\<^sup>\<Omega> \<Rightarrow> Packet event stream" where
  "channel_input_dataAbbr sb \<equiv>  (snd (def_Buffer_HLR3_Input.sbgetter\<cdot>sb))"

abbreviation channel_input_data_efilter::"def_Buffer_HLR3_Input.channels msgWithChan event stream \<rightarrow> Packet event stream" where
  "channel_input_data_efilter \<equiv> (emap (inv PacketEVENTConstr)) oo (eventFilter channel_input_data)"

definition channel_input_data_sfilter::"def_Buffer_HLR3_Input.channels msgWithChan stream \<Rightarrow> Packet stream" where
  "channel_input_data_sfilter s = smap (inv PacketEVENTConstr)\<cdot>(smap snd\<cdot>({m. fst m = channel_input_data} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition channel_input_dataf::"def_Buffer_HLR3_Input.channels msgWithChan list \<Rightarrow> Packet list" where
  "channel_input_dataf = (\<lambda>ls. map ((inv PacketEVENTConstr) o snd) (filter (\<lambda>m. fst m = channel_input_data) (map Rep_msgWithChan ls)))"


(* lemmas over abbreviations *)

lemma channel_control_dataf_empty[simp]:"channel_control_dataf [] = []"
  by(simp add: channel_control_dataf_def)

lemma channel_control_dataf_channel_control_data[simp]:
  assumes "Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr m)"
  shows "channel_control_dataf (a#ls) = m # channel_control_dataf ls"
  by(simp add: assms channel_control_dataf_def)

lemma channel_control_dataf_channel_input_data[simp]:
  assumes "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr m)"
  shows "channel_control_dataf (a#ls) = channel_control_dataf ls"
  by(simp add: assms channel_control_dataf_def)

lemma channel_control_data_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "channel_control_data_sfilter s = <(channel_control_dataf (s2list s))>"
  apply(simp add: channel_control_data_sfilter_def channel_control_dataf_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)

lemma channel_input_dataf_empty[simp]:"channel_input_dataf [] = []"
  by(simp add: channel_input_dataf_def)

lemma channel_input_dataf_channel_control_data[simp]:
  assumes "Rep_msgWithChan a = (channel_control_data, CtrlEnumEVENTConstr m)"
  shows "channel_input_dataf (a#ls) = channel_input_dataf ls"
  by(simp add: assms channel_input_dataf_def)

lemma channel_input_dataf_channel_input_data[simp]:
  assumes "Rep_msgWithChan a = (channel_input_data, PacketEVENTConstr m)"
  shows "channel_input_dataf (a#ls) = m # channel_input_dataf ls"
  by(simp add: assms channel_input_dataf_def)

lemma channel_input_data_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "channel_input_data_sfilter s = <(channel_input_dataf (s2list s))>"
  apply(simp add: channel_input_data_sfilter_def channel_input_dataf_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)


(* filter_input_noop lemmas *)

lemma efilter_input_noop:
  "efilter (\<lambda>(c,m). (c = channel_control_data) \<or> (c = channel_input_data))
    \<cdot>(emap Rep_msgWithChan\<cdot>i) = emap Rep_msgWithChan\<cdot>i"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;case_tac ab;simp)
  by (simp add: Abs_msgWithChan_inverse2)+

lemma efilter_input_noop2:
  "(efilter (\<lambda>m. (fst m = channel_control_data) \<or> (fst m = channel_input_data))
    \<cdot>(emap Rep_msgWithChan\<cdot>i)) = (emap Rep_msgWithChan\<cdot>i)"
  using efilter_input_noop by(simp add: case_prod_beta')

lemma sfilter_input_noop:
  "\<forall>t. {m. (fst m = channel_control_data) \<or> (fst m = channel_input_data)}
  \<ominus> smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i) = smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i)"
  by(simp add: efilter_input_noop2 smap_esnth filter_esnth)


(* input eq lemmas *)

lemma channel_control_data_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "channel_control_data_efilter\<cdot>i \<sqsubseteq> channel_control_dataAbbr sb"
proof(-)
  have h1: "emap (inv CtrlEnumEVENTConstr)\<cdot>(emap CtrlEnumEVENTConstr\<cdot>(channel_control_dataAbbr sb)) = (channel_control_dataAbbr sb)"
      by(simp add: emaps2emap)

  obtain x1 x2 where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x1,x2)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "(sb \<^enum> channel_control_data) = (smap (Timed o TLive )\<cdot>(emap CtrlEnumEVENTConstr\<cdot>(channel_control_dataAbbr sb)))"
    apply(simp add: ab_def)
    apply(induction x1;simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_control_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> emap CtrlEnumEVENTConstr\<cdot>(channel_control_dataAbbr sb)"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma channel_control_data_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(channel_control_data_efilter\<cdot>i) \<subseteq> eValues\<cdot>(channel_control_dataAbbr sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms channel_control_data_prefix_eq by simp

lemma channel_control_data_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(channel_control_dataAbbr sb)) = channel_control_data_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain x1 x2 where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x1,x2)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "channel_control_dataAbbr sb = emap (inv CtrlEnumEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> channel_control_data))"
    apply(simp add: ab_def)
    apply(induction x1;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: channel_control_data_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed

lemma channel_input_data_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "channel_input_data_efilter\<cdot>i \<sqsubseteq> channel_input_dataAbbr sb"
proof(-)
  have h1: "emap (inv PacketEVENTConstr)\<cdot>(emap PacketEVENTConstr\<cdot>(channel_input_dataAbbr sb)) = (channel_input_dataAbbr sb)"
      by(simp add: emaps2emap)

  obtain x1 x2 where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x1,x2)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "(sb \<^enum> channel_input_data) = (smap (Timed o TLive )\<cdot>(emap PacketEVENTConstr\<cdot>(channel_input_dataAbbr sb)))"
    apply(simp add: ab_def)
    apply(induction x2;simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = channel_input_data)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> emap PacketEVENTConstr\<cdot>(channel_input_dataAbbr sb)"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma channel_input_data_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(channel_input_data_efilter\<cdot>i) \<subseteq> eValues\<cdot>(channel_input_dataAbbr sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms channel_input_data_prefix_eq by simp

lemma channel_input_data_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(channel_input_dataAbbr sb)) = channel_input_data_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain x1 x2 where ab_def: "sb = def_Buffer_HLR3_Input.sbsetter\<cdot>(x1,x2)"
    by(metis def_Buffer_HLR3_Input.SB.set_get prod.exhaust_sel)
  have "channel_input_dataAbbr sb = emap (inv PacketEVENTConstr)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> channel_input_data))"
    apply(simp add: ab_def)
    apply(induction x2;simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: channel_input_data_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed


(* ticksb output lemmas *)

lemma sbsetter_ticksb:"def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>Tick) = ticksb"
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
  (\<up>Tick) \<Zcat>\<Zcat> def_Buffer_HLR3_Output.sbgetter\<cdot>s"
  by(simp add: sbgetter_ticksb conc_sb_def getter_conc2sbconc[symmetric])


(* usplit out lemmas *)

lemma usplit_event_sbsetter_channel_output_data_list:
  "uSplit\<cdot>(smap EventMsg\<cdot>(smap channel_Buffer_HLR3_output_dataConstr\<cdot>(<ls>))) =
    def_Buffer_HLR3_Output.sbsetter\<cdot>(smap EventMsg\<cdot>(<ls>))"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= channel_output_data and m="PacketEVENTConstr a"])
  apply(simp_all add: channel_Buffer_HLR3_output_dataConstr.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_channel_output_data:
  "uSplit\<cdot>(\<up>(EventMsg (channel_Buffer_HLR3_output_dataConstr a)) \<Zcat> s) =
    def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg a)) \<Zcat>\<Zcat> (uSplit\<cdot>s)"
  using usplit_event_sbsetter_channel_output_data_list[where ls="[a]"] apply simp
  by(simp add: usplit_conc)?

lemma somethingexists[simp]:
  "(\<exists>m1::CtrlEnum. Rep_msgWithChan aa = (channel_control_data, CtrlEnumEVENTConstr m1)) \<or>
   (\<exists>m2::Packet. Rep_msgWithChan aa = (channel_input_data, PacketEVENTConstr m2))"
  apply(auto)?
  apply(cases aa;case_tac y;case_tac a;case_tac b;simp add: well_def)?
  using not_channel_control_data_Packet not_channel_input_data_CtrlEnum not_channel_output_data_CtrlEnum
  apply(metis (full_types) msg.exhaust def_Buffer_HLR3_Input.channels.exhaust surj_pair)?
  apply(blast+)?
  by((subst Abs_msgWithChan_inverse, simp_all add: well_def, subst(asm) Abs_msgWithChan_inverse, simp_all add: well_def)+)?


(* automaton transition lemmas *)

lemma init0_nda:"autInitConfig\<cdot>(behavior.eaut ()) = {(StateConstr Substate.state__S ([]) ([]), bottom)}"
  apply(simp add:behavior.config_def)
  by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)

lemma init0_da:
  assumes "da \<in> (behavior.daset ())"
  shows "\<exists>foo. (dautInitConfig da) = ((StateConstr Substate.state__S ([]) ([]), foo), bottom)"
proof(-)
  have "apfst fst (dautInitConfig da) = (StateConstr Substate.state__S ([]) ([]), bottom)"
    using init0_nda nda2da_init eventGen.daset_def assms by fastforce
  then show ?thesis
    by(metis eq_fst_iff snd_conv tuple_to_apfst)
qed

lemma transitionE00_nda:
  assumes "Rep_msgWithChan m = (channel_input_data, PacketEVENTConstr channel_input_data_pattern)"
  and "((length var_old_packets) = 0)"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg channel_input_data_pattern)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms usplit_event_sbsetter_channel_output_data apply(simp)
  apply(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)?
    (* autosledgi *) sorry

lemma transitionE00_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_input_data, PacketEVENTConstr channel_input_data_pattern)"
  and "((length var_old_packets) = 0)"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg channel_input_data_pattern)))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<up>(EventMsg channel_input_data_pattern)))"
    using transitionE00_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma transitionE01_nda:
  assumes "Rep_msgWithChan m = (channel_input_data, PacketEVENTConstr channel_input_data_pattern)"
  and "((length var_old_packets) > 0)"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp)

lemma transitionE01_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_input_data, PacketEVENTConstr channel_input_data_pattern)"
  and "((length var_old_packets) > 0)"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S (var_old_packets) ((append var_new_packets [channel_input_data_pattern])), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
    using transitionE01_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma transitionE10_nda:
  assumes "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) > 1))"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp)

lemma transitionE10_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) > 1))"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
    using transitionE10_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma transitionE11_nda:
  assumes "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) = 1))"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<var_new_packets>))))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms usplit_event_sbsetter_channel_output_data_list apply(simp)
  apply(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)?
    (* autosledgi *) sorry

lemma transitionE11_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.ACK) \<and> ((length var_old_packets) = 1))"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<var_new_packets>))))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S ((tl var_old_packets)) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<var_new_packets>))))"
    using transitionE11_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma transitionE12_nda:
  assumes "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.NAK) \<and> ((length var_old_packets) > 0))"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S ([]) ((append var_old_packets var_new_packets)), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<(append var_old_packets var_new_packets)>))))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms usplit_event_sbsetter_channel_output_data_list apply(simp)
  apply(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)?
    (* autosledgi *) sorry

lemma transitionE12_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((channel_control_data_pattern = CtrlEnum.NAK) \<and> ((length var_old_packets) > 0))"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S ([]) ((append var_old_packets var_new_packets)), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<(append var_old_packets var_new_packets)>))))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S ([]) ((append var_old_packets var_new_packets)), def_Buffer_HLR3_Output.sbsetter\<cdot>((smap EventMsg\<cdot>(<(append var_old_packets var_new_packets)>))))"
    using transitionE12_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma transitionE13_nda:
  assumes "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((length var_old_packets) = 0)"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) (EventMsg m)) =
         {(StateConstr Substate.state__S (var_old_packets) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms by(simp)

lemma transitionE13_da:
  assumes "da \<in> (behavior.daset ())"
  and "Rep_msgWithChan m = (channel_control_data, CtrlEnumEVENTConstr channel_control_data_pattern)"
  and "((length var_old_packets) = 0)"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m) =
         ((StateConstr Substate.state__S (var_old_packets) (var_new_packets), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) (EventMsg m)) =
          (StateConstr Substate.state__S (var_old_packets) (var_new_packets), def_Buffer_HLR3_Output.sbsetter\<cdot>(\<epsilon>))"
    using transitionE13_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

lemma tick0_nda:
  assumes "True"
  shows "((autTransition\<cdot>(behavior.eaut ())) ((StateConstr Substate.state__S var_old_packets var_new_packets)) Tick) =
         {(StateConstr Substate.state__S (var_new_packets) ([]), def_Buffer_HLR3_Output.sbsetter\<cdot>((\<up>(Tick)) \<Zcat>\<Zcat> (\<epsilon>)))}"
  apply(simp add: behavior.transition_def)
  apply(simp add: assms EventLocale.outconv_def behavior.ndaTransition_tickC_def)
  using assms sbsetter_ticksb by(simp)

lemma tick0_da:
  assumes "da \<in> (behavior.daset ())"
  assumes "True"
  shows "\<exists>bar. dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) Tick =
         ((StateConstr Substate.state__S (var_new_packets) ([]), bar), def_Buffer_HLR3_Output.sbsetter\<cdot>((\<up>(Tick)) \<Zcat>\<Zcat> (\<epsilon>)))"
proof(-)
  have "apfst fst (dautTransition da ((StateConstr Substate.state__S var_old_packets var_new_packets), foo) Tick) =
         ((StateConstr Substate.state__S (var_new_packets) ([])), def_Buffer_HLR3_Output.sbsetter\<cdot>((\<up>(Tick)) \<Zcat>\<Zcat> (\<epsilon>)))"
  using tick0_nda nda2da_trans eventGen.daset_def assms by fastforce
then show ?thesis
  by (metis Pair_inject prod.collapse tuple_to_apfst)
qed


lemma getch_to_getter_1:
  "(out \<^enum> channel_output_data)
 = (Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr))) ((def_Buffer_HLR3_Output.sbgetter\<cdot>(out)))"
  proof -
    obtain s1 
      where s_def: "(s1) = def_Buffer_HLR3_Output.sbgetter\<cdot>(out)"
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
    fix c assume c_def: "c = channel_output_data"
    have "Pair channel_output_data ` sValues\<cdot>
            ((Rep_cfun (smap (Timed o TLive o map_event PacketEVENTConstr)))
              ((def_Buffer_HLR3_Output.sbgetter\<cdot>(out))))
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
    shows "Tick \<notin> sValues\<cdot>((def_Buffer_HLR3_Output.sbgetter\<cdot>out))"
  apply auto
  proof -
    assume tick: "Tick \<in> sValues\<cdot>((def_Buffer_HLR3_Output.sbgetter\<cdot>out))"
    hence "(Timed (TLive (Tick))) \<in> sValues\<cdot>(out \<^enum> channel_output_data)"
      apply(subst getch_to_getter_1)
      by(simp add: smap_sValues)
    hence "(Timed (TLive (Tick))) \<in> (snd ` sbValues\<cdot>(out))"
      using svalues_getch_subset_sbvalues by blast
    with assms show False
      by (metis tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlent)
  qed

lemma getter_preserves_len_finite:
  assumes "\<And>c. #(out \<^enum> c) < \<infinity>"
    shows "#((def_Buffer_HLR3_Output.sbgetter\<cdot>out)) < \<infinity>"
  apply(rule conjI)?
  by(metis assms getch_to_getter_1 slen_smap)

lemma no_tick_from_eventgen:
  assumes "da \<in> (behavior.daset ())"
    shows "Tick \<notin> sValues\<cdot>((def_Buffer_HLR3_Output.sbgetter\<cdot>(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))))"
  apply(rule conjI)?
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param="()"])
  apply(simp_all add:assms)
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
  apply(simp_all add:assms)?
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list (eshdts\<cdot>i))" and param="()"])?
  by(simp_all add:assms)?

lemma not_inf_from_eventgen:
  assumes "da \<in> (behavior.daset ())"
    shows "#((def_Buffer_HLR3_Output.sbgetter\<cdot>(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i))))))) < \<infinity>"
  apply(rule conjI)?
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param="()"])
  using assms apply blast apply simp+
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne da (StateConstr state old_packets new_packets, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
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
  assumes "spf \<in> def_Buffer_LLR.Sps ()"
      and "wellformed (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"
    shows "assumption_0 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<and>
           assumption_1 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<longrightarrow>
           predicate_0 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: def_Buffer_LLR.Sps_def behavior.Sem_def)
  apply(rule bundlemergepred[where SPS="eSem (behavior.eaut ())"])
  apply(simp)
  apply(simp add: assumption_0_def assumption_1_def predicate_0_def)
  apply(simp add: case_prod_beta)?
  (* autosledgi *) sorry

lemma predicate_1_llr:
  assumes "spf \<in> def_Buffer_LLR.Sps ()"
      and "wellformed (def_Buffer_HLR3_Input.sbgetter\<cdot>sb)"
    shows "assumption_0 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<and>
           assumption_1 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb)) \<longrightarrow>
           predicate_1 () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: def_Buffer_LLR.Sps_def behavior.Sem_def)
  apply(rule bundlemergepred[where SPS="eSem (behavior.eaut ())"])
  apply(simp)
  apply(simp add: assumption_0_def assumption_1_def predicate_1_def)
  apply(simp add: case_prod_beta)?
  (* autosledgi *) sorry

lemma causality_llr:
  assumes "spf \<in> def_Buffer_LLR.Sps ()"
    shows "causality (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  apply(simp add: causality_def weakpred_def)
  using assms by(metis case_unit def_Buffer_LLR.Sps_def eventGen.sem_weak weak_def)

lemma wholePredicate_llr:
  assumes "spf \<in> def_Buffer_LLR.Sps ()"
    shows "wholePredicate () (def_Buffer_HLR3_Input.sbgetter\<cdot>sb) (def_Buffer_HLR3_Output.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: wholePredicate_def)
  by(simp add: predicate_0_llr predicate_1_llr causality_llr)

(* General refinement skeleton *)
lemma refinement[simp]: "def_Buffer_LLR.Sps () \<subseteq> def_Buffer_HLR3.Sps ()"
  by(simp add: def_Buffer_HLR3.Sps_def subsetI wholePredicate_llr)


end
