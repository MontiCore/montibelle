theory EventStream

imports StreamAutomaton StreamFilter TimedStreamFunction inc.EventDatatype inc.Causality

begin
default_sort countable

lemma eventset_cont[cont2cont]: "cont (\<lambda>A. EventMsg ` A \<union> {Tick})"
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: less_set_def)
  apply (meson Union_mono image_mono subset_insertI2)
  apply (simp add: less_set_def lub_eq_Union)
  by blast


lemma eind: 
  assumes "adm P" 
    and "P \<epsilon>" 
    and "\<And>msg s. P s  \<Longrightarrow> P (\<up>(EventMsg msg) \<Zcat> s)" 
    and "\<And>s. P s  \<Longrightarrow> P (\<up>(Tick) \<Zcat> s)"
  shows "P x"
  apply(induction x)
    apply(simp add: assms)+
  apply(rename_tac msg rst, case_tac msg)
  by(simp add: assms)+



lemma sfilter_len_tlen:
  "#(sfilter {Tick}\<cdot>s) = #\<^sub>\<surd>s"
  apply (induction s)
  apply (rule adm_eq)
  using cont_Rep_cfun2 cont_compose len_stream_cont apply blast
  apply simp+
  apply (case_tac a; simp)
  using lnat_suc_plus by fastforce

lemma ticknotinsvalues[simp]:"Tick \<notin> sValues\<cdot>(smap EventMsg\<cdot>(s))"
  apply(induction s,simp_all)
  by (simp add: smap_sValues)

lemma stlen_appendtick:
  assumes "#s<\<infinity>"
  shows "#\<^sub>\<surd> (s \<Zcat> \<up>Tick) = lnsuc\<cdot>(#\<^sub>\<surd>s)"
  using assms
  apply(induction s;simp)
  apply (simp add: one_def; fail)
  apply(case_tac a;simp)
  by (simp add: lnat_suc_plus lnless_def)+

definition emap::"('a \<Rightarrow> 'b) \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"emap f = smap (map_event f)"


lemma emaptick[simp]:"emap f\<cdot>(\<up>Tick \<Zcat> s) = \<up>Tick \<Zcat> emap f\<cdot>s"
     and emapevent[simp]:"emap f\<cdot>(\<up>(EventMsg e) \<Zcat> s) = \<up>(EventMsg (f e)) \<Zcat> emap f\<cdot>s"
     and emapbot[simp]:"emap f\<cdot>\<epsilon> = \<epsilon>"
     and emaptick2[simp]:"emap f\<cdot>(\<up>Tick) = \<up>Tick"
     and emapevent2[simp]:"emap f\<cdot>(\<up>(EventMsg e)) = \<up>(EventMsg (f e))"
  by(simp add: emap_def)+

lemma emap_tlen[simp]: "#\<^sub>\<surd>(emap f\<cdot>s) = #\<^sub>\<surd>s"
  apply (induction s, simp_all)
  apply (simp add: tlen_stream_def; fail)
  by (case_tac a; simp)

lemma emaps2emap: "emap f\<cdot>(emap g\<cdot>s) = emap (f o g)\<cdot>s"
  by(simp add: emap_def smaps2smap event.map_comp)

lemma emap_id [simp]:"emap id\<cdot>x = x"
  by (simp add: emap_def event.map_id0)

lemma emap_split: "emap f\<cdot>(s1 \<Zcat> s2) = (emap f\<cdot>s1) \<Zcat> (emap f\<cdot>s2)"
  by (simp add: emap_def smap_split)

lemma emap_smap_event:
  "emap f\<cdot>(smap EventMsg\<cdot>s) = smap EventMsg\<cdot>(smap f\<cdot>s)"
  by (induction s, simp_all)

lemma emap_len[simp]:"#(emap f\<cdot>s) = #s"
  by(simp add: emap_def)

lemma smapevent_tlen[simp]:"#\<^sub>\<surd> (smap EventMsg\<cdot>s) = 0"
  apply(induction s,simp_all)
  by(rule adm_eq,simp_all add: tlen_stream_def)

lemma smapevent_tlenrt[simp]:assumes "#s<\<infinity>"
  shows"#\<^sub>\<surd> (smap EventMsg\<cdot>s \<Zcat> t) = #\<^sub>\<surd>t"
  using assms by (simp)

lemma emap_inj_below: "inj f \<Longrightarrow> emap f\<cdot>x \<sqsubseteq> emap f\<cdot>y \<Longrightarrow> x\<sqsubseteq> y"
  apply(simp add: emap_def)
  using event.inj_map smapnotbelowinj by auto


definition e2ustream::"'a event stream \<rightarrow> 'a stream"where
"e2ustream = smap (inv EventMsg) oo sfilter (UNIV -{Tick})"

lemma e2ustream_tick[simp]:"e2ustream\<cdot>(\<up>Tick \<Zcat> s) = e2ustream\<cdot>s"
  and e2ustream_event[simp]:"e2ustream\<cdot>(\<up>(EventMsg e) \<Zcat> s) = \<up>e \<Zcat> e2ustream\<cdot>s"
  and e2ustream_eps[simp]:"e2ustream\<cdot>\<epsilon> = \<epsilon>"
  and e2ustream_tickend[simp]:"e2ustream\<cdot>(\<up>Tick) = \<epsilon>"
  and e2ustream_eventend[simp]:"e2ustream\<cdot>(\<up>(EventMsg e)) = \<up>e"
  by(simp_all add: e2ustream_def)

lemma e2ustream_map: "smap f\<cdot>(e2ustream\<cdot>s) = e2ustream\<cdot>(emap f\<cdot>s)"
  apply(induction s, simp+)
  by(case_tac "a"; simp)

definition eValues::"'a event stream \<rightarrow> 'a set" where
"eValues = sValues oo e2ustream"

lemma evalues_tick [simp]:"eValues\<cdot>(\<up>Tick \<Zcat> s) = eValues\<cdot>s"
     and evalues_event [simp]:"eValues\<cdot>(\<up>(EventMsg e) \<Zcat> s) = insert e (eValues\<cdot>s)"
     and evalues_eps [simp]:"eValues\<cdot>\<epsilon> = {}"
     and evalues_tickend[simp]:"eValues\<cdot>(\<up>Tick) = {}"
     and evalues_eventend[simp]:"eValues\<cdot>(\<up>(EventMsg e)) = {e}"
  by(simp_all add: eValues_def)

lemma evalues_snth:"Fin n < #s \<Longrightarrow> snth n s = EventMsg a \<Longrightarrow> a \<in> eValues\<cdot>s"
  apply(induction n arbitrary: s)
  apply(case_tac s;simp)
  apply(case_tac s;simp)
  by(case_tac aa;simp)

lemma svalues_evalues [simp]: "sValues\<cdot>s \<subseteq> (EventMsg ` eValues\<cdot>s) \<union> {Tick}"
  apply(auto simp add: eValues_def)[1]
  apply(induction s; simp)
  apply(intro adm_all adm_imp; simp add: adm_in_img2)
   apply(intro adm_cmp adm_in_img2)
  apply(rename_tac msg s out)
  apply(case_tac msg)
  by auto

lemma eValues_smap_event[simp]: "eValues\<cdot>(smap EventMsg\<cdot>s) = sValues\<cdot>s"
  by(induction s; simp)


lemma
  eValues_sValues_without_tick:
  assumes "sValues\<cdot>s = (EventMsg ` A) \<union> {Tick}"
  shows "eValues\<cdot>s = A"
  apply(simp add: eValues_def e2ustream_def smap_sValues assms)
proof -
  have "inv EventMsg ` (EventMsg ` A \<inter> (UNIV - {\<surd>})) = inv EventMsg ` EventMsg ` A"
    by blast
  also have "inv EventMsg ` EventMsg ` A = A"
    by simp
  finally show "inv EventMsg ` (EventMsg ` A \<inter> (UNIV - {\<surd>})) = A"
    by blast
qed

lemma
  eValues_sValues_without_tick_subset:
  assumes "sValues\<cdot>s \<subseteq> (EventMsg ` A) \<union> {Tick}"
  shows "eValues\<cdot>s \<subseteq> A"
proof (cases "Tick \<in> sValues\<cdot>s")
  case True
  then obtain S where ob: "sValues\<cdot>s = (EventMsg ` S) \<union> {Tick}"
    by (metis (no_types, lifting)
        Tick_notin_image_Event
        assms
        subset_UnE
        subset_image_iff
        subset_singleton_iff
        sup_bot_right
    )
  then have "eValues\<cdot>s = S"
    by (simp add: eValues_sValues_without_tick)
  also have "S \<subseteq> A"
    using ob assms by auto
  finally show ?thesis
    by simp

next
  case False
  then obtain S where ob: "sValues\<cdot>s = (EventMsg ` S)"
    by (metis
        Un_insert_right
        assms
        subset_image_iff
        subset_insert
        sup_bot_right
    )
  then have "eValues\<cdot>s = S"
    by (metis
        eValues_smap_event
        equalityD2
        smap_obtainin
        smap_sValues
        these_image_EventMsg_eq
    )  
  also have "S \<subseteq> A"
    using ob assms by auto
  finally show ?thesis
    by simp
qed

lemma
  sValues_eValues_with_tick:
  assumes "eValues\<cdot>s = A"
  shows "sValues\<cdot>s \<subseteq> (EventMsg ` A) \<union> {Tick}"
proof -
  have "(inv EventMsg) ` sValues\<cdot>((sfilter (UNIV -{Tick}))\<cdot>s) = A"
    by (metis assms cfcomp2 e2ustream_def eValues_def smap_sValues)
  then have "EventMsg ` (inv EventMsg) ` sValues\<cdot>((sfilter (UNIV -{Tick}))\<cdot>s) = EventMsg ` A"
    by fastforce
  then have "sValues\<cdot>((sfilter (UNIV -{Tick}))\<cdot>s) = EventMsg ` A"
    by (simp add: UNIV_event_conv image_inv_into_cancel)
  then show ?thesis
    by (metis assms svalues_evalues)
qed

lemma
  sValues_eValues_with_tick_subset:
  assumes "eValues\<cdot>s \<subseteq> A"
  shows "sValues\<cdot>s \<subseteq> (EventMsg ` A) \<union> {Tick}"
  using assms subset_Un_eq svalues_evalues by fastforce

lemma eValues_sconc2un:
  "#x = Fin k \<Longrightarrow> eValues\<cdot>(x \<Zcat> y) = eValues\<cdot>x \<union> eValues\<cdot>y"
  apply(simp add: atomize_imp)
  apply(rule_tac x="x" in spec)
  apply(induct_tac k, simp+)
  apply(rule allI, rule impI)
  apply(rule_tac x="x" in scases, simp+)
  by(case_tac a;simp)

lemma sconc_eValues: "eValues\<cdot>(x \<Zcat> y) \<subseteq> eValues\<cdot>x \<union> eValues\<cdot>y"
  by(metis SetPcpo.less_set_def below_refl lncases sconc_fst_inf eValues_sconc2un sup.coboundedI1)

lemma emap_inv_id[simp]: "eValues\<cdot>s \<subseteq> range F \<Longrightarrow> emap (F \<circ> (inv F))\<cdot>s = s"
  apply(induction s)
  apply(simp_all)
  apply(case_tac a)
  by(simp_all add: f_inv_into_f)

definition efilter::"('a \<Rightarrow> bool) \<Rightarrow>  'a event stream \<rightarrow> 'a event stream" where
"efilter P = sfilter (insert Tick {EventMsg a | a. P a})"


lemma efilter_tick[simp]:"efilter P\<cdot>(\<up>Tick \<Zcat> s) = \<up>Tick \<Zcat> efilter P\<cdot>s"
     and efilter_tickf[simp]:"efilter P\<cdot>(\<up>Tick) = \<up>Tick"
     and efilter_P [simp]:"P e \<Longrightarrow> efilter P\<cdot>(\<up>(EventMsg e) \<Zcat> s) = \<up>(EventMsg e) \<Zcat> efilter P\<cdot>s"
     and efilter_not_P [simp]:"\<not> P e \<Longrightarrow> efilter P\<cdot>(\<up>(EventMsg e) \<Zcat> s) = efilter P\<cdot>s"
     and efilter_eps[simp]:"efilter P\<cdot>\<epsilon> = \<epsilon>"
     and efilter_P2 [simp]:"P e \<Longrightarrow> efilter P\<cdot>(\<up>(EventMsg e)) = \<up>(EventMsg e)"
     and efilter_not_P2 [simp]:"\<not> P e \<Longrightarrow> efilter P\<cdot>(\<up>(EventMsg e)) = \<epsilon>"
  by(simp add: efilter_def)+

lemma efilter_tlen[simp]:
  "#\<^sub>\<surd>(efilter P\<cdot>s) = #\<^sub>\<surd>s"
  apply (induction s)
  apply (rule adm_eq)
  apply (simp add: tlen_stream_def;fail)
  apply simp+
  apply (case_tac a; simp)
  by (case_tac "P aa"; simp)

lemma e2ustream_filter:  "e2ustream\<cdot>(efilter P\<cdot>s) = sfilter {a | a. P a}\<cdot>(e2ustream\<cdot>s)"
  apply(induction s; simp)
  apply(rename_tac msg stream, case_tac msg; simp)
  by(rename_tac event, case_tac "P event"; simp)

lemma efilter_len_leq[simp]: "#(efilter f\<cdot>s) \<le> #s"
  by(simp add: efilter_def)

lemma efilter_id[simp]: "efilter (\<lambda>_. True) = ID"
  apply(simp add: efilter_def) 
  apply(rule cfun_eqI, rename_tac s, induct_tac s; simp)
  by (simp add: insert_Collect)


definition eshdts::"'a event stream \<rightarrow> 'a stream"where
"eshdts = e2ustream oo tshd"

lemma eshdts_def2: "eshdts = smap (inv EventMsg) oo stakewhile (\<lambda>e. e\<noteq> Tick)"
  apply(rule cfun_eqI, rename_tac s)
  apply(induct_tac s rule:eind; simp add: eshdts_def tshd_def)
  by (metis (full_types) e2ustream_tickend not_Event_eq stwbl_f tlen_event.simps(2) tlen_notzero)

lemma eshdts_event:
      "eshdts\<cdot> (\<up>(EventMsg a) \<Zcat> s) = \<up>a \<Zcat> eshdts\<cdot>s"
  and  eshdts_tick [simp]:"eshdts\<cdot>(\<up>Tick \<Zcat> s) = \<epsilon>"
  and eshdts_eps [simp]:"eshdts\<cdot>\<epsilon> = \<epsilon>"
  and eshdts_id [simp]:"Tick \<notin>sValues\<cdot>s \<Longrightarrow> eshdts\<cdot>s = smap (inv EventMsg)\<cdot>s"
  apply(simp_all add: eshdts_def2)
  apply(induction s)
  apply(rule adm_imp,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg lub_eq_Union; fail)
  by(case_tac a;simp)

lemma eshdts_len[simp]:assumes"Tick\<in>sValues\<cdot>s"
  shows "#(eshdts\<cdot>s) < \<infinity>"
  apply(simp add: eshdts_def2)
  apply (subgoal_tac "\<exists>n. snth n s = Tick")
  using stakewhile_slen le_less apply fastforce
  using assms apply(auto simp add: sValues_def2)[1]
  by metis

lemma eshdts_len_leq: "#(eshdts\<cdot>s) \<le> #s"
  apply (induction s)
  apply (subst lnle_def)
  apply (rule adm_below)
  apply (rule cont_compose [where f="\<lambda>x. eshdts\<cdot>x"])
  apply (rule cont2cont, simp_all)
  by (case_tac a; simp add: eshdts_event)

lemma eshdts_lub:assumes"Tick\<in>sValues\<cdot>s"
  and "s \<sqsubseteq> s2"
shows "eshdts\<cdot>s2 = eshdts\<cdot>s"
  using assms
  apply(induction s arbitrary: s2,simp,simp)
  apply(case_tac s2;simp)
  apply(subgoal_tac "a=aa",simp)
  apply(case_tac aa;simp)
  apply (metis less_fst_sconsD eshdts_event)
  by (metis less_all_sconsD)


lemma eshdts_evalues[simp]:"sValues\<cdot>(eshdts\<cdot>s) \<subseteq> eValues\<cdot>s"
  apply(induction s,simp_all)
  by(case_tac a;auto simp add: eshdts_event)

lemma eshdts_svalues:
  "sValues\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>s)) \<subseteq> sValues\<cdot>s"
  apply (induction s, simp_all)
  apply (case_tac a; simp)
  apply (simp add: eshdts_event)
  by blast

lemma eshdts_split_eq:
  assumes "#s1 < \<infinity>"
    and "Tick \<notin> sValues\<cdot>s1"
  shows "eshdts\<cdot>(s1 \<Zcat> \<up>Tick \<Zcat> s2) = smap (inv EventMsg)\<cdot>s1"
proof-
  obtain n where n_def: "#s1 = Fin n"
    using assms lnat_well_h2 by blast
  show ?thesis
    using assms(2)
    apply (induction s1 arbitrary: s2 rule: finind [where n="n"])
    apply (simp add: n_def; fail)
    apply (simp; fail)
    by (case_tac a; simp add: eshdts_event)
qed

lemma eshdts_conc_eq:
  assumes "Tick \<notin> sValues\<cdot>s1"
  shows "eshdts\<cdot>(s1 \<Zcat> s2) = (smap (inv EventMsg)\<cdot>s1) \<Zcat> eshdts\<cdot>s2"
  using assms
proof(induction s2 arbitrary: s1)
  case adm
  then show ?case
    apply(rule adm_all)
    apply(rule adm_imp)
    apply(rule adm_upward)
    apply(simp)
    apply(rule adm_eq)
    by (intro cont2cont)+
next
  case bottom
  then show ?case by simp
next
  case (step a s2)
  then show ?case
  proof(cases "#s1 = \<infinity>")
    case True
    then show ?thesis
      by(simp add: step.prems)
  next
    case False
    then show ?thesis
    proof(cases a)
      case Tick
      then show ?thesis
        apply(simp)
        apply(subst eshdts_split_eq)
        using False inf_great linorder_less_linear apply(blast)
        by(simp_all add: step.prems)
    next
      case (EventMsg aa)
      have "Tick \<notin> sValues\<cdot>(s1 \<Zcat> \<up>(EventMsg aa))"
        using step.prems sconc_sValues by fastforce
      then show ?thesis
        apply(simp add: EventMsg eshdts_event)
        using step.IH[where ?s1.0="s1 \<Zcat> \<up>(EventMsg aa)"]
        by(simp add: step.prems smap_split)
    qed
  qed
qed

lemma eshdts_sdrop:
  assumes "Tick \<notin> sValues\<cdot>(stake n\<cdot>s)"
  shows "sdrop n\<cdot>(eshdts\<cdot>s) = eshdts\<cdot>(sdrop n\<cdot>s)"
  using assms
  apply (induction s arbitrary: n)
  apply (rule adm_all)
  apply (rule adm_imp)
  apply simp
  apply (rule adm_upward)
  apply (meson cont_pref_eq1I sValues_prefix subsetD)
  apply (rule adm_eq)
  apply (intro cont2cont)+
  apply (simp; fail)
  apply (case_tac n)
  apply (simp; fail)
  apply simp
  by (case_tac a; simp add: eshdts_event)

lemma aux_preds_eq: "(\<lambda>e::'msg::countable event. \<exists>y::'msg. e = EventMsg y) = (\<lambda>e::'msg event. #\<^sub>\<surd>e = 0)"
  by (metis bot_is_0 event.distinct(1) lnat.con_rews one_def tlen_event.elims)

lemma tsrt_def_3: "tsrt = srtdw (\<lambda>e::'msg::countable event. e \<noteq> Tick)"
  by (simp add: aux_preds_eq srtdw_def tsrt_def oo_def)

lemma tsrt_event [simp]:"tsrt\<cdot> (\<up>(EventMsg a) \<Zcat> s) = tsrt\<cdot>s"
  and tsrt_etick[simp]:"tsrt\<cdot>(\<up>Tick \<Zcat> s) = s"
  and tsrt_etick_notin[simp]:"Tick \<notin>sValues\<cdot>s \<Longrightarrow> tsrt\<cdot>s = \<epsilon>"
  apply (meson tsrt_msg tlen_event.simps(2))
  apply (simp add: one_def; fail)
  apply (subgoal_tac "\<forall>e \<in> sValues\<cdot>s. #\<^sub>\<surd>e = 0", simp)
  by (metis tlen_event.elims)

lemma tlen_tsrt_e[simp]: "#\<^sub>\<surd>(tsrt\<cdot>xs) = lnpred\<cdot>(#\<^sub>\<surd>(xs:: 'm::countable event stream))"
  by(rule tlen_tsrt[OF tlen_event_le_one])

lemma tsrt_evalues[simp]:"eValues\<cdot>(tsrt\<cdot>s) \<subseteq> eValues\<cdot>s"
  apply(induction s,simp_all)
  by(case_tac a, auto)

lemma tsrt_split_eq:
  assumes "#s1 < \<infinity>"
    and "Tick \<notin> sValues\<cdot>s1"
  shows "tsrt\<cdot>(s1 \<Zcat> \<up>Tick \<Zcat> s2) = s2"
proof-
  obtain n where n_def: "#s1 = Fin n"
    using assms lnat_well_h2 by blast
  show ?thesis
    using assms(2)
    apply (induction s1 arbitrary: s2 rule: finind [where n="n"])
    apply (simp add: n_def; fail)
    apply simp
    by (case_tac a; simp)
qed


lemma tsrt_tlen[simp]: "Tick \<in> sValues\<cdot>s \<Longrightarrow> lnsuc\<cdot>(#\<^sub>\<surd> (tsrt\<cdot>s)) = #\<^sub>\<surd>s"
  apply (induction s, simp_all) 
  by (metis (no_types, opaque_lifting) ab_semigroup_add_class.add_ac(1) lnat.sel_rews(2) lnat_plus_lnsuc lnat_suc_plus tlen_event.simps(1))

lemma invevent_eq:assumes "Tick \<notin>sValues\<cdot>s"
  shows"smap EventMsg\<cdot>(smap (inv EventMsg)\<cdot>s) = s"
  using assms
  apply(induction s)
  apply(rule adm_imp,simp_all)
  apply (simp add: adm_in2; fail)
  by(case_tac a,simp_all)

lemma stake_step_last:"Fin m<#s \<Longrightarrow> stake (Suc m)\<cdot>s = stake m\<cdot>s \<Zcat> \<up>(snth m s)"
  apply(rule snths_eq)
  apply(subst slen_stake) 
  apply (simp add: less2lnleD; fail)
  apply(subst sconc_slen2,simp)
  apply(subst slen_stake) 
  apply (simp add: less2lnleD; fail)
  apply (simp; fail)
  by (metis drop_not_all slen_snth_prefix snth_def stake2shd stake_concat)

lemma sValues2snth_strong: "z \<in> sValues\<cdot>s \<Longrightarrow> \<exists>n. snth n s = z \<and> n<#s"
by (auto simp add: sValues_def2)

lemma esplit_tick:assumes "Fin m<#s"
  assumes "snth m s = Tick"
and "\<And>x. x<m \<Longrightarrow> snth x s \<noteq>Tick"
  shows"smap EventMsg\<cdot>(smap (inv EventMsg)\<cdot>(stake m\<cdot>s)) \<Zcat> \<up>Tick \<Zcat> (sdrop (Suc m)\<cdot>s) = s" 
proof-
  have "Tick \<notin> sValues\<cdot>(stake m\<cdot>s)"
    apply(auto simp add:sValues_def2)[1]
    using assms
    by (metis inject_Fin lnat_well_h1 lnle_def lnless_def slen_stake stake_snths)
  then show "smap EventMsg\<cdot>(smap (inv EventMsg)\<cdot>(stake m\<cdot>s)) \<Zcat> \<up>Tick \<Zcat> (sdrop (Suc m)\<cdot>s) = s"
    apply(subst invevent_eq)
    apply(simp add: sValues_def2 sValues2snth; fail)
    apply(subst(3) split_streaml1[where n="(Suc m)" and s=s,symmetric])
    by(subst stake_step_last,simp_all add: assms)
qed

(*
proof-
  obtain n_set where n_def:"n_set= {n. snth n s = Tick \<and> n<#s}"
    by simp
  then have nex:"n_set \<noteq> {}"
    using assms sValues_def2
    by (simp add: sValues2snth_strong)
  obtain m where m_def:"(m::nat) = (LEAST n. n\<in> n_set)"
    by simp
  have m_def2:"snth m s = Tick"and len:"Fin m<#s"
    using m_def n_def nex LeastI_ex
    by (metis (mono_tags, lifting) all_not_in_conv mem_Collect_eq)+
  then have "(\<forall>x<m. snth x s\<noteq> Tick)" 
    apply auto
    apply(subgoal_tac "x<#s")
    using m_def n_def nex not_less_Least
    apply fastforce
    by (meson dual_order.strict_trans leD leI less2nat_lemma)
*)
lemma stakewhile2stake:assumes"\<And>x. x<m \<Longrightarrow> P (snth x s)"
and "Fin m <#s"
and "\<not>P (snth m s)"
shows "stakewhile P\<cdot>s = stake m\<cdot>s"
  using assms
  apply(induction m arbitrary: s,simp_all)
  apply (metis Fin_02bot empty_is_shortest gr_0 lnat.exhaust lnzero_def snth_shd snths_eq stakewhile_snth)
  apply(case_tac sa,simp_all)
  apply(case_tac "P a",simp_all)
  apply (metis Suc_less_eq snth_scons)
  apply(subgoal_tac "snth 0 sa = a \<and> 0<ma")
  apply (metis less_SucI)
  by (metis shd1 snth_shd zero_less_Suc)

lemma sdropwhile2sdrop:
  assumes"\<And>x. x<m \<Longrightarrow> P (snth x s)"
  and "Fin m <#s"
  and "\<not>P (snth m s)"
  shows"sdropwhile P\<cdot>s = sdrop m\<cdot>s"
using assms
  apply(induction m arbitrary: s,simp_all)
  apply(case_tac sa,simp_all)
  apply(case_tac sa,simp_all)
  apply(case_tac "P a",simp_all)
  apply (metis Suc_less_eq snth_scons)
  apply(subgoal_tac "snth 0 sa = a \<and> 0<ma")
  apply (metis less_SucI)
  by (metis shd1 snth_shd zero_less_Suc)

lemma essplit_tickhdrt:assumes "Tick \<in> sValues\<cdot>s"
  shows"(smap EventMsg\<cdot>(eshdts\<cdot>s)) \<Zcat> \<up>Tick \<Zcat> (tsrt\<cdot>s) = s"
proof-
    obtain n_set where n_def:"n_set= {n. snth n s = Tick \<and> n<#s}"
    by simp
  then have nex:"n_set \<noteq> {}"
    using assms sValues_def2
    by (simp add: sValues2snth_strong)
  obtain m where m_def:"(m::nat) = (LEAST n. n\<in> n_set)"
    by simp
  have m_def2:"snth m s = Tick"and len:"Fin m<#s"
    using m_def n_def nex LeastI_ex
    by (metis (mono_tags, lifting) all_not_in_conv mem_Collect_eq)+
  then have "(\<forall>x<m. snth x s\<noteq> Tick)" 
    apply auto[1]
    apply(subgoal_tac "x<#s")
    using m_def n_def nex not_less_Least
    apply fastforce
    by (meson dual_order.strict_trans leD leI less2nat_lemma)
  have "eshdts\<cdot>s = smap (inv EventMsg)\<cdot>(stake m\<cdot>s)"
    apply(simp add: eshdts_def2)
    apply(subst stakewhile2stake[where m=m],simp_all add: m_def2 len)
    using \<open>\<forall>x<m. snth x s \<noteq> Tick\<close>
    by (meson tlen_event.elims)
  moreover have "tsrt\<cdot>s = sdrop (Suc m)\<cdot>s"
    apply(simp add: tsrt_def sdrop_back_rt srtdw_def)
    apply(subst sdropwhile2sdrop[where m=m],simp_all add: m_def2 len)
    using \<open>\<forall>x<m. snth x s \<noteq> Tick\<close>      
    apply (meson tlen_event.elims)
    by (simp add: one_lnat_def) 
  ultimately show ?thesis
    apply simp
    apply(rule esplit_tick)
    apply (simp_all add: len m_def2)
    using \<open>\<forall>x<m. snth x s \<noteq> Tick\<close> by blast
qed

lemma tsdrop_event[simp]:"tsdrop (Suc n)\<cdot>(\<up>(EventMsg a) \<Zcat> s) = tsdrop (Suc n)\<cdot>s"
  apply(induction n)
  by(simp add: tsdrop_def)+

lemma tsdrop_tick[simp]:"tsdrop (Suc n) \<cdot>(\<up>Tick \<Zcat> s) = tsdrop n\<cdot>s"
  apply(simp add: tsdrop_def)
  by(induction n;simp)


definition esnth::"nat \<Rightarrow> 'a event stream \<rightarrow> 'a stream"where
"esnth n = eshdts oo (tsdrop n)"

lemma esnth_nothing[simp]:"esnth 0\<cdot>s = eshdts\<cdot>s"
  by(simp add: esnth_def)

lemma esnth_empty[simp]:"esnth n\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: esnth_def)

lemma esnth_event[simp]:"esnth (Suc n)\<cdot>(\<up>(EventMsg a) \<Zcat> s) = esnth (Suc n)\<cdot>s"
  by(simp add: esnth_def)

lemma esnth_tsrt:"esnth (Suc n)\<cdot>s = esnth n\<cdot>(tsrt\<cdot>s)"
  apply(simp add: esnth_def)
  apply(induction s,simp_all)
  by(case_tac a;simp)

lemma esnth_tick[simp]:"esnth (Suc n)\<cdot>(\<up>Tick \<Zcat> s) = esnth n\<cdot>s"
  by(simp add: esnth_def)

lemma esnth_eps[simp]:"Tick \<notin> sValues\<cdot>s \<Longrightarrow> esnth (Suc n)\<cdot>s = \<epsilon>"
  apply(induction s,simp_all)
  apply(rule adm_imp,simp)
  apply(rule admI,simp add: contlub_cfun_arg lub_eq_Union)
  apply(rule adm_eq,simp,simp)
  by(case_tac a;simp)

lemma esnth_svalues[simp]: "sValues\<cdot>(esnth n\<cdot>s) \<subseteq> eValues\<cdot>(s)"
proof(induction n arbitrary: s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply(simp add: esnth_tsrt)
    apply(cases "Tick \<in> sValues\<cdot>(tsrt\<cdot>s)")
    using tsrt_evalues apply blast
    apply(cases n;simp)
    by (metis (no_types, lifting) dual_order.trans eshdts_id eshdts_evalues tsrt_evalues)
qed
 

lemma tlen_inftimes_inf: assumes "#\<^sub>\<surd>x \<noteq> 0 " 
    shows "#\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>) = \<infinity>"
proof (rule ccontr)
  assume "#\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>) \<noteq> \<infinity>" 
  obtain n where n_def: "#\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>) = Fin n" 
    using LNat.LNat.lnat.exhaust \<open>#\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>) \<noteq> \<infinity>\<close> by auto
  have "#\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>) = #\<^sub>\<surd>x + #\<^sub>\<surd> ((\<up>x)\<^sup>\<infinity>)"
    by(subst sinftimes_unfold,simp add: n_def )
  thus False 
    by (metis assms lnat_plus_ineq n_def plus_lnat0_r)
qed

lemma inftick_len [simp]: "#\<^sub>\<surd> ((\<up>Tick)\<^sup>\<infinity>) = \<infinity>"
  apply(rule tlen_inftimes_inf)
  by(simp add: one_lnat_def)

lemma tlentosvalues[simp]:"#\<^sub>\<surd> s = 0 \<longleftrightarrow> Tick \<notin> sValues\<cdot>s"
  apply(induction s)
  apply(rule adm_iff)
  apply(rule adm_imp)
  apply(rule adm_neq_compact)
  apply(rule compactI2,simp_all)
  apply(rule adm_imp,simp)
  apply(rule admI,simp add: contlub_cfun_arg lub_eq_Union)
  apply(rule adm_eq,simp_all)
  by (metis lnat_suc_plus lnsuc_neq_0_rev plus_lnat0_r tlen_event.elims tlen_event.simps(1))

lemma srteps[simp]: 
  assumes "#\<^sub>\<surd> s = 0"
  shows"tsrt\<cdot>(s \<Zcat>\<up>Tick) = \<epsilon>"
  apply (simp add: tsrt_def srtdw_def)
  apply (cases "#s=\<infinity>",simp)
  apply (subgoal_tac "sdropwhile (\<lambda>e::'a event. \<exists>y::'a. e = EventMsg y)\<cdot>s = \<epsilon>")
  apply (simp add: aux_preds_eq; fail)
  apply (rule sdropwhile_dropstream)
  using assms not_Tick_eq tlentosvalues apply fastforce
  apply (subgoal_tac "sdropwhile (\<lambda>e. #\<^sub>\<surd> e = 0)\<cdot>(s \<Zcat> \<up>Tick) = \<up>Tick")
  apply auto[1] 
  apply (subst sdropwhile_sconc, auto) 
  apply (subgoal_tac "\<forall>e \<in> sValues\<cdot>s. #\<^sub>\<surd> e = 0")
  apply (simp add: snth2sValues; fail) 
  apply (metis assms tlen_event.elims tlentosvalues)
  apply (simp add: order.strict_iff_order; fail)
  by (simp add: one_def)

lemma srtsplit[simp]: assumes "#\<^sub>\<surd> s = 0" and "#s<\<infinity>" shows"tsrt\<cdot>(s \<Zcat> \<up>Tick \<Zcat> rt) = rt"
  apply (simp add: tsrt_def_2 srtdw_def)
  apply (subst sdropwhile_dropfst,simp_all add: assms)
  apply (metis assms(1) tlen_event.elims tlentosvalues)
  by (metis (mono_tags) event.exhaust inject_scons sdropwhile_f stwbl_eps stwbl_f surj_scons tlen_event.simps(2) tlent)

lemma notitckstlen[simp]:"Tick \<notin> sValues\<cdot>s \<Longrightarrow> #\<^sub>\<surd> s = 0"
  by simp

lemma sdroptsfststream[simp]:assumes "Tick \<notin> sValues\<cdot>s"
and "#s<\<infinity>"
  shows"tsdrop (Suc n)\<cdot>(s \<Zcat> \<up>Tick \<Zcat> y) = tsdrop n\<cdot>(y)"
  using assms
  apply(subst tsdrop_def)
  apply(subst iterate_Suc2)
  apply(subst srtsplit,simp_all)
  apply(subst tsdrop_def[symmetric]) ..

lemma esnth_dropfst:assumes "Tick \<notin> sValues\<cdot>s1"
and "#s1<\<infinity>"
  shows"esnth (Suc n)\<cdot>(s1 \<Zcat> s2) = esnth (Suc n)\<cdot>s2"
  using assms 
proof(induction s2 arbitrary: s1)
  case adm
  then show ?case apply(rule adm_all,rule adm_imp,simp)
  by(rule admI,simp add: contlub_cfun_arg lub_eq_Union)
next
  case bottom
  then show ?case by simp
next
  case (step a s2)
  then show ?case
    apply(case_tac a,simp_all)
  proof(simp add: esnth_def)
    fix aa
    show"esnth (Suc n)\<cdot>(s1 \<Zcat> \<up>(EventMsg aa) \<Zcat> s2) = esnth (Suc n)\<cdot>s2"
      using step.IH[where ?s1.0="s1 \<Zcat> \<up>(EventMsg aa)"] apply auto[1]
      using step.prems
      using lnzero_def plus_lnat0_0 tlentosvalues by fastforce
  qed
qed


lemma tsrt_tlen2[simp]:assumes"#\<^sub>\<surd> (s:: 'msg event stream) = Fin ( Suc n)"
  shows "(#\<^sub>\<surd> (tsrt\<cdot>s)) = Fin n"
  using tsrt_tlen assms
  by (metis Fin_0 Fin_Suc Zero_neq_Suc lnat.injects tlentosvalues)

lemma tsrt_tlen_leq[simp]:assumes"m < #\<^sub>\<surd> (s:: 'msg event stream)"
  shows "m \<le> (#\<^sub>\<surd> (tsrt\<cdot>s))"
  apply(cases "Tick \<in> sValues\<cdot>s",simp_all add: assms)
  apply (metis assms lnle2le tlen_tsrt_e tsrt_tlen)
  using assms lnzero_def by force

lemma smap_esnth:"smap f\<cdot>(esnth n\<cdot>i) = esnth n\<cdot>(emap f\<cdot>i)"
  apply(induction i arbitrary: n,simp_all)
  apply(case_tac n;case_tac a;simp add: eshdts_event)
  by (metis esnth_nothing)

lemma smapevent_esnth[simp]:"esnth n\<cdot>(smap (map_event f)\<cdot>s) = smap f\<cdot>(esnth n\<cdot>s)"
  by(simp add: emap_def[symmetric] smap_esnth)

lemma filter_esnth:"sfilter S\<cdot>(esnth n\<cdot>i) = esnth n\<cdot>(efilter (\<lambda>m. m\<in> S)\<cdot>i)"
  apply(induction i arbitrary: n,simp_all)
  apply(case_tac n;case_tac a;simp add: eshdts_event)
  apply(case_tac "aa \<in> S",simp_all add: eshdts_event)
  apply (metis esnth_nothing) 
  apply (metis esnth_nothing)
  by(case_tac "aa \<in> S",simp_all add: eshdts_event)

lemma evalues_filter[simp]: "eValues\<cdot>(efilter f\<cdot>s) \<subseteq> {msg | msg. f msg}"
  apply(induction s;simp)
  apply(case_tac a; simp)
  by(rename_tac msg, case_tac "f msg"; simp)

lemma esnthprefixeq:assumes "x \<sqsubseteq> y"
and "Fin n < #\<^sub>\<surd>x"
shows"(esnth n\<cdot>x) = (esnth n\<cdot>y)"
  apply(simp add: esnth_def eshdts_def2 tsrt_def)
  using assms
proof(induction n arbitrary: x y)
  case 0
  then show ?case
    apply simp
    apply(cases "Tick \<in> sValues\<cdot>x",simp_all)
    apply(cases "Tick \<in> sValues\<cdot>y")
    apply(subst essplit_tickhdrt[of x, symmetric],simp)
    apply(subst essplit_tickhdrt[of y, symmetric],simp)
    apply(rule cfun_arg_cong)
    apply(rule stakewhile_finite_below)
    apply(simp add: aux_preds_eq)
    apply (metis (mono_tags, lifting) aux_preds_eq  essplit_tickhdrt event.simps(3) stakewhile_dom)
    apply (metis (mono_tags, lifting) essplit_tickhdrt)
    apply (simp add: essplit_tickhdrt aux_preds_eq)
    using sValues_prefix by blast
next
  case (Suc n)
  then show ?case 
    apply(cases "Tick \<in> sValues\<cdot>x",simp_all)
    apply(cases "Tick \<in> sValues\<cdot>y")
    apply(subst essplit_tickhdrt[of x, symmetric],simp)
    apply(subst essplit_tickhdrt[of y, symmetric],simp)
    apply(simp add: esnth_tsrt)
    apply(rule Suc.IH)
    using monofun_cfun_arg apply blast
    apply (metis (no_types, opaque_lifting) Fin_Suc lnat.inverts lnless_def tsrt_tlen)
    using sValues_prefix by blast
qed

lemma esnth_rule:assumes "\<And>n. n<lnsuc\<cdot>(#\<^sub>\<surd> s) \<Longrightarrow> P (esnth n\<cdot>(\<up>Tick \<Zcat> s))"
and "n< #\<^sub>\<surd> s"
shows"P (esnth n\<cdot>s)"
  using assms
  apply(induction n,simp_all)
  apply (metis Fin_02bot Fin_Suc inject_lnsuc lnat.inverts lnless_def lnzero_def esnth_nothing esnth_tick)
  by (metis Fin_Suc lnat.injects lnat.inverts lnless_def esnth_tick)

lemma tlen_eventstream:"#\<^sub>\<surd> s = #(sfilter {Tick}\<cdot>s)"
  apply(induction s,simp_all)
  apply(rule adm_eq,simp)
  apply(simp add: len_stream_def; fail)
  apply(case_tac a;simp)
  using lnat_suc_plus by blast

lemma e2ustream_len:"#(e2ustream\<cdot>s) = #(sfilter (minus (UNIV::'a event set) {Tick::'a event})\<cdot>s)"
  apply(induction s,simp_all)
  apply(simp add: len_stream_def)
  by(case_tac a;simp)


fun toListHelper::"'m list \<Rightarrow> 'm event \<Rightarrow> ('m list \<times> 'm list stream)" where
"toListHelper s Tick    = (   []    , \<up>s)" |
"toListHelper s (EventMsg m) = ( s @ [m] , \<epsilon> )"

definition sEventToList :: "'m event stream \<rightarrow> 'm list stream" where
"sEventToList = sscanlA toListHelper []"

lemma sscanltolist_h [simp]:"Tick \<notin> sValues\<cdot>s \<Longrightarrow> sscanlA toListHelper ls\<cdot>s = \<epsilon>"
  apply(induction s arbitrary: ls)
  apply(rule adm_imp,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg)  
  apply(simp add: lub_eq_Union; fail)
  by(case_tac a;simp)

lemma stimedtolistsimps[simp]:"sEventToList\<cdot>\<epsilon> = \<epsilon>"
  and [simp]:"sEventToList\<cdot>(\<up>Tick \<Zcat> s) = \<up>[] \<Zcat> sEventToList\<cdot>s"
  and [simp]:"sEventToList\<cdot>(\<up>(EventMsg a) \<Zcat> s) = (sscanlA toListHelper [a])\<cdot>s"
  and [simp]:"(sscanlA toListHelper ls)\<cdot>(\<up>Tick \<Zcat> s) = \<up>ls \<Zcat> sEventToList\<cdot>s"
  and [simp]:"Tick\<notin>sValues\<cdot>s \<Longrightarrow> sEventToList\<cdot>s = \<epsilon>"
  and [simp]:"sEventToList\<cdot>(\<up>Tick) = \<up>[]"
  by(simp_all add: sEventToList_def)

lemma stimedtolist_split_h:"#s1 < \<infinity> \<Longrightarrow> sscanlA toListHelper ls\<cdot>(s1 \<Zcat> \<up>Tick \<Zcat> s2) = sscanlA toListHelper ls\<cdot>(s1 \<Zcat> \<up> Tick) \<Zcat> sEventToList\<cdot>s2"
  apply(induction s1 arbitrary: ls)
  apply force
  apply simp
  apply(simp add: sEventToList_def; fail)
  apply(case_tac a;simp)
  apply(rule reduce_seq)
  by (metis fold_inf inf_less_eq not_less)+

lemma stimedtolist_split:"#s1 < \<infinity> \<Longrightarrow> sEventToList\<cdot>(s1 \<Zcat> \<up>Tick \<Zcat> s2) = sEventToList\<cdot>(s1 \<Zcat> \<up> Tick) \<Zcat> sEventToList\<cdot>s2"
  using sEventToList_def stimedtolist_split_h by metis

lemma svalues_belowelem[simp]: assumes "s1 \<sqsubseteq> s2"
  and "a\<in> sValues\<cdot>s1"
shows "a \<in> sValues\<cdot>s2"
  apply(subgoal_tac "sValues\<cdot>s1 \<subseteq> sValues\<cdot>s2")
  using assms apply blast
  by (simp add: assms(1))


lemma sscanlaut_split:"#s1<\<infinity> \<Longrightarrow> \<exists>nextState. sscanlA f state\<cdot>(s1 \<Zcat>\<Zcat> s2) = sscanlA f state\<cdot>(s1) \<Zcat>\<Zcat> sscanlA f nextState\<cdot>s2"
  apply(induction s1 arbitrary: state s2)
  apply force
   apply auto[1]
proof(simp)
  fix a s1 state s2
  assume a1:"(\<And>state s2. #s1 < \<infinity> \<Longrightarrow> \<exists>nextState. sscanlA f state\<cdot>(s1 \<Zcat> s2) = sscanlA f state\<cdot>s1\<Zcat>\<Zcat>sscanlA f nextState\<cdot>s2)"
  assume a2:"lnsuc\<cdot>(#s1) < \<infinity>"
  then obtain ns where ns_def:"sscanlA f (fst (f state a))\<cdot>(s1 \<Zcat> s2) = sscanlA f (fst (f state a))\<cdot>s1\<Zcat>\<Zcat>sscanlA f ns\<cdot>s2"
    using a1[of "(fst (f state a))" s2] a2 apply simp
    using dual_order.strict_trans2 less_lnsuc by blast
  show"\<exists>nextState.
          snd (f state a)\<Zcat>\<Zcat>sscanlA f (fst (f state a))\<cdot>(s1 \<Zcat> s2) =
          (snd (f state a)\<Zcat>\<Zcat>sscanlA f (fst (f state a))\<cdot>s1)\<Zcat>\<Zcat>sscanlA f nextState\<cdot>s2"
    apply(rule_tac x="ns" in exI,simp add: ns_def)
    by (simp add: assoc)
qed

lemma h:"Tick \<notin> sValues\<cdot>s \<Longrightarrow> smap (EventMsg \<circ> inv EventMsg)\<cdot>s = s"
  apply(induction s)
  apply(rule adm_imp,auto)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg)
  apply(simp add: lub_eq_Union; fail)
  by(case_tac a;simp)

lemma h2:"Tick \<in> sValues\<cdot>s \<Longrightarrow> \<up>Tick \<Zcat> srt\<cdot>(sdropwhile (\<lambda>e. \<exists>y. e = EventMsg y)\<cdot>s) = sdropwhile (\<lambda>e. \<exists>y. e = EventMsg y)\<cdot>s"
  apply(induction s,simp_all)
  by(case_tac a; simp)

lemma s_split: "Tick \<in> sValues\<cdot>s \<Longrightarrow> s = smap EventMsg\<cdot>(eshdts\<cdot>s) \<Zcat>(\<up>Tick) \<Zcat> (tsrt\<cdot>s)"
  apply (simp add: eshdts_def2 smapsmap2smap tsrt_def_2 srtdw_def)
  apply (subst h, simp add: aux_preds_eq)
  apply (simp add: one_lnat_def; fail) 
proof -
  assume a1: "Tick \<in> sValues\<cdot>s"
  have f2: "(\<lambda>e. \<exists>a. e = EventMsg (a::'a)) = (\<lambda>e. #\<^sub>\<surd> e = 0)"
    using aux_preds_eq by blast
  have "s = stakewhile (\<lambda>e. #\<^sub>\<surd> e = 0)\<cdot> s \<Zcat> sdropwhile (\<lambda>e. #\<^sub>\<surd> e = 0)\<cdot>s \<and> Tick \<in> sValues\<cdot>s"
    using a1 by (metis (no_types) stakewhileDropwhile)
  then show "s = stakewhile (\<lambda>e. \<exists>a. e = EventMsg a)\<cdot> s \<Zcat> \<up>Tick \<Zcat> srt\<cdot> (sdropwhile (\<lambda>e. #\<^sub>\<surd> e = 0)\<cdot> s)"
    using f2 h2 by force
qed

lemma s_split_list: "Tick \<in> sValues\<cdot>s \<Longrightarrow> s = smap EventMsg\<cdot>(<(s2list (eshdts\<cdot>s))>) \<Zcat>(\<up>Tick) \<Zcat> (tsrt\<cdot>s)"
  by(subst s2l2s_eq,simp_all add: s_split)
  
lemma stimedtoliststep:
" #s < \<infinity> \<Longrightarrow> Tick \<notin> sValues\<cdot>s \<Longrightarrow> sscanlA toListHelper ls\<cdot>(s \<Zcat> \<up>Tick) = \<up>(ls @ s2list (smap (inv EventMsg)\<cdot>s))"
proof(induction s arbitrary: ls)
  case adm
  then show ?case 
    by force
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  show ?case
    apply(case_tac a)
    using step.IH step.prems apply simp
    apply simp
    apply(subst s2list2lcons)
    using step.prems apply force
    apply(subst step.IH)
    using step.prems
    apply (metis inf_less_eq not_le_imp_less slen_sconc_snd_inf)
    using step.prems by auto
qed

lemma stimedtolist_tsstep_h:
  assumes "Tick\<in>sValues\<cdot>s"
  shows "sscanlA toListHelper ls\<cdot>s = \<up>(ls @ s2list (eshdts\<cdot>s)) \<Zcat> sEventToList\<cdot>(tsrt\<cdot>s)"
  apply(subst s_split,simp add: assms)
  apply(subst stimedtolist_split_h,simp add: assms)
  apply(subst stimedtoliststep,simp_all add: assms)
  by (simp add: smapsmap2smap)

lemma stimedtolist_tsstep:
  assumes"Tick\<in>sValues\<cdot>s"
  shows "sEventToList\<cdot>s = \<up>(s2list (eshdts\<cdot>s)) \<Zcat> sEventToList\<cdot>(tsrt\<cdot>s)"
  apply(subst sEventToList_def)
  by(subst stimedtolist_tsstep_h,simp_all add: assms)

lemma assumes "Fin n < #(sEventToList\<cdot>s)"
shows "snth (Suc n) (sEventToList\<cdot>s) = snth n (sEventToList\<cdot>(tsrt\<cdot>s))"
  apply(cases "Tick\<in> sValues\<cdot>s")
  using assms
  apply(induction n arbitrary: s)
  apply(subst stimedtolist_tsstep,simp,simp)+
  apply simp
  by(simp add: snth_rt)


lemma sscanla_tolist[simp]:"#(sscanlA toListHelper ls\<cdot>s) = #\<^sub>\<surd> s"
  apply(induction s arbitrary: ls)
  apply(rule adm_all)
  apply(rule adm_eq)
  apply(simp add: len_stream_def,simp_all)
  apply(case_tac a;simp)
  by (metis lnat_suc_plus)

lemma stimedtolistlen[simp]:"#(sEventToList\<cdot>s) = #\<^sub>\<surd> s"
  by(simp add: sEventToList_def)

lemma stimedtolist_snthtosvalues:
  assumes "Fin n < #(sEventToList\<cdot>s)"
  shows "set (snth n (sEventToList\<cdot>s)) \<subseteq> sValues\<cdot>(esnth n \<cdot>s)"
  using assms apply simp
proof(induction n arbitrary: s)
  case 0
  then show ?case
    apply(case_tac "Tick \<in> sValues\<cdot>s")
    apply(subst stimedtolist_tsstep,simp,simp)
    by(subst set2svalues,simp,simp,simp add: less_le)
next
  case (Suc n)
  then show ?case 
    apply(case_tac "Tick \<in> sValues\<cdot>s")
    apply(subst stimedtolist_tsstep,simp,simp)
    apply(simp add: esnth_tsrt)
    apply(subst Suc.IH)
    using tsrt_tlen
    apply (metis Fin_Suc leD leI lnsuc_lnle_emb)
    apply simp
    by (metis Fin_0 less_le_not_le lnle_Fin_0 tlentosvalues)
qed





lemma stimedtolist_well:
  "sValues\<cdot>(sEventToList\<cdot>s) \<subseteq> {ls. set ls\<subseteq> eValues\<cdot>s}"
proof(auto simp add: sValues_def2)
  fix xa n
  assume a1:"xa \<in> set (snth n (sEventToList\<cdot>s))"
  assume a2:" Fin n < #\<^sub>\<surd> s"
  have "xa \<in> sValues\<cdot>(esnth n\<cdot>s)"
    using stimedtolist_snthtosvalues a1 a2 by auto
  show "xa \<in> eValues\<cdot>s"
    using \<open>xa \<in> sValues\<cdot>(esnth n\<cdot>s)\<close> esnth_svalues by blast
qed

definition sListToEvent :: "'m list stream \<rightarrow> 'm event stream" where
"sListToEvent = sscanlA (\<lambda> _ list. 
  ((),smap EventMsg\<cdot>(list2s list) \<Zcat> \<up>Tick)) ()"

lemma slisttotimedsimps[simp]:"sListToEvent\<cdot>\<epsilon> = \<epsilon>"
  and [simp]:"sListToEvent\<cdot>((\<up>[]) \<Zcat> s) = (\<up>Tick) \<Zcat> sListToEvent\<cdot>s"
  and [simp]:"sListToEvent\<cdot>((\<up>(x#xs)) \<Zcat> s) = \<up>(EventMsg x) \<Zcat> sListToEvent\<cdot>((\<up>(xs)) \<Zcat> s)"
  by(simp_all add: sListToEvent_def)

lemma list2event2list_h [simp]:"sscanlA toListHelper ls\<cdot>(smap EventMsg\<cdot>(<list>) \<Zcat> \<up>Tick \<Zcat> s) = \<up>(ls @ list) \<Zcat> sscanlA toListHelper []\<cdot>s"
  by(induction list arbitrary: ls;simp)

lemma seventtolist_liststep [simp]:"sEventToList\<cdot>(smap EventMsg\<cdot>(<ls>) \<Zcat> \<up>\<surd> \<Zcat> s) = \<up>ls \<Zcat> sEventToList\<cdot>s"
  by(simp add: sEventToList_def)

lemma list2event2list: "(sEventToList oo sListToEvent) = ID"
  apply(rule cfun_eqI,auto)
  by(induct_tac x;simp add: sEventToList_def sListToEvent_def)

lemma slisttoevent_s2list_sconc:
  assumes "#as < \<infinity>"
  shows "sListToEvent\<cdot>(\<up>(s2list as) \<Zcat> bs) = (smap EventMsg\<cdot>as) \<Zcat> \<up>Tick  \<Zcat> sListToEvent\<cdot>bs"
proof-
  obtain n where n_def: "#as = Fin n"
    using assms lnat_well_h2 by blast
  show ?thesis
    using assms
    apply (induction as arbitrary: bs rule: finind [where n="n"])
    apply (simp_all add: n_def)
    apply (subst s2list2lcons)
    apply (force; fail)
    apply simp
    by (metis fold_inf inf_ub order.not_eq_order_implies_strict)
qed

lemma slisttoevent_svalues:
  "sValues\<cdot>(sListToEvent\<cdot>s) \<subseteq> EventMsg ` (\<Union>(set ` sValues\<cdot>s)) \<union> {Tick}"
  apply (induction s)
  apply (subst less_set_def [symmetric])
  apply (rule adm_below)
  apply (intro cont2cont; fail)
  apply (rule cont_compose [where f="\<lambda>x. \<Union> (set ` sValues\<cdot>x)"])
  apply (intro cont2cont; fail)
  apply (rule cont_compose [where f="\<lambda>x. sValues\<cdot>x"])
  apply (intro cont2cont; fail)+
  apply (simp; fail)
  apply (induct_tac a, simp_all)
  by blast

lemma e2ustream_step:
  "e2ustream\<cdot>s = (eshdts\<cdot>s) \<Zcat> e2ustream\<cdot>(tsrt\<cdot>s)"
  apply (simp add: e2ustream_def)
  apply (cases "Tick \<in> sValues\<cdot>s")
  apply (subgoal_tac "sfilter (UNIV - {Tick})\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>s) \<Zcat> (\<up>Tick) \<Zcat> tsrt\<cdot>s) = sfilter (UNIV - {Tick})\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>s)) \<Zcat> sfilter (UNIV - {Tick})\<cdot>(tsrt\<cdot>s)")
  apply (subst s_split [where s="s"], simp_all)
  apply (subst sfilter_snths_in_stream_lemma [symmetric])
  apply (metis (no_types, lifting) Diff_insert_absorb Tick_notin_image_Event UNIV_event_conv smap_sValues_range snth2sValues subsetD)
  apply (simp add: smap_split smapsmap2smap; fail)
  apply (metis Diff_insert_absorb Tick_notin_image_Event UNIV_event_conv add_sfilter lnat_well_h2 sfilter_nin eshdts_len slen_smap)
  apply (subst sfilter_snths_in_stream_lemma [symmetric])
  apply (metis Diff_insert_absorb Tick_notin_image_Event UNIV_I UNIV_event_conv insert_iff snth2sValues)
  by simp

lemma emap_evalues:
  "eValues\<cdot>(emap f\<cdot>s) = f ` eValues\<cdot>s"
  apply (induction s)
  apply (rule adm_eq)
  apply (intro cont2cont; fail)+
  apply (rule cont_compose [where f="Rep_cfun eValues"])
  apply (intro cont2cont; fail)+
  apply (simp;fail)
  by (case_tac a; simp)

lemma slisttoevent_evalues:
  "eValues\<cdot>(sListToEvent\<cdot>s) = \<Union>(set ` sValues\<cdot>s)"
proof (induction s)
  case adm
  then show ?case
    apply (rule adm_eq)
    apply (rule cont_compose [where f="Rep_cfun sListToEvent"])
    apply (intro cont2cont)+
    apply (rule cont_compose [where f="Rep_cfun sValues"])
    by (intro cont2cont)+
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then show ?case
    by (induction a, simp_all)
qed

lemma inveq_reduce_maps:
  assumes "inj h"
  and "inj g"
  and "inj f"
shows"smap (\<lambda>x. h (g (map_event f x)))\<cdot>(emap (inv f)\<cdot>
      (smap (\<lambda>x. inv g (inv h x))\<cdot>(smap (h o g)\<cdot>(emap f\<cdot>x)))) = 
      smap (h o g)\<cdot>(emap f\<cdot>x)"
  apply(induction x,simp_all)
  by(case_tac a;simp add: assms)

lemma sltoevent_infticks [simp]:
  "sListToEvent\<cdot>((\<up>[])\<^sup>\<infinity>) = ((\<up>Tick)\<^sup>\<infinity>)"
  apply (rule rek2sinftimes)
  apply (simp add: sListToEvent_def)
  by (subst sinftimes_unfold, simp+)

lemma eventlenleqlen[simp]:"#\<^sub>\<surd>(s::'a::countable event stream) \<le> #s"
proof(induction s)
  case adm
  then show ?case
    apply(subst lnle_def)
    by(rule adm_below,simp_all)
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then show ?case
    apply(cases a;simp add: lnat_suc_plus)
    by (meson less_lnsuc trans_lnle)
qed


definition listValues::"'m::countable list stream \<rightarrow> 'm set" where
"listValues = eValues oo sListToEvent"

lemma listvalues_eps[simp]:"listValues\<cdot>\<epsilon> = {}"
  by(simp add: oo_def listValues_def)

lemma listvalues_step[simp]:"listValues\<cdot> (\<up>(ls) \<Zcat> s) = set ls \<union> listValues\<cdot>s"
  apply(induction ls,simp)
  by(simp add: listValues_def oo_def)+



lemma "adm P \<Longrightarrow> (\<And>n s. # (s::'a::{countable}stream) = Fin n \<Longrightarrow> P s) \<Longrightarrow> P s"
  apply(rule stream_infs,simp_all)
  by (meson lnat_well_h2)

lemma ticklen_ind:"adm P \<Longrightarrow> (\<And>n s. #s<\<infinity> \<Longrightarrow> #\<^sub>\<surd> (s::'a::{countable} event stream) = Fin n \<Longrightarrow> P s) \<Longrightarrow> P s"
  apply(rule stream_infs,simp_all)
  by (metis LNat.LNat.lnat.exhaust eventlenleqlen lnat_well_h2 notinfI3)

lemma tsrt_len[simp]:"#(tsrt\<cdot>s) \<le> #s"
  apply(induction s)
  apply(subst lnle_def)
  apply(rule adm_below,simp add: len_stream_def,simp_all)
  by (metis (no_types, lifting) dual_order.trans less_lnsuc slen_scons srtlen_lnsuc tsrt_srt_len)

lemma below_tickend_to_eq:  "ys \<sqsubseteq> xs \<Zcat> \<up>\<surd> \<Longrightarrow> #\<^sub>\<surd>ys = lnsuc\<cdot>(#\<^sub>\<surd>xs) \<Longrightarrow> ys = xs \<Zcat> \<up>\<surd>"
  by (metis below_conc eq_less_and_fst_inf eventlenleqlen inf_less_eq less_lnsuc lnat_po_eq_conv lnle_and_gt_inf(2) mono_tlen)


lemma tslice_ind1:
  assumes "adm P"
  and "\<And>s. #s < \<infinity> \<Longrightarrow> #\<^sub>\<surd>s = Fin 0 \<Longrightarrow> P s"
  and "\<And>ls s. P s \<Longrightarrow> P (smap EventMsg\<cdot>(<ls>) \<Zcat> \<up>Tick \<Zcat> s)"
  shows "P s"
  apply(rule ticklen_ind,simp_all add: assms)
proof-
  fix n s
  show"#s < \<infinity> \<Longrightarrow> #\<^sub>\<surd> s = Fin n \<Longrightarrow> P s"
  proof(induction n arbitrary: s)
    case 0
    then show ?case 
      by (simp add: assms)
  next
    case (Suc n)
    then obtain ls where ls_def:"s = smap EventMsg\<cdot>(<ls>) \<Zcat>\<up>Tick\<Zcat> tsrt\<cdot>s"
      using s_split
      by (metis Fin_02bot LNat.lnat.inject Suc_neq_Zero lnzero_def s2l2s_eq eshdts_len tlentosvalues)
    show ?case 
      apply(subst ls_def)
      apply(rule assms(3))
      apply(rule Suc.IH,simp_all add: Suc.prems)
       apply (metis Suc.prems(1) fin_le_inf leD ninf2Fin tsrt_len)
      by (metis Fin_Suc lnat.sel_rews(2))
  qed
qed

lemma obtain_invls:"inj f \<Longrightarrow> set ls \<subseteq> f` S \<Longrightarrow> \<exists>ls2. ls = map f ls2"
  by (metis ex_map_conv image_iff subset_code(1))

lemma tslice_ind:
  assumes "adm P"
  and "\<And>ls. P (smap EventMsg\<cdot>(<ls>))"
  and "\<And>ls s. P s \<Longrightarrow> P (smap EventMsg\<cdot>(<ls>) \<Zcat> \<up>Tick \<Zcat> s)"
  shows "P s"
  apply(rule tslice_ind1)
  apply(simp_all add: assms)
  using assms(1) s2l2s_eq
  by (metis assms(2) invevent_eq slen_smap)

lemma e2ustream_sconc:"#s1<\<infinity> \<Longrightarrow> e2ustream\<cdot>(s1 \<Zcat> s2) = e2ustream\<cdot>s1 \<Zcat> e2ustream\<cdot>s2"
proof(induction s1 arbitrary: s2)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a s1)
  then show ?case
    by(cases a,simp_all add: less_le_not_le)
qed

lemma esnth_predicatetslice:
  assumes"(\<And>n::nat. Fin n < (1::lnat) + #\<^sub>\<surd> s \<Longrightarrow> P (esnth n\<cdot>(smap EventMsg\<cdot>(<ls>) \<Zcat> \<up>Tick \<Zcat> s)))"
  shows "Fin n < #\<^sub>\<surd> s \<Longrightarrow> P (esnth n\<cdot>s)"
  using assms[where n="Suc n"]
  by(simp add: esnth_tsrt lnat_suc_plus)

lemma tlen2e2ustreamlen[simp]:assumes"\<And>n. Fin n < #\<^sub>\<surd> s \<Longrightarrow> 0<#(esnth n\<cdot>s)"
  shows "#\<^sub>\<surd> s \<le> #(e2ustream\<cdot>s)"
  using assms
proof(induction s rule : tslice_ind)
  case 1
  then show ?case  
  apply(rule adm_imp,simp_all)
  apply(rule adm_upward)
  apply auto[1]
  apply(rule_tac x="xa" in exI)
  apply (metis (no_types, lifting) cont_pref_eq1I lnless_def esnthprefixeq tlen_stream_def trans_lnless)
  apply(subst lnle_def)
  by(rule adm_below,simp_all add: len_stream_def)
next
  case 2
  then show ?case 
    by simp
next
  case (3 ls s)
  have "0<#(smap EventMsg\<cdot>(<ls>))"
    using "3.prems"[where n=0] apply simp
    using eshdts_split_eq[of "smap EventMsg\<cdot>(<ls>)" s] apply auto[1]
    using gr_0 lnat_suc_plus by blast
  then show ?case
    apply auto[1]
    apply(simp add: e2ustream_sconc)
    apply(cases ls,simp_all add: lnat_suc_plus)
    apply(subgoal_tac "#\<^sub>\<surd> s \<le> #(e2ustream\<cdot>(s))")
    apply(simp add: sconc_slen2; fail)
    apply(rule "3.IH") apply(rule esnth_predicatetslice[where ls=ls]) using "3.prems" 
    by simp_all
qed

lemma esnth_tsrt_predicate[simp]:
  assumes"\<And>n. Fin (n) < #\<^sub>\<surd> i \<Longrightarrow> P (esnth n\<cdot>i)"
  shows "Fin n <#\<^sub>\<surd> (tsrt\<cdot>i) \<Longrightarrow> P (esnth n\<cdot>(tsrt\<cdot>i))"
  using assms[where n= "Suc n"]
  apply(simp add: esnth_tsrt)
  by (metis (mono_tags, lifting) less2lnleD nless_le tlen_tsrt_e trans_lnle tsrt_tlen2 tsrt_tlenleq)

lemma finsrt_tlen[simp]:
  assumes"Fin (Suc n) < (#\<^sub>\<surd>(i::'msg event stream))" 
  shows" Fin n < (#\<^sub>\<surd>(tsrt\<cdot>i))"
  using assms
  apply(subst(asm) s_split[of i])
  using assms
  apply (metis less2lnleD lnle_Fin_0 nat.discI tlentosvalues)
  using assms
  apply(subst(asm) tlen_tslice)
  using assms
  apply (metis empty_is_shortest notitckstlen eshdts_len slen_smap slen_zero)
  apply simp_all
  by (metis not_Tick_eq ticknotinsvalues tlen_event.simps(2))

lemma tslice_alt:
  assumes "adm P"
  and "P \<epsilon>"
  and "\<And>s ls t. (t = \<up>Tick \<or> (t=\<epsilon> \<and> s=\<epsilon>)) \<Longrightarrow> P s \<Longrightarrow> P (smap EventMsg\<cdot>(<ls>) \<Zcat> t \<Zcat> s)"
  shows "P s"
  apply(rule tslice_ind,simp_all add: assms)
  using assms(3)[where t=\<epsilon> and s=\<epsilon>] by (simp add: assms(2))

lemma liststream_event_induction:
  fixes s::"'m list stream"
  assumes "adm P"
    and "P \<epsilon>"
    and "\<And>xs ls msg. P ((\<up>ls)\<Zcat>xs) \<Longrightarrow> P ((\<up>(msg # ls)) \<Zcat> xs)"
    and "\<And>xs. P xs \<Longrightarrow> P ((\<up>[]) \<Zcat> xs)"
  shows "P s"
  apply(induction s)
    apply(simp add: assms)+
  apply(rename_tac ls xs, induct_tac ls)
  by(auto simp add: assms)

(*
definition u2estream::"('a stream \<rightarrow> 'a event stream) set"where
"u2estream = {f. \<forall>i. e2ustream\<cdot>(f\<cdot>i) = i}"

lemma [simp]:"u2estream \<noteq> {}"
  apply(simp add: u2estream_def)
  apply(rule ccontr,auto)
proof-
  assume a1:"\<forall>f. \<exists>i. e2ustream\<cdot>(f\<cdot>i) \<noteq> i"
  have "\<And>i. e2ustream\<cdot>(smap Event\<cdot>i) = i"
    apply(simp add: e2ustream_def)
    by(induct_tac i,simp_all)
  thus False
    using a1 by blast
qed

(*Empty!*)
definition nondetDelay::"('a event stream \<rightarrow> 'a event stream)set"where
"nondetDelay = ((\<lambda>f. f oo e2ustream) ` u2estream) \<inter> {f. weak f}"



lemma "nondetDelay = {}"
  apply(auto simp add: nondetDelay_def image_iff)
proof(simp add: weak_def)
  fix f::"'a stream \<rightarrow> 'a event stream"
  assume a1:"f\<in>u2estream"
  assume a2:"\<forall>i. wellformed i \<longrightarrow> #\<^sub>\<surd> i \<le> #\<^sub>\<surd> (f\<cdot>(e2ustream\<cdot>i))"
  have h1:"(f\<cdot>\<epsilon>) = sinftimes (\<up>Tick)"
  proof-
    have "e2ustream\<cdot>(f\<cdot>\<epsilon>) = \<epsilon>"
      sorry
    have h1_1:"#\<^sub>\<surd> (sinftimes (\<up>Tick)) \<le> #\<^sub>\<surd> (f\<cdot>(e2ustream\<cdot>(sinftimes (\<up>Tick))))"
      sorry
    then have h1_2:"sValues\<cdot>(f\<cdot>\<epsilon>) = {Tick}"
      sorry
    show ?thesis
      using h1_1 apply (simp add: e2ustream_def)
      apply(rule s_one_dom_inf)
      apply(simp add: h1_2)
      using eventlenleqlen 
      by (metis inf_less_eq)
  qed
  moreover have "#(f\<cdot>\<epsilon>) = \<infinity>"
    by(simp add: h1)
  moreover have "\<And>i. f\<cdot>i = f\<cdot>\<epsilon>"
    by (metis calculation(2) cont_pref_eq1I len_max minimal)
  ultimately have "\<And>a. e2ustream\<cdot>(f\<cdot>(\<up>a)) \<noteq> (\<up>a)"
    by(simp add: e2ustream_def)
  thus False
    using a1 u2estream_def by auto
qed*)

definition timeWrapper::"('a stream \<Rightarrow> 'a stream \<Rightarrow> bool) \<Rightarrow>('a event stream \<rightarrow> 'a event stream)set"where
"timeWrapper P = {f | f. weak f \<and> (\<forall>i. P (e2ustream\<cdot>i) (e2ustream\<cdot>(f\<cdot>i)))}"

lemma assumes"spf\<in>timeWrapper P"
  shows "P (e2ustream\<cdot>i) (e2ustream\<cdot>(spf\<cdot>i))"
  using assms by(simp add: timeWrapper_def)

definition nondetDelay_alt::"('a event stream \<rightarrow> 'a event stream) set"where
"nondetDelay_alt = timeWrapper (=)"


lemma efilter_tick_tlen [simp]: "Tick \<in> A \<Longrightarrow> #\<^sub>\<surd> (A \<ominus> x) = #\<^sub>\<surd> x"
  apply(induction x, simp add: tlen_stream_def)
   apply auto[1]
  apply(rename_tac msg x, case_tac msg; simp)
  by (metis add.right_neutral sfilter_in sfilter_nin stream_tlen_step2 tlen_event.simps(2))


definition counterexample::"unit event stream \<Rightarrow> unit event stream" where
"counterexample i \<equiv> if (i = ((\<up>(EventMsg ()))\<^sup>\<infinity>)) then (\<up>Tick)
                                           else sfilter {Tick}\<cdot>i"

lemma "#\<^sub>\<surd>i \<le> #\<^sub>\<surd> (counterexample i)"
  by(auto simp add: counterexample_def)

lemma "monofun counterexample"
  apply(rule monofunI, auto simp add: counterexample_def)
  apply (metis approxl3 assoc_sconc s2sinftimes sinftimes_unfold)
  apply (metis (no_types, lifting) cont_pref_eq1I event.distinct(1) minimal rev_below_trans sfilter_sinftimes_nin singleton_iff)
  using monofun_cfun_arg by blast

hide_const counterexample


lemma tshd_start_hin: "\<And>(s::bool event stream) (a::bool). tshd\<cdot>s = <[EventMsg a, Tick]> \<Longrightarrow> <[EventMsg a, Tick]> \<sqsubseteq> s"
proof -
  fix s::"bool event stream" and a::"bool"
  assume asm: "tshd\<cdot>s = <[EventMsg a, Tick]>"

  have "(stwbl (\<lambda>e::bool event. #\<^sub>\<surd> e = (0::lnat))\<cdot>s = <[EventMsg a, Tick]>) \<Longrightarrow> <[EventMsg a, Tick]> \<sqsubseteq> s"
    using stwbl_below[of "(\<lambda>e::bool event. #\<^sub>\<surd> e = (0::lnat))" s] by auto

  thus "<[EventMsg a, Tick]> \<sqsubseteq> s"
    using asm unfolding tshd_def by auto
qed
  
lemma tshd_start_rueck: "\<And>(s::bool event stream) (a::bool). <[EventMsg a, Tick]> \<sqsubseteq> s \<Longrightarrow> tshd\<cdot>s = <[EventMsg a, Tick]>"
proof -
  fix s a 
  
  have "(<[EventMsg a, Tick]> \<sqsubseteq> s) \<Longrightarrow> (stwbl (\<lambda>e::bool event. #\<^sub>\<surd> e = (0::lnat))\<cdot>s = <[EventMsg a, Tick]>)"
  proof -
    fix z
    assume xPrefix:  "<[EventMsg a, Tick]> \<sqsubseteq> s"

    hence xPrefix2: "(\<up>(EventMsg a) \<Zcat> \<up>\<surd>) \<sqsubseteq> s"
      by simp

    obtain y where ydef: "sdrop 2\<cdot>s = y"
      by simp

    have xdef: "(\<up>(EventMsg a) \<Zcat> (\<up>\<surd>) \<Zcat> y) = s"
      using xPrefix2 ydef 
      by (metis (no_types, lifting) One_nat_def Suc_1 approxl3 less_fst_sconsD sdrop_0 sdrop_forw_rt srt_supconc)

    have "(#\<^sub>\<surd> (\<up>\<surd>) \<noteq> (0::lnat))" 
      by (simp add: one_def)

    hence "(\<up>(EventMsg a) \<Zcat> (\<up>\<surd>) \<sqsubseteq> s) \<Longrightarrow> (stwbl (\<lambda>e::bool event. #\<^sub>\<surd> e = (0::lnat))\<cdot>s = \<up>(EventMsg a) \<Zcat> (\<up>\<surd>))"
      using xPrefix2 xdef by auto

    thus "(stwbl (\<lambda>e::bool event. #\<^sub>\<surd> e = (0::lnat))\<cdot>s = <[EventMsg a, Tick]>)"
      using xPrefix by simp
  qed
  thus "(<[EventMsg a, Tick]> \<sqsubseteq> s) \<Longrightarrow> tshd\<cdot>s = <[EventMsg a, Tick]>"
    unfolding tshd_def by auto
qed


end