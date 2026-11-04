theory EventLocale

imports BundleMerge EventAutomaton automaton.RefinementSignature
  EventAutomaton_AddChannel

begin

default_sort type


definition outconv::"('state::type\<times>('out::{echan,countable} msgWithChan) event list) set \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) set" where
"outconv  \<equiv> \<lambda> S. apsnd ((Rep_cfun uSplit) o list2s ) `S"

lemma outconv_apfst: "apfst f ` (outconv A) = outconv (apfst f ` A)"
  by(simp add: outconv_def image_comp)

lemma outconv_wellformed:
  assumes "(state, out) \<in> outconv S"
  shows "wellformed out"
  apply (insert assms)
  apply (simp add: wellformed_sb_def outconv_def)
proof (rule allI)
  fix c
  obtain sout where sout_set_in: "(state, sout) \<in> S" 
    and sout_def: "out \<^enum> c = uSplit\<cdot>((<sout>)) \<^enum> c"
    apply (insert assms)
    apply (simp add: outconv_def)
    by fastforce
  have "#(emap snd\<cdot>
      (efilter (\<lambda>(x::'b, e::msg). x = c)\<cdot>
       (emap Rep_msgWithChan\<cdot>((<sout>))))) \<le> #(<sout>)"
    by (metis (no_types, lifting) emap_def efilter_def slen_sfilterl1 slen_smap)
  thus "wellformed (out  \<^enum>  c)"
    apply (simp add: sout_def del: emap_len)
    apply (simp add: uSplit.rep_eq eventFilter_def toM.simps del: emap_len)
    apply (rule conjI)
    apply (metis Inf'_neq_0 slen_zero wellformed_stream_def)
    apply (simp add: sbgetch_insert del: emap_len)
    apply (rule impI)
    by (metis LNat.lnat.distinct(2) inf_less_eq slen_smap wellformed_stream_def)
qed

lemma outconv_monofun:"monofun outconv"
  apply(rule monofunI)
  by(auto simp add: outconv_def less_set_def)
lemma outconv_mono:"mono outconv"
  apply(rule monoI)
  by(auto simp add: outconv_def less_set_def)

fun eventWrapper_da::"('a::type event \<Rightarrow> ('state\<times>'b list)) \<Rightarrow>('a event  
                        \<Rightarrow> ('state::type\<times> 'b::type event list))" where
"eventWrapper_da f Tick = apsnd (\<lambda>ls. Tick#(map EventMsg ls)) (f Tick)"|
"eventWrapper_da f e = apsnd (\<lambda>ls. (map EventMsg ls)) (f e)"

fun eventWrapper::"('a::type event \<Rightarrow> ('state\<times>'b list) set) \<Rightarrow>('a event  
                        \<Rightarrow> ('state::type\<times> 'b::type event list) set)" where
"eventWrapper f Tick = apsnd (\<lambda>ls. Tick#(map EventMsg ls))` (f Tick)" |
"eventWrapper f e = apsnd (\<lambda>ls. map EventMsg ls)` (f e)"


locale eventGen =
  fixes ndaTransition_event::"'param::type \<Rightarrow> 'state::type 
         \<Rightarrow> ('in::{echan,enum,somechan} \<times> msg)  
         \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) set"
    and ndaTransition_tick::"'param::type \<Rightarrow> 'state::type  
         \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) set"
      and ndaInitConfig:: "'param 
         \<Rightarrow> ('state \<times> ('out msgWithChan) list) set"
      and delay::"bool" 
begin

definition ndaInitConfigC::"'param \<Rightarrow> ('state \<times> ('out msgWithChan) list) set" where
"ndaInitConfigC p \<equiv> if ndaInitConfig p= {} then UNIV else ndaInitConfig p"

definition ndaTransition_eventC::"'param::type \<Rightarrow> 'state::type \<Rightarrow> ('in::{echan,enum,somechan} \<times> msg)  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) set" where
"ndaTransition_eventC p s i \<equiv> if ndaTransition_event p s i = {} then UNIV
                                        else ndaTransition_event p s i"

definition ndaTransition_tickC::"'param::type \<Rightarrow> 'state::type  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) set" where
"ndaTransition_tickC p s \<equiv> if ndaTransition_tick p s = {} then UNIV
                                        else ndaTransition_tick p s"

fun ndaTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> (('in::{echan,enum,somechan} \<times> msg) event)
                        \<Rightarrow> (('state\<times>('out::{echan,finite} msgWithChan) list) set)" where
"ndaTransition p s (EventMsg m) = ndaTransition_eventC p s m" | 
"ndaTransition p s Tick      = ndaTransition_tickC p s" 


definition transition::"'param \<Rightarrow> 'state::type \<Rightarrow> 'in msgWithChan event  
                        \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) set" where
"transition p s = (outconv) o (eventWrapper (ndaTransition p s)) o map_event Rep_msgWithChan"

lemma trans_states: "fst ` transition p s input = fst `ndaTransition p s (map_event Rep_msgWithChan input)"
  apply(cases input)
  by(simp add: transition_def outconv_def image_comp)+


definition config::"'param \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) set" where
"config p = (if delay then outconv (apsnd (\<lambda>ls. map EventMsg ls@[Tick]) ` ndaInitConfigC p) else 
                            outconv (apsnd (\<lambda>ls. map EventMsg ls)` ndaInitConfigC p))"

lemma config_def2: 
  "config p = outconv (apsnd (\<lambda>ls. map EventMsg ls @ (if delay then [Tick] else [])) ` ndaInitConfigC p)"
  by(cases delay; simp add: eventGen.config_def)


lift_definition eaut::"'param \<Rightarrow> ('state, 'in msgWithChan event, 'out\<^sup>\<Omega>) automaton" is
"\<lambda>p. (transition p,config p)"
  apply(auto simp add: transition_def config_def outconv_def ndaInitConfigC_def)[1]
  apply(case_tac "map_event Rep_msgWithChan sbe")
  apply(simp_all add: ndaTransition_eventC_def ndaTransition_tickC_def)
  by (metis empty_not_UNIV)+

lemma autinitconfig2config[simp]: "autInitConfig\<cdot>(eaut p) = config p"
  by (simp add: autInitConfig_def eaut.rep_eq)

lemma auttrans2trans[simp]: "autTransition\<cdot>(eaut p) = transition p"
  by (simp add: autTransition_def eaut.rep_eq)

definition Sem :: "'param \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"where
"Sem p= mergeTimedId \<then> eSem (eaut p)"

lemma transition_in_out_leq:
  assumes "(state', out) \<in> transition p state msg"
  shows "#\<^sub>\<surd> msg \<le> #\<^sub>\<surd> out"
proof-
  have msg_one_leq: "#\<^sub>\<surd>msg \<le> 1"
    by (cases msg; simp)
  obtain convmsg where convmsg_def: "convmsg \<in> eventWrapper (ndaTransition p state) (map_event Rep_msgWithChan msg)"
    and "(state',out) = (apsnd (Rep_cfun uSplit \<circ> stream_abbrev) convmsg)"                       
    by (metis (no_types, opaque_lifting) assms comp_apply imageE outconv_def transition_def)
  hence out_insert: "out = (Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg)"
    by (metis snd_apsnd snd_conv)
  have "#\<^sub>\<surd>msg \<le> #\<^sub>\<surd> (<(snd(convmsg))>)"
    apply (insert convmsg_def)
    apply (cases msg; simp)
    using lnat_suc_plus neq02Suclnle one_lnat_def by auto
  thus "#\<^sub>\<surd> msg \<le> #\<^sub>\<surd> out"
    by (metis (no_types, lifting) demergelen inf_ub o_apply out_insert sbtlen_empty')
qed
  
lemma eaut_weak:
  assumes "spf \<in> eSem (eaut p)"
  shows "weak spf"
proof (rule weakI)
  fix i :: "'in msgWithChan event stream"
  have spf_sem: "spf \<in> (sem stream_step (eaut p))"
    apply (insert assms)
    by (simp add: eSem_def)
  then obtain initState initOut spf2 where init_state_out_def: "(initState,initOut)\<in>autInitConfig\<cdot>(eaut p)"
      and spf2_statesem: "spf2\<in>(stateSem stream_step (eaut p)) initState"
      and spf_apply: "spf\<cdot>i = initOut \<Zcat>\<Zcat> spf2\<cdot>i"
    using ndasem_pred by blast
  have initout_wellformed: "wellformed initOut"
    apply (insert init_state_out_def)
    apply (simp add: config_def)
    by (meson outconv_wellformed)
  have "#\<^sub>\<surd> i \<le> #\<^sub>\<surd> (spf2\<cdot>i)"
    apply (rule statesem_weak_ind [where conv="sup'" and aut="eaut p" and step="stream_step" and s="initState"])
    apply (metis conc_stream_def stream_tlen_eps streamind)
    apply simp+
    apply (rule conjI)
    using transition_in_out_leq apply blast
    using outconv_wellformed transition_def apply force
    apply force
    by (simp add: spf2_statesem)
  thus "#\<^sub>\<surd> i \<le> #\<^sub>\<surd> (spf\<cdot>i)"
    by (metis (no_types, lifting) initout_wellformed add.right_neutral dual_order.trans lessequal_addition lnat_plus_commu lnmin_smaller_addition spf_apply strict_lnmin_snd tlen_conc)
qed

lemma eaut_strong:
  assumes "spf \<in> eSem (eaut p)"
    and delay
  shows "strong spf"
proof (rule strongI)
  fix s :: "'in msgWithChan event stream"
  obtain initState initOut spf2 where init_state_out_def: "(initState,initOut)\<in>autInitConfig\<cdot>(eaut p)"
      and spf2_statesem: "spf2\<in>(stateSem stream_step (eaut p)) initState"
      and spf_apply: "spf\<cdot>s = initOut \<Zcat>\<Zcat> spf2\<cdot>s"
    apply (insert assms(1))
    apply (simp only: eSem_def)
    using ndasem_pred by blast
  then obtain initMsg where init_msg_def: "(initState, initMsg) \<in> (ndaInitConfigC p)"
    and "(initState, initOut) = apsnd ((Rep_cfun uSplit \<circ> stream_abbrev \<circ> ((\<lambda>ls. map EventMsg ls@[Tick])))) (initState, initMsg)"
    apply simp
    apply (simp add: config_def)
    apply (simp add: assms(2) outconv_def)
    apply (simp add: image_comp)
    apply (simp add: apsnd_compose)
    by auto
  hence "initOut = uSplit\<cdot>((<(map EventMsg (initMsg)@[Tick])>))"
    by auto
  hence "1 \<le> #\<^sub>\<surd>initOut"
    apply simp
    apply(cases "chDom TYPE('out) = {}")
    apply (metis ex_in_conv sbtlengeq')
    apply(subst demergelen)
    apply blast
    apply (subst stlen_appendtick,simp)
    by(simp add: one_def)
  have "#\<^sub>\<surd>s \<le> #\<^sub>\<surd>(spf2\<cdot>s)"
    apply (rule statesem_weak_stream [where aut="eaut p" and s="initState"])
    apply (simp add: spf2_statesem)
    by (simp add: outconv_wellformed transition_def transition_in_out_leq)
  thus "#\<^sub>\<surd> s <\<^sup>l #\<^sub>\<surd> (spf\<cdot>s)"
    by (metis (no_types, lifting) \<open>(1::lnat) \<le> #\<^sub>\<surd> (initOut::'out\<^sup>\<Omega>)\<close> dual_order.trans eventGen.autinitconfig2config eventGen.config_def init_state_out_def lessequal_addition lnat_plus_commu lnat_plus_suc outconv_wellformed spf_apply tlen_conc)
qed

lemma sem_weak:
  assumes "spf \<in> (Sem p)"
  shows "weak spf"
  proof -
    have "spf \<in> mergeTimed \<then> eSem (eaut p)"
      using assms apply (simp add: Sem_def seqcomp_insert)
      by (metis mergeIdInTimed subsetD)
    thus ?thesis
      using assms apply (simp add: Sem_def seqcomp_insert)
      apply auto
      by (metis bundlemerge_weak cfcomp_weak_well eventGen.eaut_weak)
  qed

lemma sem_strong:
  assumes "spf \<in> (Sem p)" and "delay"
  shows "strong spf"
  using assms apply (simp add: Sem_def seqcomp_insert)
  apply (simp add: eventGen.Sem_def seqcomp_insert)
  by (metis bundlemerge_weak cfcomp_strong_well2 eventGen.eaut_strong mergeIdInTimed subset_iff)
  

lemma esem_wellformed[simp]:
  assumes "spf \<in> (eSem (eaut p))"
  and "wellformed i"
shows"wellformed(spf\<cdot>i)"
  apply(rule wellformed_weakI)
    apply (meson assms(1) eventGen.eaut_weak weakI weak_def)
  by (simp add: assms(2))

lemma sem_wellformed[simp]:
  assumes "spf \<in> (Sem p)"
  and "wellformed i"
  shows"wellformed(spf\<cdot>i)"
  using assms
  apply(auto simp add: Sem_def seqComp_def)[1]
  using bundlemerge_wellformed esem_wellformed   
  using mergeIdInTimed by blast


definition daset::"'param \<Rightarrow> ('state \<times> ('in  msgWithChan event stream \<rightarrow> 'out\<^sup>\<Omega>), 'in msgWithChan event , 'out\<^sup>\<Omega>) dAutomaton set" where
  "daset p = nda2daset (eaut p)"

lemma daset_sem_eq_esem:
  shows "daSem stream_step ` (daset p) = eSem (eaut p)"
  apply(simp add: eSem_def)
  apply(subst nda2daset[where conv=sup'])
  apply(simp_all add: eventGen.daset_def)
  using stream_step_eps streamind by blast

lemma daset_not_empty: "daset p \<noteq> {}"
  using daset_sem_eq_esem sem_notempty eSem_def image_is_empty by metis

lemma daset_init: "da \<in> daset p \<Longrightarrow> 
  apfst fst (dautInitConfig da) \<in> autInitConfig\<cdot>(eaut p)"
  by (metis eventGen.daset_def nda2da_init)

lemma event_transition_has_event_output:
  assumes "(state', out) \<in> transition p state (EventMsg a)"
  shows "\<exists> convmsg. (state',out) = (apsnd (Rep_cfun uSplit \<circ> stream_abbrev) convmsg)
  \<and> convmsg \<in>  apsnd (\<lambda>ls. map EventMsg ls) ` (ndaTransition p state)
    (map_event Rep_msgWithChan (EventMsg a))
  \<and> out = (Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg)"
proof -
obtain convmsg where convmsg_def: "convmsg \<in>  eventWrapper 
   (ndaTransition p state) (map_event Rep_msgWithChan (EventMsg a))"
  and state_out_insert:
  "(state',out) = (apsnd (Rep_cfun uSplit \<circ> stream_abbrev) convmsg)"
    by (metis (no_types, opaque_lifting) assms
          comp_apply imageE outconv_def transition_def)
  hence out_insert: "out = (Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg)"
    by (metis snd_apsnd snd_conv)

  have not_tick:"Tick \<noteq>
    (map_event Rep_msgWithChan (EventMsg a))"
    by simp
  hence "eventWrapper (ndaTransition p state) 
    (map_event Rep_msgWithChan (EventMsg a)) =
    apsnd (\<lambda>ls. map EventMsg ls) ` (ndaTransition p state)
    (map_event Rep_msgWithChan (EventMsg a))"
    by simp
  hence "convmsg \<in>  apsnd (\<lambda>ls. map EventMsg ls) ` (ndaTransition p state)
    (map_event Rep_msgWithChan (EventMsg a))"
    using convmsg_def by simp
  with convmsg_def show ?thesis using state_out_insert out_insert by blast
qed

lemma event_transition_no_tick:
  assumes "chDom TYPE('out) \<noteq> {}"
  and "(state', out) \<in> transition p state (EventMsg a)"
shows "\<forall> m \<in> snd ` sbValues\<cdot>(out).  #\<^sub>\<surd> m = 0"
proof
   obtain convmsg where convmsg_def: "(state',out) = (apsnd (Rep_cfun uSplit \<circ> stream_abbrev) convmsg)
  \<and> convmsg \<in>  apsnd (\<lambda>ls. map EventMsg ls) ` (ndaTransition p state)
    (map_event Rep_msgWithChan (EventMsg a))" and
  out_insert:"out = (Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg)"
    using event_transition_has_event_output[where state'=state' and 
      out=out and p=p and state=state and a=a] using assms(2) by blast
  with convmsg_def assms(2) have convmsg_no_tick:
    "#\<^sub>\<surd> (<(snd convmsg)>) = 0" by force
  hence out_no_tick:"\<And> c. #\<^sub>\<surd> (out \<^enum> c) = 0"
    apply(subst out_insert)
    using ssplit_sbgetch_tlen assms(1)
    by (metis comp_apply)
  
  fix m assume "m \<in> snd ` sbValues\<cdot>(out)"
  then obtain c where c_def:"(c, m) \<in> sbValues\<cdot>out"
    by force
  with out_no_tick have c_tlen_0:"#\<^sub>\<surd> (out \<^enum> c) = 0" by simp

  have m_def:"m \<in> (sValues\<cdot>(out \<^enum> c))"
    apply(insert c_def)
    using sbvalues_insert by blast

  hence m':"m \<in> (sValues\<cdot>((Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg) \<^enum> c))"
    by (simp add:out_insert)

  obtain s where out_only_event_stream:"smap (Timed o TLive)\<cdot>s =  (out \<^enum> c)"
    using sb_echan_smapstream out_insert by metis

  with m_def have "m \<in> sValues\<cdot>(smap (Timed o TLive)\<cdot>s)" by simp
  then obtain m2 where m2_def:"m = (Timed (TLive m2))"
    by (metis comp_apply imageE smap_sValues)
    
  with c_tlen_0 m_def show "#\<^sub>\<surd> m = 0" 
    apply(case_tac m)
     apply simp
    apply(case_tac x2)
       apply(simp_all)
    by (metis 
\<open>\<And>thesis::bool. (\<And>s::msg event stream. smap (Timed \<circ> TLive)\<cdot>s = (out::'out\<^sup>\<Omega>) \<^enum> (c::'out) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
  inj_timed inj_tlive sValues_smapl1 smap_tlen smapsmap2smap tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlentosvalues)
qed

lemma mult_da_event_transitions_no_tick:
  assumes "da \<in> (daset param)"
  shows "\<forall> m \<in> snd `
   sbValues\<cdot>(snd (multTransitionsInOne da state (map EventMsg ls))).
  #\<^sub>\<surd> m = 0"
proof (induction ls arbitrary: state)
  case Nil
  then show ?case
  proof
    fix m assume m_def:"m \<in> snd `
   sbValues\<cdot>(snd (multTransitionsInOne da state (map EventMsg [])))"
    have trans:"snd (multTransitionsInOne da state (map EventMsg []))
      = (\<bottom>)" by simp

    with m_def have "m \<in> snd `
   sbValues\<cdot>(\<bottom>)"
      by (simp add: set_cpo_simps(3))
    
    thus "#\<^sub>\<surd> m = (0::lnat)"
      by (simp add: set_cpo_simps(3))
  qed
next
  case (Cons a ls)
  have "(map EventMsg (Cons a ls)) = Cons (EventMsg a) (map EventMsg ls)"
    by simp

  have step:"snd(multTransitionsInOne da state (map EventMsg (Cons a ls)))
    = snd (dautTransition da state (EventMsg a)) \<Zcat>\<^sup>\<Omega>
snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a)))
                      (map EventMsg ls))"
    by(simp add: conc_sb_def)

  have "snd(multTransitionsInOne da state (map EventMsg (Cons a ls)))
    =snd (dautTransition da state (EventMsg a))
    \<Zcat>\<Zcat> (snd (multTransitionsInOne da
         (fst (dautTransition da state (EventMsg a)))
           (map EventMsg ls)))"
    by simp

  have daut_step_no_tick:"\<forall> m \<in> snd ` 
    sbValues\<cdot>(snd (dautTransition da state (EventMsg a))).  #\<^sub>\<surd> m = 0"
    using auttrans2trans eventGen.daset_def event_transition_no_tick 
    by (metis assms local.Cons nda2da_trans sbValues_empty tuple_to_apfst)

  have step_subset:"sbValues\<cdot>
       (snd (dautTransition da state (EventMsg a)) \<Zcat>\<^sup>\<Omega>
        snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg ls)))
    \<subseteq> sbValues\<cdot>
       (snd (dautTransition da state (EventMsg a))) \<union> sbValues\<cdot>
       (snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg ls)))"
    by (simp add:sbValues_sbconc_subset_union)

  then show ?case
    apply(subst step)
    apply(simp add:sbValues_sbconc_subset_union)
  proof
    fix m assume "m \<in> sbValues\<cdot>
            (snd (dautTransition da state (EventMsg a)) \<Zcat>\<^sup>\<Omega>
             snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg ls)))"
    with step_subset have m_in_union:"m \<in> sbValues\<cdot>
       (snd (dautTransition da state (EventMsg a))) \<union> sbValues\<cdot>
       (snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg ls)))"
      by auto
    show " #\<^sub>\<surd> (snd m) = (0::lnat)"
      apply(case_tac "m \<in> sbValues\<cdot>(snd (dautTransition da state (EventMsg a)))")
       apply (metis daut_step_no_tick imageI)
      apply(insert m_in_union) 
      apply(simp)
      using Cons.IH by simp
  qed
qed

lemma event_transition_not_inf:
  assumes "chDom TYPE('out) \<noteq> {}"
  and "(state', out) \<in> transition p state (EventMsg a)"
shows "\<forall> c. # (out \<^enum> c)  < \<infinity>"
  proof
  obtain convmsg where convmsg_def: "(state',out) = (apsnd (Rep_cfun uSplit \<circ> stream_abbrev) convmsg)
  \<and> convmsg \<in>  apsnd (\<lambda>ls. map EventMsg ls) ` (ndaTransition p state)
    (map_event Rep_msgWithChan (EventMsg a))" and
  out_insert:"out = (Rep_cfun uSplit \<circ> stream_abbrev) (snd convmsg)"
    using event_transition_has_event_output[where state'=state' and 
      out=out and p=p and state=state and a=a] using assms(2) by blast
  with convmsg_def assms(2) have convmsg_not_inf:
    "# (<(snd convmsg)>) < \<infinity>" by force

  thus "\<And> c. # (out \<^enum> c) < \<infinity>"
    apply(subst out_insert)
    using ssplit_sbgetch_tlen assms(1)
    by (metis comp_apply eventlenleqlen inf_less_eq linorder_not_le wellformed_sb_def wellformed_ssplit wellformed_stream_def)
qed

lemma da_event_transition_not_inf:
  assumes "da \<in> (daset param)"
  and "chDom TYPE('out) \<noteq> {}"
  shows "\<And>c. #(snd (dautTransition da state (EventMsg a)) \<^enum> c) < \<infinity>"
proof -
  fix c
  have da_to_nda_trans:"(snd (dautTransition da state (EventMsg a)))
    \<in> snd ` ((transition param) (fst state) (EventMsg a))"
    using nda2da_trans_snd
    by (metis assms(1) auttrans2trans eventGen.daset_def)

  have nda_trans_not_inf:
    "\<forall> s \<in> (snd ` ((transition param) (fst state) (EventMsg a))).
    \<forall> c. #(s \<^enum> c) < \<infinity>"
    using event_transition_not_inf[where state="(fst state)" and p=param] assms
    by force

  show "#(snd (dautTransition da state (EventMsg a))  \<^enum>  c) < \<infinity>"
    using da_to_nda_trans nda_trans_not_inf by blast
qed

lemma mult_da_event_transitions_not_inf:
  assumes "da \<in> (daset param)"
  and "chDom TYPE('out) \<noteq> {}"
  shows "\<And>c. #((snd (multTransitionsInOne da state (map EventMsg ls)))  \<^enum> c) < \<infinity>"
proof (induction ls arbitrary: state)
  case Nil
  then show ?case by(simp)
next
  case (Cons a list)
  have sbConc:"(snd (dautTransition da state
            (EventMsg a))\<Zcat>\<Zcat>
  snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg list)))
  = sbConc (snd (dautTransition da state
            (EventMsg a)))\<cdot>(
  snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) (map EventMsg list)))"
    by (simp add: conc_sb_def)

  have "\<And>c. #((snd (multTransitionsInOne da (fst (dautTransition da state (EventMsg a))) 
  (map EventMsg list)))  \<^enum> c) < \<infinity>" using Cons.prems Cons.IH by simp
  thus ?case 
    apply simp 
    apply(subst sbConc)
    apply(subst sbconc_getch)
    using da_event_transition_not_inf sconc_slen assms by blast
qed

end

context
begin
lemma ndainitconfig_ref:
  assumes init_refine:"\<And>s out.  init2 p2 \<noteq> {} \<Longrightarrow> apfst f ` (init1 p1) \<subseteq> (init2 p2)"
  assumes init_refine_partial:"(init1 p1) = {} \<Longrightarrow> (init2 p2) = {}"
  shows "apfst f ` eventGen.ndaInitConfigC init1 p1 \<subseteq> eventGen.ndaInitConfigC init2 (p2)"
  by(simp add: eventGen.ndaInitConfigC_def assms)

lemma ndatrans_eventc_ref:
  fixes trans1_e::"'param1::type \<Rightarrow> 'state1::type \<Rightarrow> ('in1::{echan,enum,somechan} \<times> msg)  
                        \<Rightarrow> ('state1\<times>('out::{echan,finite} msgWithChan) list) set"
  fixes trans2_e::"'param2::type \<Rightarrow> 'state2::type \<Rightarrow> ('in2::{echan,enum,somechan} \<times> msg)  
                        \<Rightarrow> ('state2\<times>('out::{echan,finite} msgWithChan) list) set"
  assumes "\<And>t out. well (Rep_msgWithChan msg) \<Longrightarrow> (t, out) \<in> (trans1_e p1 state (Rep_msgWithChan msg)) \<Longrightarrow>
              (f t, out)  \<in> (trans2_e p2 (f state) (h (Rep_msgWithChan msg))) \<or> (trans2_e p2 (f state) (h (Rep_msgWithChan msg))) = {}"
     and partial: " well (Rep_msgWithChan msg) \<Longrightarrow> (trans1_e p1 state (Rep_msgWithChan msg)) = {} \<Longrightarrow> (trans2_e p2 (f state) (h (Rep_msgWithChan msg))) = {}"

  shows   "apfst f ` eventGen.ndaTransition_eventC trans1_e p1 state (Rep_msgWithChan msg)
       \<subseteq> eventGen.ndaTransition_eventC trans2_e p2 (f state) (h (Rep_msgWithChan msg))"
  apply(simp add: eventGen.ndaTransition_eventC_def)
  apply(intro conjI impI)
  using partial repeventwithsomechan_well   apply (metis(mono_tags))
  by (metis (no_types, lifting) apfst_convE assms(1) image_subset_iff repeventwithsomechan_well)

  private lemma eaut_trans_h:
    assumes "\<And>s sbe t out. well sbe \<Longrightarrow> Inv s \<Longrightarrow>  (t, out) \<in> (trans1_e p s sbe) \<Longrightarrow>
              (f t, out)  \<in> (trans2_e (g p) (f s) sbe) \<or> (trans2_e (g p) (f s) sbe) = {}"
        and "\<And>s t out. Inv s \<Longrightarrow> (t, out) \<in> (trans1_t p s) \<Longrightarrow>
                    (f t, out)  \<in> (trans2_t (g p) (f s)) \<or> (trans2_t (g p) (f s)) = {}"
  
    and "\<And>s sbe. well sbe \<Longrightarrow> Inv s \<Longrightarrow> (trans1_e p s sbe) = {} \<Longrightarrow> (trans2_e (g p) (f s) sbe) = {}"
    and "\<And>s.     Inv s \<Longrightarrow> (trans1_t p s) = {} \<Longrightarrow> (trans2_t (g p) (f s)) = {}"
    and inv: "Inv state"
    and "(nextState, out) \<in> eventGen.transition trans1_e trans1_t p state msg"
  shows "(f nextState, out) \<in> eventGen.transition trans2_e trans2_t (g p) (f state) msg"
proof - 
    have h0_tick: "\<And>out nextState msg. (nextState, out) \<in> eventGen.ndaTransition trans1_e trans1_t p state Tick \<Longrightarrow>
           (f nextState, out) \<in> eventGen.ndaTransition trans2_e trans2_t (g p) (f state) Tick"
      apply(simp add: eventGen.ndaTransition.simps)
      apply(simp_all add: eventGen.ndaTransition_tickC_def)
      apply auto[1]
      apply(case_tac "trans1_t p state = {}"; simp add: image_iff)
      apply (simp add: assms(4) inv)
      using assms(2) inv by auto[1]

    have h0_event: "\<And>out nextState msg. well msg \<Longrightarrow> (nextState, out) \<in> eventGen.ndaTransition trans1_e trans1_t p state (EventMsg msg) \<Longrightarrow>
           (f nextState, out) \<in> eventGen.ndaTransition trans2_e trans2_t (g p) (f state) (EventMsg msg)"
      apply(simp add: eventGen.ndaTransition.simps)
      apply(simp_all add: eventGen.ndaTransition_eventC_def)
      apply auto[1]
      apply(case_tac "trans1_e p state  (a,b) = {}"; simp add: image_iff)
      using assms(3) inv apply auto[1]  
      using assms(1) inv by blast
    have h1:"\<And> transition1 transition2 msg. 
      (apfst f ` (transition1 p state) msg \<subseteq>  transition2 (g p) (f state) msg) \<Longrightarrow> 
        apfst f ` outconv (eventWrapper (transition1 p state) msg) \<subseteq> outconv (eventWrapper (transition2 (g p) (f state)) msg )"
      apply(simp add: image_comp outconv_apfst)
      apply(rule monoD [where f=outconv]) 
       apply(rule monoI, simp add: outconv_def image_mono)
      apply(case_tac msg; simp add: image_comp) 
      using image_iff by fastforce+
  
    hence "apfst f ` eventGen.transition trans1_e trans1_t p state msg \<subseteq>
                    eventGen.transition trans2_e trans2_t (g p) (f state) msg"
      apply(insert trans)
      using eventGen.transition_def apply simp 
      apply(simp add: eventGen.transition_def)
      apply(rule h1)
      apply(cases "(map_event Rep_msgWithChan msg)")
      using h0_tick apply auto[1]
      using h0_event apply auto[1] 
      using repeventwithsomechan_well by metis 

    thus ?thesis
      using assms(6) by auto 
  qed  

  
  theorem eaut_statesem_refine:
    assumes "\<And>s sbe t out. well sbe \<Longrightarrow> Inv s \<Longrightarrow> (t, out) \<in> (trans1_e p s sbe) \<Longrightarrow>
              (f t, out)  \<in> (trans2_e (g p) (f s) sbe) \<or> (trans2_e (g p) (f s) sbe) = {}"
        and "\<And>s t out. Inv s \<Longrightarrow> (t, out) \<in> (trans1_t p s) \<Longrightarrow>
                    (f t, out)  \<in> (trans2_t (g p) (f s)) \<or> (trans2_t (g p) (f s)) = {}"
  
    and "\<And>s sbe. Inv s \<Longrightarrow> well sbe \<Longrightarrow> (trans1_e p s sbe) = {} \<Longrightarrow> (trans2_e (g p) (f s) sbe) = {}"
    and "\<And>s.     Inv s \<Longrightarrow> (trans1_t p s) = {} \<Longrightarrow> (trans2_t (g p) (f s)) = {}"
    and inv: "Inv state" 
  
    and invariant1_e: "\<And>currentState input nextState. Inv currentState \<Longrightarrow> well input
                   \<Longrightarrow> nextState \<in> fst ` trans1_e p currentState input
                   \<Longrightarrow> Inv nextState"
    and invariant2_e: "\<And>currentState input nextState. Inv currentState \<Longrightarrow> well input
                   \<Longrightarrow> trans1_e p currentState input = {}
                   \<Longrightarrow> Inv nextState"
  
    and invariant1_t: "\<And>currentState nextState. Inv currentState
                   \<Longrightarrow> nextState \<in> fst ` trans1_t p currentState
                   \<Longrightarrow> Inv nextState"
    and invariant2_t: "\<And>currentState nextState. Inv currentState
                   \<Longrightarrow> trans1_t p currentState = {}
                   \<Longrightarrow> Inv nextState"
  
  shows "eStateSem (eventGen.eaut trans1_e trans1_t init1 delay  p) state \<subseteq>
         eStateSem (eventGen.eaut trans2_e trans2_t init2 delay (g p)) (f state)"
    apply(simp add: eStateSem_def)
    apply(rule statesem_refine_rule [where Inv=Inv])
    apply (simp_all add: autTransition.rep_eq eventGen.eaut.rep_eq inv)
     apply(rule eaut_trans_h[where Inv=Inv and trans1_e="trans1_e" and trans1_t=trans1_t];simp add: assms(1-4))
    apply(simp add: eventGen.trans_states)
    apply(case_tac msg; simp add: eventGen.ndaTransition.simps)
    apply (metis eventGen.ndaTransition_tickC_def invariant1_t invariant2_t)
    by (metis eventGen.ndaTransition_eventC_def invariant1_e invariant2_e repeventwithsomechan_well)

   lemma eaut_statesem_trans_refine:
    assumes "\<And>s sbe t out. well sbe \<Longrightarrow> (t, out) \<in> (trans1_e p s sbe) \<Longrightarrow>
              (t, out)  \<in> (trans2_e p s sbe) \<or> (trans2_e p s sbe) = {}"
        and "\<And>s t out. (t, out) \<in> (trans1_t p s) \<Longrightarrow>
                    (t, out)  \<in> (trans2_t p s) \<or> (trans2_t p s) = {}"
  
    and "\<And>s sbe. well sbe \<Longrightarrow> (trans1_e p s sbe) = {} \<Longrightarrow> (trans2_e p s sbe) = {}"
    and "\<And>s.                  (trans1_t p s) = {} \<Longrightarrow> (trans2_t p s) = {}"
  
  shows "eStateSem (eventGen.eaut trans1_e trans1_t init1 delay p) state \<subseteq>
         eStateSem (eventGen.eaut trans2_e trans2_t init2 delay p) state"
    apply(rule eaut_statesem_refine[where Inv="\<lambda>_. True"])
    apply(simp_all add: assms)
    done    
    
  private lemma eaut_init_h: 
    assumes "\<And>s out. (s,out)\<in>(init1 p) \<Longrightarrow> (f s,out)\<in>(init2 (g p)) \<or> (init2 (g p)) = {}"
        and "init1 p = {} \<Longrightarrow> init2 (g p) = {}"
    shows "apfst f ` autInitConfig\<cdot>(eventGen.eaut trans1_e trans1_t init1 delay p) \<subseteq> 
                     autInitConfig\<cdot>(eventGen.eaut trans2_e trans2_t init2 delay (g p))"
    apply (simp add: autInitConfig.rep_eq eventGen.eaut.rep_eq)
    apply(subst eventGen.config_def)+
    apply(subst eventGen.ndaInitConfigC_def)+
    apply(cases delay; cases "init1 p = {}"; cases "init2 (g p) = {}"; simp)
    apply(simp_all add: assms outconv_apfst)
    apply(rule monoD [where f=outconv], rule monoI, simp add: outconv_def image_mono, simp add: image_iff image_subset_iff)+
    using assms(1) apply force
    apply(rule monoD [where f=outconv], rule monoI, simp add: outconv_def image_mono, simp add: image_iff image_subset_iff)+
    apply(rule ballI)
    apply(rule_tac x="((f (fst x)),(snd x))" in bexI,simp)
    using assms(1) by auto

  private lemma h: "apfst f ` B \<subseteq> A \<Longrightarrow> (s,out)\<in>B \<Longrightarrow>(f s, out) \<in> A"
    by auto

  theorem eaut_sem_refine:
    assumes "\<And>state. Inv state \<Longrightarrow> eStateSem (eventGen.eaut trans1_e trans1_t init1 delay  p) state \<subseteq>
                                   eStateSem (eventGen.eaut trans2_e trans2_t init2 delay (g p)) (f state)"
      and "\<And>s out. (s,out)\<in>(init1 p) \<Longrightarrow> (f s,out)\<in>(init2 (g p)) \<or> (init2 (g p)) = {}"
      and "init1 p = {} \<Longrightarrow> init2 (g p) = {}"
      and "\<And>s. s \<in> (fst ` init1 p) \<Longrightarrow> Inv s"
      and "init1 p = {} \<Longrightarrow> (\<And>s. Inv s)"
    shows "eSem (eventGen.eaut trans1_e trans1_t init1 delay  p) \<subseteq>
          eSem (eventGen.eaut trans2_e trans2_t init2 delay (g p))"
    apply(simp add: eSem_def)
    apply(rule sem_refine_rule [where f=f])
     apply(rule h [where B=" autInitConfig\<cdot>(eventGen.eaut trans1_e trans1_t init1 delay p)"])
      apply (simp add: assms(2) assms(3)eaut_init_h)
     apply simp

    unfolding eStateSem_def [symmetric]
    apply(rule assms(1))
     apply (simp add: autInitConfig.rep_eq eventGen.eaut.rep_eq)
    apply(subst (asm) eventGen.config_def)
    apply(cases delay; simp add: outconv_def image_comp)
     apply(subst (asm) eventGen.ndaInitConfigC_def,
        cases "init1 p = {}"; simp add: assms(4-5))+
    done

  theorem eaut_sem_trans_refine:
    assumes "\<And>state. eStateSem (eventGen.eaut trans1_e trans1_t init1 delay p) state 
                   \<subseteq> eStateSem (eventGen.eaut trans2_e trans2_t init2 delay p) state"
      and "\<And>s out. (s,out)\<in>(init1 p) \<Longrightarrow> (s,out)\<in>(init2 p) \<or> (init2 p) = {}"
      and "init1 p = {} \<Longrightarrow> init2 p = {}"
    shows "eSem (eventGen.eaut trans1_e trans1_t init1 delay p)
        \<subseteq> eSem (eventGen.eaut trans2_e trans2_t init2 delay p)"
    apply(rule eaut_sem_refine[where Inv="\<lambda>_. True" and f="id"])
    by(simp_all add: assms)

end


context
begin
definition restrictOut::"'csGreater::somechan msgWithChan list \<Rightarrow> 'csSmaller::chan msgWithChan list" where
"restrictOut ls = map ewcTypeCast (filter (\<lambda>msg. Rep (getChannel msg) \<in> chDom TYPE('csSmaller)) ls)"

definition restrictOutE::"'csGreater::{tchan,somechan} msgWithChan event list \<Rightarrow> 'csSmaller::tchan msgWithChan event list" where
"restrictOutE ls = map (map_event ewcTypeCast) (filter (case_event (\<lambda>msg. Rep (getChannel msg) \<in> chDom TYPE('csSmaller)) True) ls)" 


definition convertMsg::"(('chRef::chan \<times> msg) \<Rightarrow> ('chOrig::chan \<times> msg)) \<Rightarrow> 'chRef msgWithChan \<Rightarrow> 'chOrig msgWithChan" where
"convertMsg f msg_ch = Abs_msgWithChan (f (Rep_msgWithChan msg_ch))"

lemma convertmsg_switch: 
  fixes msg::"'cs::somechan msgWithChan"
  assumes "\<And>msg . well msg \<Longrightarrow> well (i msg)"
  shows "Rep_msgWithChan ((convertMsg i) msg) = i (Rep_msgWithChan msg)"
  apply(simp add: convertMsg_def)
  apply(subst Abs_msgWithChan_inverse2)
  apply(rule assms(1))
  by simp+

lemma convertmsg_event_switch:
  fixes msg::"'cs::somechan msgWithChan event"
  assumes "\<And>msg . well msg \<Longrightarrow> well (i msg)"
  shows "map_event Rep_msgWithChan (map_event (convertMsg i) msg) = 
      map_event i (map_event Rep_msgWithChan msg)"
  apply(cases msg; simp)
  using convertmsg_switch using assms by auto


lemma restrictoute_mapevent[simp]:"restrictOutE (map EventMsg ls) = map EventMsg (restrictOut ls)"
  unfolding restrictOutE_def restrictOut_def
  by(induction ls; simp)

lemma restrictoute_mapeventtick[simp]:"restrictOutE (map EventMsg ls @ [Tick]) = map EventMsg (restrictOut ls) @ [Tick]"
  unfolding restrictOutE_def restrictOut_def
  by(induction ls; simp)

lemma restrictoute_tick[simp]:"restrictOutE (Tick # ls) = Tick # restrictOutE ls"
  unfolding restrictOutE_def restrictOut_def
  by(induction ls; simp)

lemma restrictoute_nil [simp]: "restrictOutE [] = []"
  unfolding restrictOutE_def
  by(simp)
lemma restrictout_nil [simp]: "restrictOut [] = []"
  unfolding restrictOut_def
  by(simp)


lemma restrictoute_drop[simp]:
  assumes "Rep (getChannel msg) \<notin> chDom TYPE('csSub::{tchan})"
  shows "restrictOutE (EventMsg msg # ls) 
    = (restrictOutE (ls)::'csSub msgWithChan event list)"
  by(simp add: restrictOutE_def assms)

lemma restrictoute_in[simp]:
  assumes "Rep (getChannel msg) \<in> chDom TYPE('csSub::{tchan})"
  shows "restrictOutE (EventMsg msg # ls) 
    = EventMsg (ewcTypeCast msg) # (restrictOutE (ls)::'csSub msgWithChan event list)"
  by(simp add: restrictOutE_def assms)


lemma usplit_cast2restrict:
  assumes "chDom TYPE('csSub) \<subseteq> chDom TYPE('csSuper)"
  shows "(uSplit\<cdot>(<ls>)::'csSuper::{echan,somechan,countable}\<^sup>\<Omega>)\<star> 
      = (uSplit\<cdot>(<(restrictOutE ls)>)::'csSub::{echan,countable}\<^sup>\<Omega>)"
proof(induction ls)
  case Nil
  then show ?case by simp
next
  case (Cons msg ls)
  then show ?case
  proof(cases msg)
    case Tick
    then show ?thesis
      apply(simp only: restrictoute_tick, simp)
      apply(simp add: usplit_conc sbtypecast_conc)
      by (simp add: local.Cons usplit_tick_cast[OF assms])
  next
    case (EventMsg a)
    have "Rep (getChannel a) \<in> chDom TYPE('csSub) \<Longrightarrow> ?thesis"
      apply (simp add: usplit_conc sbtypecast_conc EventMsg)
      using usplit_cast_in[OF assms] by (metis local.Cons)
    moreover have "Rep (getChannel a) \<notin> chDom TYPE('csSub) \<Longrightarrow> ?thesis"
      apply (simp add: usplit_conc sbtypecast_conc EventMsg)
      using usplit_cast_notin by (metis botconc1 local.Cons)
    ultimately show ?thesis 
      by blast
  qed
qed
  
lemma outconv_mapprod: 
  assumes "chDom TYPE('csSub::{echan,countable}) 
        \<subseteq> chDom TYPE('csSuper::{echan,somechan,countable})"
  shows "map_prod f (sbTypeCast_abbr::('csSuper\<^sup>\<Omega> \<Rightarrow> 'csSub\<^sup>\<Omega>))  ` (EventLocale.outconv A)
                  = EventLocale.outconv (map_prod f restrictOutE ` A)"
  apply(simp add: EventLocale.outconv_def image_comp o_def apsnd_def prod.map_comp)
  apply(rule image_cong, simp)
  apply(case_tac x; simp)
  using usplit_cast2restrict[OF assms] .  

lemma mapconvertmsgwitchan_id: "(map_event (convertMsg id) msg) = msg"
  apply(cases msg; simp add: convertMsg_def)
  by (simp add: Rep_msgWithChan_inverse)

  private lemma eaut_trans_outmodify_h:
    fixes f::"'stateRef \<Rightarrow> 'stateOrig"
      and g::"'paramRef \<Rightarrow> 'paramOrig"
      and i::"('chRef::{echan,somechan,enum} \<times> msg) \<Rightarrow> ('chOrig::{echan,somechan,enum} \<times> msg)"

    assumes "\<And>s sbe t out. well sbe \<Longrightarrow> Inv s \<Longrightarrow>  (t, out) \<in> (trans1_e p s sbe) \<Longrightarrow>
              (f t, restrictOut out)  \<in> (trans2_e (g p) (f s) (i sbe)) \<or> (trans2_e (g p) (f s) (i sbe)) = {}"
        and "\<And>s t out. Inv s \<Longrightarrow> (t, out) \<in> (trans1_t p s) \<Longrightarrow>
                    (f t, restrictOut out)  \<in> (trans2_t (g p) (f s)) \<or> (trans2_t (g p) (f s)) = {}"
  
    and "\<And>s sbe. well sbe \<Longrightarrow> Inv s \<Longrightarrow> (trans1_e p s sbe) = {} \<Longrightarrow> (trans2_e (g p) (f s) (i sbe)) = {}"
    and "\<And>s.     Inv s \<Longrightarrow> (trans1_t p s) = {} \<Longrightarrow> (trans2_t (g p) (f s)) = {}"
    and i_well: "\<And> sbe. well sbe \<Longrightarrow> well (i sbe)"
    and inv: "Inv state"
    and "(nextState, out::'csSuper\<^sup>\<Omega>) \<in> eventGen.transition trans1_e trans1_t p state msg"
    and out_subset:"chDom TYPE('csSub::{echan,finite}) 
        \<subseteq> chDom TYPE('csSuper::{echan,somechan,finite})"
  shows "(f nextState, out\<star>::'csSub\<^sup>\<Omega>) \<in> eventGen.transition trans2_e trans2_t (g p) (f state) (map_event (convertMsg i) msg)"
proof - 
    have h0_tick: "\<And>out nextState msg. (nextState, out) \<in> eventGen.ndaTransition trans1_e trans1_t p state Tick \<Longrightarrow>
           (f nextState, restrictOut out) \<in> eventGen.ndaTransition trans2_e trans2_t (g p) (f state) Tick"
      apply(simp add: eventGen.ndaTransition.simps)
      apply(simp_all add: eventGen.ndaTransition_tickC_def)
      apply auto[1]
      apply(case_tac "trans1_t p state = {}"; simp add: image_iff)
      apply (simp add: assms(4) inv)
      using assms(2) inv by auto[1]

    have h0_event: "\<And>out nextState msg. well msg \<Longrightarrow> (nextState, out) \<in> eventGen.ndaTransition trans1_e trans1_t p state (EventMsg msg) \<Longrightarrow>
           (f nextState, restrictOut out) \<in> eventGen.ndaTransition trans2_e trans2_t (g p) (f state) (EventMsg (i msg))"
      apply(simp add: eventGen.ndaTransition.simps)
      apply(simp_all add: eventGen.ndaTransition_eventC_def)
      apply auto[1]
      apply(case_tac "trans1_e p state  (a,b) = {}"; simp add: image_iff)
      using assms(3) inv apply auto[1]  
      using assms(1) inv by blast
    have h1:"\<And> transition1 transition2 msg. 
      ((map_prod f (restrictOut)) ` (transition1 p state) msg \<subseteq>  transition2 (g p) (f state) (map_event (i) msg)) \<Longrightarrow> 
        (map_prod f (sbTypeCast_abbr::('csSuper\<^sup>\<Omega> \<Rightarrow> 'csSub\<^sup>\<Omega>))) ` EventLocale.outconv (eventWrapper (transition1 p state) msg)
                                       \<subseteq> EventLocale.outconv (eventWrapper (transition2 (g p) (f state)) (map_event (i) msg) )"
      apply(simp add: image_comp outconv_mapprod)
      apply(subst outconv_mapprod[OF out_subset])
      apply(rule monoD [where f=EventLocale.outconv]) 
       apply(rule monoI, simp add: EventLocale.outconv_def image_mono)
      apply(case_tac msg; simp add: image_comp) 
      apply(simp_all add: apsnd_def prod.map_comp o_def)
      apply auto [1]
      using image_iff by fastforce+ 
  
    hence "(map_prod f (Rep_cfun sbTypeCast)) ` eventGen.transition trans1_e trans1_t p state msg \<subseteq>
                    eventGen.transition trans2_e trans2_t (g p) (f state) (map_event (convertMsg i) msg)"
      apply(insert trans)
      using eventGen.transition_def apply simp 
      apply(simp add: eventGen.transition_def)
      apply(subst convertmsg_event_switch, simp add: i_well)
      apply(rule h1)
      apply(cases "(map_event Rep_msgWithChan msg)")
      using h0_tick apply auto[1]
      using h0_event apply auto[1] 
      using repeventwithsomechan_well by metis 

    thus ?thesis
      using assms(7) by auto
  qed  


lemma stream_step_outcast: "sbTypeCast oo stream_step\<cdot>f = stream_step\<cdot>(\<lambda>m. sbTypeCast oo f m)"
  apply(rule cfun_eqI)
  by(induct_tac x; simp)

theorem eaut_statesem_refine_outmodify:
    assumes "\<And>s sbe t out. well sbe \<Longrightarrow> Inv s \<Longrightarrow> (t, out) \<in> (trans1_e p s sbe) \<Longrightarrow>
              (f t, restrictOut out)  \<in> (trans2_e (g p) (f s) sbe) \<or> (trans2_e (g p) (f s) sbe) = {}"
        and "\<And>s t out. Inv s \<Longrightarrow> (t, out) \<in> (trans1_t p s) \<Longrightarrow>
                    (f t, restrictOut out)  \<in> (trans2_t (g p) (f s)) \<or> (trans2_t (g p) (f s)) = {}"
  
    and "\<And>s sbe. Inv s \<Longrightarrow> well sbe \<Longrightarrow> (trans1_e p s sbe) = {} \<Longrightarrow> (trans2_e (g p) (f s) sbe) = {}"
    and "\<And>s.     Inv s \<Longrightarrow> (trans1_t p s) = {} \<Longrightarrow> (trans2_t (g p) (f s)) = {}"
    and inv: "Inv state" 
  
    and invariant1_e: "\<And>currentState input nextState. Inv currentState \<Longrightarrow> well input
                   \<Longrightarrow> nextState \<in> fst ` trans1_e p currentState input
                   \<Longrightarrow> Inv nextState"
    and invariant2_e: "\<And>currentState input nextState. Inv currentState \<Longrightarrow> well input
                   \<Longrightarrow> trans1_e p currentState input = {}
                   \<Longrightarrow> Inv nextState"
  
    and invariant1_t: "\<And>currentState nextState. Inv currentState
                   \<Longrightarrow> nextState \<in> fst ` trans1_t p currentState
                   \<Longrightarrow> Inv nextState"
    and invariant2_t: "\<And>currentState nextState. Inv currentState
                   \<Longrightarrow> trans1_t p currentState = {}
                   \<Longrightarrow> Inv nextState"

      and inviariant1_init: "\<And>s. s \<in> (fst ` init1 p) \<Longrightarrow> Inv s"
      and inviariant2_init:"init1 p = {} \<Longrightarrow> (\<And>s. Inv s)"

    and out_subset:"chDom TYPE('csSub::{echan,finite}) 
        \<subseteq> chDom TYPE('csSuper::{echan,somechan,finite})"

  shows "eStateSem (eventGen.eaut trans1_e trans1_t init1 delay  p) state  \<then> { (sbTypeCast::'csSuper::{echan,somechan,finite}\<^sup>\<Omega>\<rightarrow>'csSub::{echan,finite}\<^sup>\<Omega>)} \<subseteq>
         eStateSem (eventGen.eaut trans2_e trans2_t init2 delay (g p)) (f state)"
    unfolding eStateSem_def seqcomp_image2
    apply(rule statesem_refine_rule_outmodify[where Inv=Inv])
         apply (simp_all add: autTransition.rep_eq eventGen.eaut.rep_eq inv)
    apply(subst mapconvertmsgwitchan_id[symmetric])
        apply(rule eaut_trans_outmodify_h[where Inv=Inv and trans1_e="trans1_e" and trans1_t=trans1_t])
               apply(simp add: assms(1-4) out_subset)+


    apply(simp add: eventGen.trans_states)
    apply(case_tac msg; simp add: eventGen.ndaTransition.simps)
    apply (metis eventGen.ndaTransition_tickC_def invariant1_t invariant2_t)
    apply (metis eventGen.ndaTransition_eventC_def invariant1_e invariant2_e repeventwithsomechan_well)

      apply (simp add: autInitConfig.rep_eq eventGen.eaut.rep_eq)
      apply(subst (asm) eventGen.config_def)
      apply(cases delay; simp add: outconv_def image_comp)
     apply(subst (asm) eventGen.ndaInitConfigC_def,
        cases "init1 p = {}"; simp add: inviariant1_init inviariant2_init)+

    using stream_step_outcast apply fastforce
    by (simp add: sbtypecast_conc)


lemma eaut_init_outmodify_h:
  assumes init_refine:"\<And>s out.  (s, out) \<in> (init1 p1) \<Longrightarrow>
                    (f s, restrictOut out)  \<in> (init2 p2) \<or> (init2 p2) = {}"
  assumes init_refine_partial:"(init1 p1) = {} \<Longrightarrow> (init2 p2) = {}"
   and "(s, (out::'csSuper::{echan,somechan,finite}\<^sup>\<Omega>)) \<in> autInitConfig\<cdot>(eventGen.eaut trans1_e trans1_t init1 delay p1)"
    and out_subset:"chDom TYPE('csSub::{echan,finite}) 
        \<subseteq> chDom TYPE('csSuper::{echan,somechan,finite})"
 shows "(f s, (out\<star>)::'csSub::{echan,finite}\<^sup>\<Omega>) \<in> autInitConfig\<cdot>(eventGen.eaut trans2_e trans2_t init2 delay p2)"
proof -
  let ?delmsg = "if delay then [Tick] else []"
  have h0: "((map_prod f (restrictOut)) ` (eventGen.ndaInitConfigC init1 p1 ) \<subseteq>  eventGen.ndaInitConfigC init2 p2)"
    apply(auto simp add: eventGen.ndaInitConfigC_def)[1]
    using init_refine init_refine_partial by blast+    

  have h1:"(map_prod f (sbTypeCast_abbr))
               ` EventLocale.outconv ((apsnd (\<lambda>ls. map EventMsg ls @ ?delmsg) ` (eventGen.ndaInitConfigC init1 p1 )))
               \<subseteq> EventLocale.outconv ((apsnd (\<lambda>ls. map EventMsg ls @ ?delmsg) ` (eventGen.ndaInitConfigC init2 p2)))"
    apply(simp add: image_comp outconv_mapprod)
    apply(cases delay; simp add: image_comp)

     apply(subst outconv_mapprod[OF out_subset])
      apply(rule monoD [where f=EventLocale.outconv]) 
       apply(rule monoI, simp add: EventLocale.outconv_def image_mono)
      apply(simp add: image_comp) 
      apply(simp_all add: apsnd_def prod.map_comp o_def)
     apply auto [1]
    using h0 image_iff apply fastforce

    apply(subst outconv_mapprod[OF out_subset])
      apply(rule monoD [where f=EventLocale.outconv]) 
       apply(rule monoI, simp add: EventLocale.outconv_def image_mono)
      apply(simp add: image_comp) 
      apply(simp_all add: apsnd_def prod.map_comp o_def)
     apply auto [1]
    using h0 image_iff apply fastforce
    done
  have "(f s, out\<star>) \<in> eventGen.config init2 delay p2"
    by (metis (no_types, lifting) apsnd_conv assms(3) eventGen.autinitconfig2config eventGen.config_def2 h1 image_cong map_prod_imageI prod.collapse subset_iff)
  thus ?thesis 
    by(simp add: eventGen.eaut.rep_eq autInitConfig.rep_eq)
qed



theorem eaut_sem_refine_outmodify:
  assumes "\<And>state. state \<in>fst`(autInitConfig\<cdot>(eventGen.eaut trans1_e trans1_t init1 delay  p)) \<Longrightarrow>
           eStateSem (eventGen.eaut trans1_e trans1_t init1 delay  p) state \<then> {sbTypeCast} \<subseteq>
         eStateSem (eventGen.eaut trans2_e trans2_t init2 delay (g p)) (f state)"

  and init_refine:"\<And>t out.  (t, out) \<in> (init1 p) \<Longrightarrow>
                    (f t, restrictOut out)  \<in> (init2 (g p)) \<or> (init2 (g p)) = {}"
  and  init_refine_partial:"(init1 p) = {} \<Longrightarrow> (init2 (g p)) = {}"

    and out_subset:"chDom TYPE('csSub::{echan,finite}) 
        \<subseteq> chDom TYPE('csSuper::{echan,somechan,finite})"
  shows "eSem (eventGen.eaut trans1_e trans1_t init1 delay  p) \<then> { (sbTypeCast::'csSuper::{echan,somechan,finite}\<^sup>\<Omega>\<rightarrow>'csSub::{echan,finite}\<^sup>\<Omega>)} \<subseteq>
         eSem (eventGen.eaut trans2_e trans2_t init2 delay (g p))"
  unfolding eSem_def seqcomp_image2
  apply(rule sem_refine_rule_outmodify[where f=f])
    apply (metis assms(1) eStateSem_def seqcomp_image2)
   apply(rule eaut_init_outmodify_h[of init1 p _ _ _ _ _ trans1_e trans1_t]; (simp add: assms)?)
  by (simp add: sbtypecast_conc)

end




context
begin

theorem eaut_sem_add_channel:
  fixes trans1_e::"'param1::type \<Rightarrow> 'state1::type \<Rightarrow> ('in1::{echan,enum,somechan} \<times> msg)  
                        \<Rightarrow> ('state1\<times>('out::{echan,finite} msgWithChan) list) set"
  fixes trans2_e::"'param2::type \<Rightarrow> 'state2::type \<Rightarrow> ('in2::{echan,enum,somechan} \<times> msg)  
                        \<Rightarrow> ('state2\<times>('out::{echan,finite} msgWithChan) list) set"

  assumes init_refine:"init2 p2 \<noteq> {} \<Longrightarrow> apfst f ` (init1 p1) \<subseteq> (init2 p2)"
    and init_refine_partial:"(init1 p1) = {} \<Longrightarrow> (init2 p2) = {}"

    and "\<And>s sbe t out. well sbe \<Longrightarrow> Rep (fst sbe) \<in> chDom TYPE('in2)\<Longrightarrow>  (t, out) \<in> (trans1_e p1 s sbe) \<Longrightarrow>
               (trans2_e (p2) (f s) (apfst (Abs o Rep) sbe)) \<noteq> {} \<Longrightarrow>
              (f t, out)  \<in> (trans2_e (p2) (f s) (apfst (Abs o Rep) sbe))"
        and "\<And>s t out. (t, out) \<in> (trans1_t p1 s) \<Longrightarrow> (trans2_t (p2) (f s)) \<noteq> {} \<Longrightarrow>
                    (f t, out)  \<in> (trans2_t (p2) (f s))"
  
    and "\<And>s sbe.  well sbe \<Longrightarrow> Rep (fst sbe) \<in> chDom TYPE('in2)\<Longrightarrow> (trans1_e p1 s sbe) = {} \<Longrightarrow> (trans2_e (p2) (f s) (apfst (Abs o Rep) sbe)) = {}"
    and "\<And>s.      (trans1_t p1 s) = {} \<Longrightarrow> (trans2_t (p2) (f s)) = {}"

    and new_msg: "\<And>s sbe t out. well sbe \<Longrightarrow> Rep (fst sbe) \<notin> chDom TYPE('in2)\<Longrightarrow> Rep (fst sbe) \<in> chDom TYPE('in1) \<Longrightarrow> (t, out) \<in> (trans1_e p1 s sbe) \<Longrightarrow>
               f t = f s \<and> out = []"
    and new_msg_no_partial: "\<And>s sbe. well sbe \<Longrightarrow> Rep (fst sbe) \<notin> chDom TYPE('in2)\<Longrightarrow> Rep (fst sbe) \<in> chDom TYPE('in1)\<Longrightarrow>  (trans1_e p1 s sbe) \<noteq> {}"

    and out_subset:"chDom TYPE('in2) \<subseteq> chDom TYPE('in1)"
  shows "eSem (eventGen.eaut trans1_e trans1_t init1 delay p1) \<subseteq>
         spsComplete ({ewcFiltercast} \<then> eSem (eventGen.eaut trans2_e trans2_t init2 delay p2))"
  apply(rule eventaut_refine_add_channel_msg[where f=f])
     apply(simp add: autInitConfig.rep_eq eventGen.eaut.rep_eq eventGen.config_def outconv_apfst )
     apply(intro conjI impI)
      apply(rule monoD[where f=outconv, OF outconv_mono])
      apply(simp add: apfst_snd_image_commu eventGen.ndaInitConfigC_def image_mono assms; fail)
      apply(rule monoD[where f=outconv, OF outconv_mono])
      apply(simp add: apfst_snd_image_commu eventGen.ndaInitConfigC_def image_mono assms; fail)

     apply(simp add: autTransition.rep_eq eventGen.eaut.rep_eq eventGen.transition_def outconv_apfst )
    apply(rule monoD[where f=outconv, OF outconv_mono])
    apply(simp add: apfst_snd_image_commu eventGen.ndaTransition.simps image_mono assms ewctypecast_rep)
    apply(subst ewctypecast_rep; simp add: assms )
     apply (simp add: getChannel_def)
    apply(rule image_mono)


    apply(rule ndatrans_eventc_ref; simp add: assms )
    using o_def assms apply (metis(mono_tags) apfst_eq_conv getChannel_def repeventwithsomechan_well)
    apply (metis apfst_eq_conv assms(5) comp_apply getChannel_def repeventwithchan_well somechannotempty)


     apply(simp add: autTransition.rep_eq eventGen.eaut.rep_eq eventGen.transition_def outconv_apfst )
    apply(rule monoD[where f=outconv, OF outconv_mono])
    apply(simp add: apfst_snd_image_commu eventGen.ndaTransition.simps image_mono assms ewctypecast_rep)
     apply(rule image_mono)
     apply(simp add: eventGen.ndaTransition_tickC_def)
  apply(intro conjI impI)

      apply (simp add: assms(6))
    using assms(4)  apply(auto)[1]
     apply blast


    apply(simp add: autTransition.rep_eq eventGen.eaut.rep_eq eventGen.ndaTransition.simps eventGen.transition_def outconv_def image_comp )
    apply auto
     defer
    apply (metis eventGen.ndaTransition_eventC_def getChannel_def new_msg new_msg_no_partial repeventwithchan_well repinrange somechandom somechannotempty)

    apply(rename_tac out)
    apply(case_tac "out=[]", simp)
    apply(auto simp add: eventGen.ndaTransition_eventC_def new_msg_no_partial new_msg getChannel_def)[1]

    by (meson chdom_in new_msg repeventwithsomechan_well somechannotempty)


end



locale eventdaGen =
  fixes daTransition_event::"'param::type \<Rightarrow> 'state::type \<Rightarrow> ('in::{echan,enum} \<times> msg)  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list)"
    and daTransition_tick::"'param::type \<Rightarrow> 'state::type  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list)"
      and daInitConfig:: "'param \<Rightarrow> ('state \<times> ('out msgWithChan) list)"
      and delay::"bool"
begin


fun daTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> (('in::{echan,enum} \<times> msg) event)
                        \<Rightarrow> (('state\<times>('out::{echan,finite} msgWithChan) list))" where
"daTransition p s (EventMsg m) = daTransition_event p s m" | 
"daTransition p s Tick      = daTransition_tick p s" 


definition transition::"'param \<Rightarrow> 'state::type \<Rightarrow> 'in msgWithChan event  
                        \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>)" where
"transition p s = (apsnd ((Rep_cfun uSplit) o list2s )) o (eventWrapper_da (daTransition p s)) o map_event Rep_msgWithChan"

lemma trans_states: "fst (transition p s input) = fst (daTransition p s (map_event Rep_msgWithChan input))"
  by(cases input,simp_all add: transition_def)


definition config::"'param \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>)" where
"config p = (if delay then apsnd ((Rep_cfun uSplit) o list2s ) (apsnd (\<lambda>ls. map EventMsg ls@[Tick])  (daInitConfig p)) else 
                            apsnd ((Rep_cfun uSplit) o list2s ) (apsnd (\<lambda>ls. map EventMsg ls)  (daInitConfig p)))"

lemma config_ddef[simp]:"delay \<Longrightarrow> config p = apsnd ((Rep_cfun uSplit) o list2s ) (apsnd (\<lambda>ls. map EventMsg ls@[Tick])  (daInitConfig p))"
  by(simp add: eventdaGen.config_def)

lemma config_nddef[simp]:"\<not>delay \<Longrightarrow> config p = apsnd ((Rep_cfun uSplit) o list2s ) (apsnd (\<lambda>ls. map EventMsg ls)  (daInitConfig p))"
  by(simp add: eventdaGen.config_def)


definition eda::"'param \<Rightarrow> ('state, 'in msgWithChan event, 'out\<^sup>\<Omega>) dAutomaton" where
"eda p = (|dautTransition = transition p, dautInitConfig = config p   |)"

lemma autinitconfig2config[simp]: "dautInitConfig (eda p) = config p"
  by (simp add: eda_def)

lemma auttrans2trans[simp]: "dautTransition (eda p) = transition p"
  by (simp add: eda_def)

definition Sem :: "'param \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"where
"Sem p= mergeTimedId \<then> {daSem stream_step (eda p)}"

lemma ssem_tlen[simp]:
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"#\<^sub>\<surd> (daStateSem stream_step (eda p) s\<cdot>i) = #\<^sub>\<surd> i"
proof(induction i arbitrary: s)
  case adm
  then show ?case
    by(rule adm_all, rule adm_eq,simp_all add: tlen_stream_def cont_compose_mix)
next
  case bottom
  then show ?case
    by (simp add: assms)
next
  case (step a i)
  then show ?case
    apply(subst dastatesem_step,simp add: case_prod_beta)
    apply(cases a,simp_all add: transition_def conc_sb_def)
    apply(subst sbtlen_conc_eq[where k="1"])
    apply(subst ssplit_sbgetch_tlen,simp add: assms,simp)
    apply(rule wellformed_ssplit)
    apply(simp add: wellformed_stream_def)
    apply(subst step.IH)
    using add.commute apply blast
    apply(subst sbtlen_conc_eq[where k="0"])
    apply(subst ssplit_sbgetch_tlen,simp add: assms,simp)
    apply(rule wellformed_ssplit)
    apply(simp add: wellformed_stream_def)
    apply(subst step.IH)
    by simp
qed

lemma sem_tlen_delay[simp]:
  assumes "chDom TYPE('out) \<noteq> {}"
  and "delay"
  shows"#\<^sub>\<surd> (daSem stream_step (eda p)\<cdot>i) =lnsuc\<cdot>(#\<^sub>\<surd> i)"
  apply(simp add: daSem_def case_prod_beta )
  apply(subst config_ddef,simp add: assms,simp add: conc_sb_def)
  apply(subst sbtlen_conc_eq[where k="1"])
  apply(subst ssplit_sbgetch_tlen,simp add: assms,simp)
  apply(rule wellformed_ssplit)
  apply(simp add: wellformed_stream_def)
  apply (simp add: slen_lnsuc)
  by (simp add: assms(1) lnat_plus_suc)

lemma sem_tlen_nodelay[simp]:
  assumes "chDom TYPE('out) \<noteq> {}"
  and "\<not>delay"
  shows"#\<^sub>\<surd> (daSem stream_step (eda p)\<cdot>i) =(#\<^sub>\<surd> i)"
  apply(simp add: daSem_def case_prod_beta )
  apply(subst config_nddef,simp add: assms,simp add: conc_sb_def)
  apply(subst sbtlen_conc_eq[where k="0"])
  apply(subst ssplit_sbgetch_tlen,simp add: assms,simp)
  apply(rule wellformed_ssplit)
  apply(simp add: wellformed_stream_def)
  apply (simp add: slen_lnsuc)
  by (simp add: assms(1) lnat_plus_suc)

lemma transitionout_finite_c[simp]:
  assumes "chDom TYPE ('out) \<noteq> {}"
  shows"#(snd (multTransitionsInOne (eda p) s ls) \<^enum>  c) < \<infinity>"
  apply(induction ls arbitrary: s c,simp_all add: assms)
  apply(simp add: conc_sb_def transition_def)
  apply(rule sconc_slen,simp_all)
  apply(subst ssplit_getch,simp_all add: assms)
  using efilter_len_leq emap_len
  by (metis inf_ub l2stream_finitelen verit_comp_simplify1(3) 
     verit_la_disequality)

lemma transitionout_finite[simp]:
  assumes "chDom TYPE ('out) \<noteq> {}"
  shows"#(snd (multTransitionsInOne (eda p) s ls)) < \<infinity>"
proof-
  obtain c where c_def:"#(snd (multTransitionsInOne (eda p) s ls)) =
                    #(snd (multTransitionsInOne (eda p) s ls) \<^enum> c)"
    using assms sblen2slen by blast
  thus ?thesis
    by(simp add: assms)
qed

end

end
