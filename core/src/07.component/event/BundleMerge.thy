theory BundleMerge

imports bundle.SBFin bundle.MsgWithChan
  stream.EventStream inc.Causality
  GeneralBundleMerge bundle.TSBFunction

begin

default_sort type






lemma emap_repabs_id:"emap Abs_msgWithChan oo emap Rep_msgWithChan = ID"
  apply(rule cfun_eqI,simp)
  apply(induct_tac x;simp)
  by(case_tac a;simp add: Rep_msgWithChan_inverse)

lemma emap_absrep_id:assumes "\<And>t. t\<in> eValues\<cdot>s \<Longrightarrow> well t"
  shows"emap Rep_msgWithChan\<cdot>(emap Abs_msgWithChan\<cdot>s) = s"
  apply(rule snths_eq)
  apply(simp)
  apply(auto simp add: emap_def smap_snth_lemma)[1]
  apply(case_tac "snth n s",simp_all)
  apply(rule Abs_msgWithChan_inverse2)
  by(simp add: assms evalues_snth)


lemma sbwell_h:assumes "chDom TYPE('cs::{echan,countable}) \<noteq>{}"
  shows  "sValues\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=(c::'cs))\<cdot>(emap Rep_msgWithChan\<cdot>s))) \<subseteq> insert Tick (EventMsg `cMsg (Rep c))"
  apply(induction s)
  apply(simp only: less_set_def[symmetric])
  apply(rule adm_below;simp)
  apply(simp)
proof(case_tac a;simp)
  fix s::"'cs msgWithChan event stream" and x1::"'cs msgWithChan"
  assume a1:"sValues\<cdot>(emap snd\<cdot>(efilter (\<lambda>a::'cs \<times> msg. case a of (x::'cs, e::msg) \<Rightarrow> x = c)\<cdot>(emap Rep_msgWithChan\<cdot>s)))
       \<subseteq> insert Tick (EventMsg ` cMsg (Rep c))"
  obtain a b where x1_def:"Rep_msgWithChan x1 = (a,b) \<and> b \<in> (cMsg (Rep a))"
    using assms repincMsg by blast
  then show"sValues\<cdot>
       (emap snd\<cdot>
        (efilter (\<lambda>a::'cs \<times> msg. case a of (x::'cs, e::msg) \<Rightarrow> x = c)\<cdot>(\<up>(EventMsg (Rep_msgWithChan x1)) \<Zcat> emap Rep_msgWithChan\<cdot>s)))
       \<subseteq> insert Tick (EventMsg ` cMsg (Rep c))"
    apply simp
    by(cases "a = c";simp_all add: a1)
qed

lemma sbwell_deMerge[simp]:
  assumes "chDom TYPE('cs::{echan,countable}) \<noteq> {}"
  shows"lsb_well (\<lambda>c::'cs. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>s))))"
  apply(rule lsbwellI)
  apply(simp add: ctype_echan_def assms smap_sValues)
  apply(rule subsetI)
  apply(case_tac "x=Timed (TLive Tick)";simp)
  apply(subgoal_tac "sValues\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x::'cs, e::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>s))) 
                      \<subseteq> insert Tick (EventMsg ` cMsg (Rep c))")
  apply auto[1]
  by (simp add: sbwell_h assms)

(*
text\<open>Using the new @{type msgWithChan} type for messages of an 
event stream, the event stream describes a stream bundle. To obtain
the stream bundle with an existing domain, each of the domains
channels map to the event streams representation filtered for the 
events of that channel.\<close>

lift_definition sSplit::"'cs msgWithChan event stream \<rightarrow> 'cs::{echan,finite} sb" is
"\<lambda> s. if chDom TYPE ('cs) = {} then \<bottom> 
      else Abs_lsb
  (\<lambda>c. smap (Timed o TLive)\<cdot>
      (emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>
      (emap Rep_msgWithChan\<cdot>s))))"
  apply(cases "chDomEmpty TYPE('cs)";simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply(rule sb_belowI)
  apply(simp add: sbgetch_insert2)
  apply (simp add: monofun_cfun_arg)
  by (simp add: contlub_cfun_arg contlub_cfun_fun contlub_lambda lub_lsb)
*)

lemma usplit_echan_well[simp]:
  assumes "chDom TYPE('chan::{echan, countable}) \<noteq> {}"
  shows "lsb_well (\<lambda>c::'chan. toM TTLive\<cdot>(eventFilter c\<cdot>s))"
  apply(subgoal_tac "\<And>c::'chan. TTLive = cTime (Rep (c))")
  apply (metis assms eventfilter_well lsbwellI tom_well)
  by (simp add: assms)


lemma ssplit_hideeventwithchan_rep:
  fixes f::"'a::cpo \<rightarrow> 'cs::{echan,finite} msgWithChan event stream"
  assumes "(emap Rep_msgWithChan oo f)\<cdot>a = g\<cdot>a"
  shows "Rep_lsb ((uSplit oo f)\<cdot>a) = (if chDom TYPE('cs) = {} then (\<lambda>c. \<epsilon>) else 
(\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(g\<cdot>a)))))"
  apply(simp add: uSplit.rep_eq)
  using assms apply(simp add: oo_def cfun_eq_iff eventFilter_def toM.simps)
  using empty_sbwell rep_sb_well by blast

lemma ssplit_hideeventwithchan_abs:
  fixes f::"'a::cpo \<rightarrow> 'cs::{echan,finite} msgWithChan event stream"
  assumes "(emap Rep_msgWithChan oo f)\<cdot>a = g\<cdot>a"
  shows "((uSplit oo f)\<cdot>a) = (if chDom TYPE('cs) = {} then \<bottom> else 
Abs_lsb(\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(g\<cdot>a)))))"
  apply(simp add: uSplit.rep_eq eventFilter_def toM.simps)
  using assms by(simp add: oo_def cfun_eq_iff)

lemma demerge_rep_eq:assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  shows "Rep_lsb ((uSplit\<cdot>sb)::'cs sb) = (\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>sb))))"
  by(simp add: uSplit.rep_eq assms eventFilter_def toM.simps)


lemma sbwell_step:assumes"lsb_well f"
  and "\<And>c::'cs::chan. sValues\<cdot>(a c) \<subseteq> ctype (Rep c)"
shows "lsb_well (\<lambda>c::'cs. a c \<Zcat> f c)"
  apply(rule lsbwellI)
  apply(auto simp add: assms)[1]
  using assms(1) lsb_well_def
  by (metis (mono_tags, opaque_lifting) UnE assms(2) in_mono sconc_sValues) 

lemma demerge_tickstep[simp]:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  shows"uSplit\<cdot>(\<up>Tick \<Zcat> s) = (ticksb::'cs sb) \<Zcat>\<^sup>\<Omega> uSplit\<cdot>s"
  apply(rule sb_rep_eqI)
  apply(simp add: uSplit.rep_eq eventFilter_def toM.simps)
  apply(subst Abs_lsb_inverse)
  apply simp
  apply(rule sbwell_step)
  apply (simp add: assms)
  apply(simp add: ctype_echan_def assms) 
  apply(simp add: sbConc.rep_eq sbgetch_insert2 ticksb.rep_eq)
  apply(subst Abs_lsb_inverse)
  apply simp_all
  apply(rule sbwell_step)
  apply (simp add: assms)
  by(simp add: ctype_echan_def assms) 

lemma demerge_tickstep2[simp]:
assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
shows "uSplit\<cdot>(\<up>Tick) = (ticksb::'cs sb)"
  apply (subst sconc_snd_empty [symmetric])
  apply (subst demerge_tickstep)
  apply (simp add: assms)
  by simp

lemma evwich_sbwell[simp]:assumes"chDom TYPE('cs::echan) \<noteq>{}"
  and "Rep_msgWithChan m = (cs,e)"
  shows"lsb_well(\<lambda>c::'cs. (if c = cs then \<up>(Timed (TLive (EventMsg e))) else \<epsilon>))"
  apply(rule lsbwellI)
   apply(simp add: ctype_echan_def assms)
  using repincMsg2 assms by blast

lemma evwichconcsb_sbwell[simp]:assumes"chDom TYPE('cs::echan) \<noteq>{}"
  and "Rep_msgWithChan m = (cs,e)"
  shows"lsb_well(\<lambda>c::'cs. (if c = cs then \<up>(Timed (TLive (EventMsg e))) else \<epsilon>) \<Zcat> Rep_lsb sb c)"
  apply(rule sbwell_step)
   apply(simp add: ctype_echan_def assms)+
  using repincMsg2 assms by blast

lemma demerge_estep:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  and "Rep_msgWithChan e = (cs,m)"
  shows"uSplit\<cdot>(\<up>(EventMsg e) \<Zcat> s) = Abs_lsb (\<lambda>c::'cs. if c = cs then \<up>(Timed (TLive (EventMsg m))) else \<epsilon>)  \<Zcat>\<^sup>\<Omega> uSplit\<cdot>s"
  apply(rule sb_rep_eqI)
  apply(subst uSplit.rep_eq,simp del: emapevent)
  apply (simp add: assms)
  apply(simp add: sbConc.rep_eq sbgetch_insert2 assms)
  using assms apply simp
  by(simp add: uSplit.rep_eq assms eventFilter_def toM.simps)

lemma demerge_estep_rep:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  and "Rep_msgWithChan e = (cs,m)"
  shows"Rep_lsb(uSplit\<cdot>(\<up>(EventMsg e) \<Zcat> s)) = (\<lambda>c::'cs. if c = cs then \<up>(Timed (TLive (EventMsg m))) \<Zcat> Rep_lsb(uSplit\<cdot>s) cs else Rep_lsb(uSplit\<cdot>s) c)"
  apply(subst demerge_estep,simp_all add: assms)
  apply(subst fun_eq_iff,auto)
  apply(simp_all add: repsb_sbconc sbgetch_insert2)
  apply(subst Abs_lsb_inverse)
  apply(simp)
  apply(rule lsbwellI)
  apply(case_tac "c=cs",simp_all add: assms ctype_echan_def)
  using assms repincMsg2[of e] apply blast
  apply(subst Abs_lsb_inverse)
  apply(simp)
  apply(rule lsbwellI)
  apply(case_tac "c=cs",simp_all add: assms ctype_echan_def)
  using assms repincMsg2[of e] by blast

lemma demerge_estep_repcs[simp]:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  and "Rep_msgWithChan e = (cs,m)"
shows"Rep_lsb(uSplit\<cdot>(\<up>(EventMsg e) \<Zcat> s)) (cs::'cs) = \<up>(Timed (TLive (EventMsg m))) \<Zcat> Rep_lsb(uSplit\<cdot>s) cs "
  by(subst demerge_estep_rep[where cs=cs and m=m],simp_all add: assms)

lemma demerge_estep_repc[simp]:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  and "Rep_msgWithChan e = (cs,m)"
  and "cs \<noteq> c"
shows"Rep_lsb(uSplit\<cdot>(\<up>(EventMsg e) \<Zcat> s)) (c::'cs) = Rep_lsb(uSplit\<cdot>s) c "
  apply(subst demerge_estep_rep,simp_all add: assms)
  using assms(3) by auto

lemma demerge_estep_rep_one:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  and "Rep_msgWithChan e = (cs,m)"
shows"Rep_lsb(uSplit\<cdot>(\<up>(EventMsg e))) =(\<lambda>c::'cs. if c = cs then \<up>(Timed (TLive (EventMsg m))) else \<epsilon>)"
  apply (subst fun_eq_iff,auto)
  using demerge_estep_repcs[where e=e and cs=cs and m=m and s=\<epsilon>]
  apply (simp add: assms)
   apply (subst sbgetch_insert2[symmetric],simp)
proof- 
  fix x::'cs
  assume a1:"x \<noteq>cs"
  then show "Rep_lsb (uSplit\<cdot>(\<up>(EventMsg e))) x = \<epsilon>"
    apply(insert demerge_estep_repc[where e=e and cs=cs and m=m and c=x and s=\<epsilon>],simp add: assms)
    by(subst sbgetch_insert2[symmetric],simp)
qed


lemma eventnolen[simp]:
  assumes "chDom TYPE('cs::{echan}) \<noteq> {}"
  and "Rep_msgWithChan e = (c,m)"
shows"#\<^sub>\<surd> (Abs_lsb (\<lambda>ca::'cs. if ca = c then \<up>(Timed (TLive (EventMsg m))) else \<epsilon>) \<Zcat>\<^sup>\<Omega> sb) = #\<^sub>\<surd>sb"
  apply(rule sbtlen_rule,simp add: assms)
   apply(rule sbtlenleq',simp add: assms,simp add: sbConc.rep_eq sbgetch_insert2)
  using assms apply simp
   apply blast
proof-
  obtain cl where cl_def:"#\<^sub>\<surd>sb = #\<^sub>\<surd>(sb \<^enum> cl)"
    using assms(1) sbtlen2stlen by blast
  show "\<exists>ca::'cs. #\<^sub>\<surd> (Abs_lsb (\<lambda>ca::'cs. if ca = c then \<up>(Timed (TLive (EventMsg m))) else \<epsilon>) \<Zcat>\<^sup>\<Omega> sb  \<^enum>  ca) = #\<^sub>\<surd> sb"
  apply(rule exI[where x=cl],simp)
  apply(simp add: assms sbgetch_insert2)
    using assms by (simp add: cl_def sbgetch_insert2)
qed

lemma demergelen[simp]:
  assumes "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
shows"#\<^sub>\<surd>((uSplit\<cdot>s)::'cs\<^sup>\<Omega>) = #\<^sub>\<surd> s"
  apply(induction s)
  apply(rule adm_eq,simp_all)
  apply(rule cont_compose [where f="Rep_cfun uSplit"],auto)
  apply(simp add: assms)
proof(case_tac a;simp add: assms lnat_suc_plus)
  fix aa::"'cs msgWithChan" and s::"'cs msgWithChan event stream"
  assume ind:"#\<^sub>\<surd> (uSplit\<cdot>s) = #\<^sub>\<surd> s"
  obtain c m where aa_def:"Rep_msgWithChan aa = (c,m)"
    using prod.exhaust_sel by blast
  then show "#\<^sub>\<surd> (uSplit\<cdot>(\<up>(EventMsg aa) \<Zcat> s)) = #\<^sub>\<surd> s"
    by(simp add: assms demerge_estep ind)
qed

lemma ssplit_sbgetch_tlen[simp]:
  assumes "\<not>chDomEmpty TYPE('a::{echan,finite})"
  shows "#\<^sub>\<surd>((uSplit\<cdot>s::'a\<^sup>\<Omega>) \<^enum> c) = #\<^sub>\<surd>s"
  apply (induction s)
  apply (rule adm_eq)
  apply (simp add: tlen_stream_def)
  apply (intro cont2cont)+
  apply simp
  apply (simp add: uSplit.rep_eq eventFilter_def toM.simps assms sbgetch_insert2)
  apply (case_tac a; simp)
  apply (case_tac aa; simp add: case_prod_unfold assms)
  apply (subst Abs_msgWithChan_inverse)
  apply fastforce
  by (case_tac "fst y = c"; simp)

lemma wellformed_ssplit[simp]:
  fixes s::"'a::{echan, finite} msgWithChan event stream"
    assumes"wellformed s"
  shows "wellformed (uSplit\<cdot>s)"
  apply(cases "chDom TYPE('a) = {}")
  apply(simp add: wellformed_sb_def wellformed_stream_def)+
  using assms apply(simp add: wellformed_stream_def)
  apply(intro impI allI)
  apply(simp add: sbgetch_insert2 demerge_rep_eq)
  by (metis antisym efilter_len_leq emap_len inf_ub)
  
lemma ssplit_getch:assumes "chDom TYPE ('cs::{echan,finite}) \<noteq> {}"
  shows"(uSplit\<cdot>s \<^enum> (c::'cs)) = smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(cs,e). cs= c)\<cdot>(emap Rep_msgWithChan\<cdot>s)))"
  by(simp add: uSplit.rep_eq eventFilter_def toM.simps sbgetch_insert2 assms)

lemma ssplit_eqI:
  fixes i::"'a::{echan, finite} msgWithChan event stream"
  assumes"uSplit\<cdot>i \<sqsubseteq> sb"
    and "#i=\<infinity>"
    and "wellformed i"
  shows "uSplit\<cdot>i = sb"
proof(rule sblen_sbeqI,simp_all add: assms, cases "chDom TYPE('a) = {}",simp)
  assume nempty:"chDom TYPE('a) \<noteq> {}"
  then obtain c where c_def:"#(uSplit\<cdot>i) = #(uSplit\<cdot>i \<^enum> c)"
    using sblen2slen by blast 
  then show "#(uSplit\<cdot>i) = \<infinity>"
    apply simp
    apply(subst ssplit_getch,simp_all add: nempty)
    apply(subgoal_tac "#\<^sub>\<surd> i = \<infinity>")
    using efilter_tlen
    apply (metis emap_tlen eventlenleqlen inf_less_eq)
    using assms well_tlen by blast
qed

lemma ssplit_prefixsb:
  assumes "uSplit\<cdot>i \<sqsubseteq> (sb::'cs\<^sup>\<Omega>)"
  and "chDom TYPE('cs::{echan,finite}) \<noteq> {}"
  shows "smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(c, m). c = cs)\<cdot>(emap Rep_msgWithChan\<cdot>i))) \<sqsubseteq> sb \<^enum> cs"
  apply(insert assms) apply(drule sbgetch_sbelow[where c=cs])
  apply(subst(asm) sbgetch_insert2)
  by(simp add: demerge_rep_eq)

lemma ssplit_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> (sb::'cs::{echan, finite}\<^sup>\<Omega>)"
and "chDom TYPE('cs) \<noteq> {}"
  and "Fin n < #\<^sub>\<surd>i"
shows "smap snd\<cdot>(sfilter {m. fst m = c}\<cdot>(smap (Rep_msgWithChan)\<cdot>(esnth n\<cdot>(i)))) = (esnth n\<cdot>(smap (inv TLive o inv Timed)\<cdot>(sb \<^enum> c)))"
  using assms(1)
  apply(simp add: smap_esnth filter_esnth)
  apply(rule esnthprefixeq)
proof(simp_all add: assms sbgetch_insert2)
  obtain s where s_def:"(Rep_lsb sb c) = smap (Timed o TLive)\<cdot>s"
    apply(simp add: sbgetch_insert2[symmetric])
    using sb_echan_smapstream by blast
  have "(\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>i)))) \<sqsubseteq> Rep_lsb sb"
    using demerge_rep_eq assms 
    by (simp add: below_lsb_def uSplit.rep_eq eventFilter_def toM.simps)
  then have h1:"smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>i))) \<sqsubseteq> Rep_lsb sb c"
    by (meson fun_belowD)
  show "emap snd\<cdot>(efilter (\<lambda>m::'cs \<times> msg. fst m = c)\<cdot>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> smap (inv TLive \<circ> inv Timed)\<cdot>(Rep_lsb sb c)"
    apply(simp add: s_def)
    apply(simp add: smapsmap2smap o_def)
    using h1
    by (metis (no_types, lifting) M.inject(2) M_timed.inject(3) comp_apply cond_case_prod_eta fst_conv s_def smapnotbelow)
qed

lemma bmerge_esnth:
  fixes i::"'a::{echan, finite} msgWithChan event stream"
  assumes"(esnth n\<cdot>(smap (inv TLive o inv Timed)\<cdot>(sb \<^enum> c))) \<noteq> \<epsilon>"
    and "uSplit\<cdot>i \<sqsubseteq> sb"
    and "Fin n <#\<^sub>\<surd>i"
  shows "(sfilter {m. fst (Rep_msgWithChan m) = c}\<cdot>(esnth n\<cdot>(i))) \<noteq>\<epsilon>"
  apply(subst sfilter_image[where f= Rep_msgWithChan])
  apply (simp add: Rep_msgWithChan_inject inj_on_def)
  apply(simp add: image_iff)
  apply(subst sfilter_smap[where f= snd])
  apply(subst sfilter_redimage)
  apply (meson Rep_msgWithChan_inject injI)
  using assms ssplit_esnth_eq
  by (metis (no_types, lifting) Collect_cong sbgetch_empty2 esnth_empty strict_smap sfilter_smap)

text\<open>With @{const uSplit} a definition of a non-deterministic 
bundle merge component is rather easy. A continuous function is a
correct bundle merge function, if its output describes a prefix
of the input bundle and the passage of time is the same. This 
implies all properties described above.\<close>
(*definition bundleMerge::
"('cs::{echan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set" where
"bundleMerge \<equiv> if chDom TYPE ('cs) = {} then {f | f. \<forall>sb. f\<cdot>sb = ((\<up>Tick)\<^sup>\<infinity>)} 
                  else {f | f. \<forall>sb. uSplit\<cdot>(f\<cdot>sb) \<sqsubseteq> sb
                               \<and>    #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(f\<cdot>sb))}"

SSt: Ersetzt durch \<open>mergeTimed\<close>

text\<open>In the case that the bundle has no channels, the component can
only react to the passage of time. Hence, the output stream is an
infinite stream of ticks.\<close>
(*<*)
definition bundleMerge_alt::"('cs::{echan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set" where
"bundleMerge_alt \<equiv> if chDom TYPE ('cs) = {} then {f | f. \<forall>sb. f\<cdot>sb = ((\<up>Tick)\<^sup>\<infinity>)} else 
                            {f | f. \<forall>sb c. smap (Timed o TLive)\<cdot>(emap (snd)\<cdot>(efilter (\<lambda>(x,m). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(f\<cdot>sb)))) \<sqsubseteq> sb \<^enum> c
                                           \<and>         #\<^sub>\<surd>sb = #\<^sub>\<surd>(f\<cdot>sb)}"
(*>*)


lemma bundlemerge_alt_eq:"bundleMerge_alt = bundleMerge"
  apply(cases "chDom TYPE('a) = {}")
  apply(simp add: bundleMerge_alt_def bundleMerge_def)
  apply(auto simp add: bundleMerge_def bundleMerge_alt_def)
  apply(rule sb_belowI)
  apply(simp add: sbgetch_insert2)
  apply(simp add: uSplit.rep_eq eventFilter_def toM.simps)
  by (metis demerge_rep_eq empty_iff sbgetch_insert2 sbgetch_sbelow)
*)
lemma 
  assumes "chDom TYPE('cs::{echan,finite}) = {}"
  shows " mergeTimed = {f | f. \<forall>sb::'cs\<^sup>\<Omega>. f\<cdot>sb = ((\<up>Tick)\<^sup>\<infinity>)}"
  oops (*
  by(simp add: mergeTimed_inftick assms) *)

lemma emptydom_mergenotempty: 
  assumes "chDom TYPE('cs::{echan,finite}) = {}"
  shows "(mergeTimed::('cs sb \<rightarrow> 'cs msgWithChan event stream) set) \<noteq> {}"
  by(simp add: assms)

theorem bundlemergeprops:
  assumes "f \<in> mergeTimed"
  shows "uSplit\<cdot>(f\<cdot>sb) \<sqsubseteq> (sb::'cs::{echan,finite}\<^sup>\<Omega>) \<and> #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(f\<cdot>sb))"
  using assms mergeTimed_eq_len mergeTimed_usplit by blast

lemma bundlemerge_rule:
  assumes "\<And>sb. uSplit\<cdot>(f\<cdot>sb) \<sqsubseteq> (sb::'cs::{echan,finite}\<^sup>\<Omega>) \<and> #\<^sub>\<surd>sb = #\<^sub>\<surd>((f\<cdot>sb))"
  and "chDom TYPE('cs) = {} \<Longrightarrow> f\<cdot>\<bottom> = ((\<up>Tick)\<^sup>\<infinity>)"
  shows "f \<in> mergeTimed"
  apply(auto simp add: GeneralBundleMerge.mergeTimed_def mergeGen_def assms)[1]
  using assms(2) apply (metis (full_types) sb_empty_eq)
  by (metis assms(1) demergelen ex_in_conv)



theorem bundlemergepred:
  assumes"f\<in> (mergeTimed \<then> SPS)"
     and "\<And>i g. g\<in> SPS \<Longrightarrow> uSplit\<cdot>i \<sqsubseteq> sb \<Longrightarrow> #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(i)) \<Longrightarrow> P (g\<cdot>i)"
   shows "P (f\<cdot>sb)"
  using assms
  apply(auto simp add: seqcomp_insert)[1]
  by (metis mergeTimed_eq_len mergeTimed_usplit)

theorem bundlemergeIdpred:
  assumes"f \<in> ((mergeTimedId::('cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set)  \<then> SPS)"
     and "\<And>i g. g \<in> SPS \<Longrightarrow> uSplit\<cdot>i = sb \<Longrightarrow> #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(i)) \<Longrightarrow> P (g\<cdot>i)"
     and "is_singleton(chDom (TYPE('cs)))"
   shows "P (f\<cdot>sb)"
  using assms
  apply(auto simp add: seqcomp_insert)[1]
  by (simp add: mergeTimedId_def)

theorem bundlemergeIdpredex:
  assumes "\<exists>g. \<forall>i. g\<in>SPS \<Longrightarrow> uSplit\<cdot>i = sb \<Longrightarrow> #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>i) \<Longrightarrow> P (g\<cdot>i)"
    and single:"is_singleton(chDom (TYPE('cs)))"
  shows "\<exists>f. f \<in> ((mergeTimedId::('cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set) \<then> SPS)
       \<and> P (f\<cdot>sb)"
  using assms
  apply(auto simp add: seqcomp_insert)[1]
  apply(auto simp add: mergeTimedId_def)
  oops

theorem bundlemergeIdpred2:
  assumes f_in:"f \<in> ((mergeTimedId::('cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set) \<then> SPS)"
    and Q_rule:"\<And>g i. g \<in> SPS \<Longrightarrow> mergeIdFunc\<cdot>sb = i \<Longrightarrow> g\<cdot>i = f\<cdot>sb \<Longrightarrow> Q(g oo mergeIdFunc)"
    and single:"is_singleton(chDom (TYPE('cs)))"
  shows "Q(f)"
proof -
  obtain spf1 spf2 where
    f_def: "f = spf2 oo spf1"
    and spf1_in:"spf1 \<in> (mergeTimedId::('cs sb \<rightarrow> 'cs msgWithChan event stream) set)"
    and spf2_in:"spf2 \<in> SPS"
    using f_in by (auto simp add: seqcomp_insert)

  have spf1_eq_mergeId: "spf1 = mergeIdFunc"
  proof (rule cfun_eqI)
    fix x :: "'cs sb"
    have "uSplit\<cdot>(spf1\<cdot>x) = x"
      using spf1_in single by (simp add: mergeTimedId_def)
    thus "spf1\<cdot>x = mergeIdFunc\<cdot>x"
      using single mergeIdFuncUSplitId by metis
  qed

  hence f_eq: "f = spf2 oo mergeIdFunc" using f_def by simp
  show "Q(f)" using Q_rule[OF spf2_in refl] f_eq by simp
qed

text\<open>And secondly, @{const mergeTimed} is weak causal.\<close>

theorem bundlemerge_weak:
  assumes "(f::('cs::{echan,finite})\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) \<in> mergeTimed"
  shows "weak f"
  apply (cases "chDomEmpty TYPE('cs)")
  apply (simp add: weak_def)
  using assms apply fastforce
  by (metis (no_types, opaque_lifting) assms demergelen bundlemergeprops leI lnless_def weak_def)


text\<open>Thirdly, any @{const wellformed} input leads to a @{const wellformed}
output.\<close>

theorem bundlemerge_wellformed:
  fixes f :: "('cs::{echan,finite})\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream"
  assumes "f \<in> mergeTimed"
    and "wellformed x"
  shows "wellformed (f\<cdot>x)"
  apply(rule wellformed_weakI)
  using bundlemerge_weak assms by auto[2]


text\<open>Such an descriptive specification for @{const mergeTimed} 
often simplified these proofs. But it leaves the question of 
consistency open. Furthermore, simulation, code export and searching
counterexample with \<open>quickcheck\<close> is not possible. All of these 
last issues will be tackled and overcome in section execBundleMerge.\<close>



context
begin

private definition conditionalComplete::"'csGreat::tchan sb \<Rightarrow> 'csSmall::tchan sb  \<rightarrow> 'csGreat sb" where
"conditionalComplete sbGreat = (\<Lambda> sbSmall. ((sbSmall \<uplus> (sbGreat \<Zcat>\<Zcat> (if(sbSmall \<sqsubseteq> (sbGreat\<star>)) then \<bottom> else sbInfTlen)))\<star>\<^sub>2))"


private lemma conditionalcomplete_insert: "conditionalComplete sbGreat\<cdot>sbSmall = 
  ((sbSmall \<uplus> (sbGreat \<Zcat>\<Zcat> (if(sbSmall \<sqsubseteq> (sbGreat\<star>)) then \<bottom> else sbInfTlen)))\<star>\<^sub>2)"
  apply(simp add: conditionalComplete_def)
  apply auto[1]
  apply(subst beta_cfun)
  apply(intro cont2cont)
  apply(rule adm2cont)
  apply(simp add: monofun_def)
  using below_trans apply blast
  apply simp+

  apply(subst beta_cfun)
  apply(intro cont2cont)
  apply(rule adm2cont)
  apply(simp add: monofun_def)
  using rev_below_trans apply blast
  by simp+

private lemma conditcomplete_below: "(conditionalComplete sbRel\<cdot>sb)\<star> \<sqsubseteq> sb"
  by(simp add: conditionalcomplete_insert sb_union_cast_below)

private lemma conditcomplete_id[simp]: "conditionalComplete input\<cdot>(input\<star>) = input"
  apply(simp add: conditionalcomplete_insert)
  by (metis sbconv_eq sbtypecast_reduce1 sbtypecast_reduce2 ubunion_id)

private lemma conditcomplete_tlen:
  assumes "chDom TYPE('csSmall) \<subseteq> chDom TYPE('csGreat)"
    and "#\<^sub>\<surd>(sbRel\<star>::'csSmall sb) \<le> #\<^sub>\<surd> sbRel" and well: "wellformed sbRel"
  shows "#\<^sub>\<surd>(sb::'csSmall::tchan sb) \<le> #\<^sub>\<surd>(conditionalComplete (sbRel::'csGreat::tchan sb)\<cdot>sb)"
  apply(auto simp add: conditionalcomplete_insert)[1]
       apply(cases "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>sbRel")
      apply (metis chdom_union inf_sup_ord(4) sbtypecast_tlen sbunion_tlen_fst_leq)
     defer
     apply(cases "#\<^sub>\<surd>sb \<le> #\<^sub>\<surd>(sbRel \<Zcat>\<Zcat>sbInfTlen)")
    apply (metis chdom_union inf_sup_ord(4) sbtypecast_tlen sbunion_tlen_fst_leq)
   defer
  using assms(2) mono_tlen order.trans apply blast
  apply(subst(asm) sbconc_well_inf[OF well])
  using inf_ub by blast


private lemma usplit_cast:
  assumes "chDom TYPE('csSub::{countable,echan}) \<subseteq> chDom TYPE('csSuper::{countable,echan})"
  shows "uSplit\<cdot>(ewcFiltercast\<cdot>s) = (sbTypeCast::'csSuper sb \<rightarrow> 'csSub sb)\<cdot>(uSplit\<cdot>s)"
  apply(induction s)
    apply simp
   apply simp
  apply (rename_tac msgwithchan rst)
  apply(case_tac msgwithchan; simp)
   apply(subst usplit_conc)+
   apply (simp add: assms sbtypecast_conc usplit_tick_cast)

   apply(rename_tac msg)
  apply(case_tac "Rep (getChannel msg) \<notin> chDom TYPE('csSub)")
  unfolding usplit_conc sbtypecast_conc
   apply(subst usplit_cast_notin; simp)

  unfolding usplit_conc sbtypecast_conc
  apply(subst usplit_cast_in; simp add: assms)
  unfolding usplit_conc sbtypecast_conc
  by metis


private definition mergeAdapter::"('csGreat::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'csGreat msgWithChan event stream) \<Rightarrow> 'csGreat sb 
                       \<Rightarrow> ('csSmall::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'csSmall msgWithChan event stream)" where
"mergeAdapter mergeGreat sbRel = (\<Lambda> sb . ewcFiltercast\<cdot>(mergeGreat\<cdot>((conditionalComplete sbRel\<cdot>sb))))"

private lemma mergeAdapter_in:
  fixes mergeSPF::"'csGreat::{echan,finite}\<^sup>\<Omega> \<rightarrow> _"
  assumes mergespf_in: "mergeSPF \<in> mergeTimed"
    and cssmall_not_empty:"chDom TYPE('csSmall) \<noteq> {}"
    and cssubset: "chDom TYPE('csSmall) \<subseteq> chDom TYPE('csGreat)"
    and "#\<^sub>\<surd>(sbRel\<star>::'csSmall sb) \<le> #\<^sub>\<surd> sbRel" and well: "wellformed sbRel"
  shows "mergeAdapter mergeSPF sbRel \<in> (mergeTimed :: ('csSmall::{echan,finite}\<^sup>\<Omega> \<rightarrow> _) set)"
proof(rule mergetimed_in)
  fix sb::"'csSmall\<^sup>\<Omega>"
  assume "chDomEmpty TYPE('csSmall)"
  thus "(mergeAdapter mergeSPF sbRel)\<cdot>sb = ((\<up>(Tick))\<^sup>\<infinity>)" using assms by simp
next
  fix sb::"'csSmall\<^sup>\<Omega>"
  have h0: "uSplit\<cdot>(mergeSPF\<cdot>(conditionalComplete sbRel\<cdot>sb)) \<sqsubseteq> conditionalComplete sbRel\<cdot>sb"
    using bundlemergeprops mergespf_in by blast
  have h1: "conditionalComplete sbRel\<cdot>sb\<star> \<sqsubseteq> sb" by (simp add: conditcomplete_below cssubset sb_star21)
  show "uSplit\<cdot>(mergeAdapter mergeSPF sbRel\<cdot>sb ) \<sqsubseteq> sb"
    apply(simp add: mergeAdapter_def)
    apply(subst usplit_cast[OF cssubset])
    by (meson below_refl box_below h0 h1 monofun_cfun_arg)
next
  fix sb::"'csSmall\<^sup>\<Omega>"
  have "#\<^sub>\<surd> sb \<le> #\<^sub>\<surd>(conditionalComplete sbRel\<cdot>sb)"
    using conditcomplete_tlen assms(4) cssubset well by blast

  thus "#\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(mergeAdapter mergeSPF sbRel\<cdot>sb))" 
    apply(simp add: mergeAdapter_def)
    by (metis conditionalcomplete_insert cssmall_not_empty cssubset demergelen ewcfilter_tlen less2eq mergeTimed_eq_len mergespf_in sb_union_cast_eq sbtypecast_tlen subset_empty)
qed

private lemma mergeAdapter_eq:
  fixes mergeSPF::"'csGreat::{echan,finite}\<^sup>\<Omega> \<rightarrow> _"
  fixes sbCast::"'csGreat::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'csSmall::{echan,finite}\<^sup>\<Omega>"
  assumes "mergeSPF \<in> mergeTimed"
    and cssubset: "chDom TYPE('csSmall) \<subseteq> chDom TYPE('csGreat)"
  shows "mergeAdapter mergeSPF input\<cdot>(input\<star>::'csSmall sb) = ewcFiltercast\<cdot>(mergeSPF\<cdot>input)"
  by(simp add: mergeAdapter_def)

theorem obtainmerge_cast:
  assumes "spfRefMerge \<in> mergeTimed"
    and cssubset: "chDom TYPE('csSmall::{finite,echan}) \<subseteq> chDom TYPE('csGreat)"
    and "chDom TYPE('csSmall) \<noteq> {}"
    and "#\<^sub>\<surd>(input\<star>::'csSmall sb) \<le> #\<^sub>\<surd> (input::'csGreat::{echan,finite}\<^sup>\<Omega>)" 
    and well: "wellformed input"
  shows "\<exists>spfOrigMerge \<in> mergeTimed. spfOrigMerge\<cdot>(input\<star>::'csSmall sb) 
        = ewcFiltercast\<cdot>(spfRefMerge\<cdot>input)"
  apply(rule bexI [where x="mergeAdapter spfRefMerge input"])
  using mergeAdapter_eq assms apply blast
  using mergeAdapter_in cssubset assms(1) assms(3) assms(4) well by blast

theorem bundlemerge_add_channel_obtain:
  fixes spfRef::"'csGreat::{echan,finite} sb \<rightarrow> 'cout::chan sb"
  assumes spsref_in: "spfRef \<in> (mergeTimed \<then> spsRef)"
    and input_tlen: "#\<^sub>\<surd>(input\<star>::'csSmall::{somechan,echan,finite} sb) \<le> #\<^sub>\<surd> input" 
    and well: "wellformed input"
    and chs_subset:"chDom TYPE('csSmall) \<subseteq> chDom TYPE('csGreat)"
    and sps_refine: "(spsRef) \<subseteq> spsComplete ({ewcFiltercast} \<then> spsOrig)"
  shows "\<exists>spfOrig::'csSmall sb \<rightarrow> _ \<in> (mergeTimed \<then> spsOrig). 
          spfRef\<cdot>input = spfOrig\<cdot>(input\<star>)"
proof -
  obtain spfRefMerge spfRefAut where spfref_insert:"spfRef = spfRefAut oo spfRefMerge"
      and spfrefmerge_in:"spfRefMerge \<in> mergeTimed"
    and spfrefaut_in: "spfRefAut \<in> spsRef"
    using assms(1) by (auto simp add: seqcomp_insert)

  obtain spfOrigAut where spforigaut_insert:"spfRefAut\<cdot>(spfRefMerge\<cdot>input) 
                         = spfOrigAut\<cdot>(ewcFiltercast\<cdot>(spfRefMerge\<cdot>input))" 
  and spforigaut_in: "spfOrigAut\<in> spsOrig"
    using sps_refine apply(auto simp add: spsComplete_def seqcomp_image)[1] 
    using old.unit.exhaust spfrefaut_in subset_iff by force 

  obtain spfOrigMerge where spforigmerge_insert:"spfOrigMerge\<cdot>(input\<star>::'csSmall sb) 
      = ewcFiltercast\<cdot>(spfRefMerge\<cdot>input)"
      and spforigmerge_in:"spfOrigMerge \<in> mergeTimed"
    using obtainmerge_cast spfrefmerge_in assms chs_subset somechannotempty input_tlen well less2eq by blast

  have "spfOrigAut oo spfOrigMerge \<in> (mergeTimed \<then> spsOrig)"
    apply (auto simp add: seqcomp_insert)[1]
    using spforigaut_in spforigmerge_in by fastforce
  thus ?thesis 
    using spforigaut_insert spforigmerge_insert spfref_insert by force
qed
end

lemma mergeTimed_eq_len_event: 
  fixes spf::"'cs::{echan,finite} sb \<rightarrow> 'cs msgWithChan event stream"
  assumes "spf\<in>mergeTimed"
  shows "#\<^sub>\<surd>sb = #\<^sub>\<surd>((spf\<cdot>sb))"
  apply(cases "chDom TYPE ('cs) = {}")
  using assms by(simp add: mergeTimed_def)+

lemma mergetimed_in_event:
  fixes spf::"'cs::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream"
  assumes "\<And>sb. chDom TYPE ('cs) = {} \<Longrightarrow> spf\<cdot>sb =  ((\<up>Tick)\<^sup>\<infinity>)"
    and "\<And>sb. chDom TYPE ('cs) \<noteq> {} \<Longrightarrow> uSplit\<cdot>(spf\<cdot>sb) \<sqsubseteq> sb" 
    and "\<And>sb. chDom TYPE ('cs) \<noteq> {} \<Longrightarrow> #\<^sub>\<surd>sb = #\<^sub>\<surd>(spf\<cdot>sb)"
  shows "spf \<in> mergeTimed"
  apply(rule mergetimed_in; simp add: assms)
  by (metis assms(3) demergelen)

lemma usplit_convert_below: 
  shows "uSplit\<cdot>(tsrt\<cdot>s) = (tsbRt\<cdot>(uSplit\<cdot>s)::'cs::{echan,finite}\<^sup>\<Omega>)"
  apply(induction s rule: eind)
     apply simp+
   apply(rule sb_eqI, simp add: usplit_conc sbconc_getch_split)
   apply(case_tac "getChannel msg = c")
    apply(subst usplit_e_insert, simp+)
    
  apply(cases "chDom TYPE('cs) \<noteq> {}")
  apply(subst demerge_tickstep, simp)
  apply(simp add: conc_sb_def[symmetric])
    apply(simp add: tsdrop_def)
  done

end
