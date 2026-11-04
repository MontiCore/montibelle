theory BundleMergeTs
  imports eventcomponent.EventLocale bundle.Timeconverter 
    automaton.Executable tscomponent.TsAutomatonExec 
begin

default_sort type




lemma sbhdts_snth_eq:
  assumes "Fin n < #(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  (c::'cs::echan))))"
  shows "snth n (smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  (c::'cs)))))) = snth n (sb \<^enum> c)"
proof-
  obtain s where s_def: "sb \<^enum> c = s"
    by blast
  hence "sValues\<cdot>(s) \<subseteq> range (Timed \<circ> TLive)"
    by (metis s_def echan_svalues empty_iff sValues_notempty sbgetch_empty subsetI)
  then show ?thesis
    using assms
    apply (simp add: s_def)
    apply (induction n arbitrary: s)
    apply (case_tac s)
    apply simp
    apply simp
    apply (case_tac a)
    apply fastforce
    apply (case_tac x2)
    apply fastforce
    apply fastforce
    apply (case_tac x3; simp add: eshdts_event)
    apply fastforce
    apply (case_tac s)
    apply simp
    apply simp
    apply (case_tac a)
    apply fastforce
    apply (case_tac x2)
    apply fastforce
    apply fastforce
    apply (case_tac x3; simp add: eshdts_event)
    by fastforce
qed

lemma sbhdts_svalues:
  "sValues\<cdot>(smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  (c::'cs))))))
  \<subseteq> sValues\<cdot>(sb \<^enum> (c::'cs::echan))"
  apply(cases "chDomEmpty TYPE('cs)")
  apply simp
  apply (rule svaluesSubsetI)
  apply (metis eshdts_len_leq slen_smap)
  by (metis sbhdts_snth_eq slen_smap)

lift_definition sbHdTs :: "('cs::echan)\<^sup>\<Omega> \<rightarrow> ('cs::echan)\<^sup>\<Omega>" is
  "\<lambda>sb. Abs_lsb (\<lambda>c. smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c)))))"
  apply (intro cont2cont)
  apply (rule lsbwellI)
  using sbgetch_ctypewell sbhdts_svalues by blast


lemma sbrtts_svalues:
  "sValues\<cdot>(smap (Timed \<circ> TLive)\<cdot>(tsrt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> (c::'cs::echan))))) \<subseteq> sValues\<cdot>(sb \<^enum> c)"
  apply (subgoal_tac "sValues\<cdot>(sb  \<^enum>  c) \<subseteq> ctype (Rep c)")
  apply (subgoal_tac "sValues\<cdot>(sb  \<^enum>  c)
       \<subseteq> range (Timed o TLive)")
  using smap_inv_svalues
  apply (metis (no_types, lifting) image_mono inj_timed inj_tlive smap_sValues tsrt_svalues)
  apply (cases "chDomEmpty TYPE('cs)")
  apply simp
  apply (subst (asm) ctype_echan_def, simp)
  apply blast
  using sbgetch_ctypewell by blast

lift_definition sbRtTs :: "('cs::echan)\<^sup>\<Omega> \<rightarrow> ('cs::echan)\<^sup>\<Omega>" is
  "\<lambda>sb. Abs_lsb (\<lambda>c. smap (Timed \<circ> TLive)\<cdot>(tsrt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c))))"
  apply (intro cont2cont)
  apply (rule lsbwellI)
  by (meson dual_order.trans sbgetch_ctypewell sbrtts_svalues)


fun listmerge::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"listmerge [] b = [b]" |
"listmerge a [] = [a]" |
"listmerge (a#as) (b#bs) = (map (Cons a) (listmerge as (b#bs))) @ (map (Cons b)(listmerge (a#as) bs))"

fun tsmerge::"'a list list \<Rightarrow> 'a list list" where
"tsmerge [] = [[]]" |
"tsmerge [a] = [a]"|
"tsmerge (a#b#ls) =  concat (map (\<lambda>merged. tsmerge (merged#ls)) (listmerge a b))"


fun mergetrans::"'a::countable list list \<Rightarrow> (unit \<times> 'a list stream) list" where
"mergetrans ls = map (\<lambda>l. ((),\<up>l)) (tsmerge ls)"


definition mergeAut::"(unit,'a::countable list list, 'a list stream) listAutomaton" where
"mergeAut = (|listTransition = (\<lambda>s. mergetrans), listInitConfig = [((),\<epsilon>)]|)"




fun m2event::"M \<Rightarrow> msg event" where
"m2event (Timed (TLive e))= e"|
"m2event (Timed (TFin [])) = Tick"|
"m2event (Timed (TFin (x#xs))) = EventMsg x"|
"m2event (Untimed e) = EventMsg e"|
"m2event (Timed (Tsyn Eps)) = Tick"|
"m2event (Timed (Tsyn ts)) = undefined"|
"m2event (Timed (TOne (TOneMsg va))) = EventMsg va"


definition convtrans::"'cs::{tschan,enum}\<^sup>\<surd> \<Rightarrow> ('cs \<times> msg) list list" where
"convtrans sbe \<equiv> if chDom TYPE('cs) = {} then ([]) else 
                            (map (\<lambda>c. map (\<lambda>e. (c,e)) (sbelist c sbe)) Enum.enum)"

definition convertAut::"(unit,'cs::{tschan,enum}\<^sup>\<surd>, ('cs\<times> msg) list list stream) dAutomaton" where
"convertAut = (|dautTransition = (\<lambda>s sb. (( (),\<up>(convtrans sb)))), dautInitConfig = ((),\<epsilon>)|)"

definition convertSem::"'cs::{tschan,enum}\<^sup>\<Omega> \<rightarrow> ('cs \<times> msg) list list stream" where
"convertSem= tsExecSem convertAut"

definition mergeStateSem::"unit \<Rightarrow> ('a::countable list list stream \<rightarrow> 'a list stream) set" where
"mergeStateSem = stateSem stream_step (execToAut (listToExec mergeAut))"

definition mergeSem::"('a::countable list list stream \<rightarrow> 'a list stream) set" where
"mergeSem = sem stream_step (execToAut (listToExec mergeAut))"

definition outconv::"('cs::{echan,countable} tstimed\<times>msg) list stream \<rightarrow> ('cs\<times> msg) event stream" where
"outconv = emap (\<lambda>(c,e). (tstimedToOrigin c,e)) oo (sListToEvent)"

lemma m2eventinv[simp]:"m2event \<circ> (Timed \<circ> TLive) = id"
  by(rule fun_eqI,simp)

lemma helper:"sValues\<cdot>s \<subseteq> range (Timed o TLive) \<Longrightarrow> smap (Timed \<circ> TLive \<circ> m2event)\<cdot>s = s"
  by(induction s,auto)

lemma helper2:"sValues\<cdot>s \<subseteq> {Tick} \<union> (EventMsg ` S) \<Longrightarrow> eValues\<cdot>s \<subseteq> S"
  by(induction s,auto)

lemma inconv_well[simp]:fixes sb::"'cs::{echan} sb"
  shows "lsb_well (\<lambda>c::'cs tstimed. smap (Timed o TFin)\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb \<^enum> (tstimedToOrigin c)))))"
  apply(cases "chDom TYPE('cs) = {}",simp)
  apply(rule lsbwellI)  
  apply(case_tac c;simp)
  apply(subst ctype_tfinchan)
  apply(case_tac "Rep x",simp)
   apply (meson ctype_empty_iff ctype_nempty dom2ctypenempty)
  apply(simp add: smap_sValues)
proof(rule image_mono)
  fix c::"'cs tstimed" and x::'cs
  assume a1:"chDom TYPE('cs) \<noteq> {}"
  assume a2:"c = TSTIMED x"
  then have "cTime (Rep x) = TTLive"
    by (simp add: a1)
  then have h: "sValues\<cdot>(sb  \<^enum>  x) \<subseteq> (Timed o TLive) `({Tick} \<union> (EventMsg ` (cMsg (Rep x))) )"
    using sbgetch_ctypewell a1 ctype_echan_def by blast
  have "\<exists>s. sb \<^enum> x = smap (Timed o TLive)\<cdot>s"
    apply(rule_tac x="smap m2event\<cdot>(sb \<^enum> x)" in exI)
    apply(simp add: smapsmap2smap)
    apply(subst helper,simp_all)
    using h by auto
  then obtain s where s_def:"sb \<^enum> x = smap (Timed o TLive)\<cdot>s"
    by blast
  have "eValues\<cdot>s \<subseteq> cMsg (Rep x)"
    apply(rule helper2)
    using h s_def
    by(subst subsetI,simp_all add: smap_sValues image_subset_iff image_iff)
  then show "sValues\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb  \<^enum>  x))) \<subseteq> {ls::msg list. set ls \<subseteq> cMsg (Rep x)}"
    apply(simp add: s_def smapsmap2smap)
    using  stimedtolist_well by blast
qed

lift_definition inconv::"'cs::{echan} sb \<rightarrow> 'cs tstimed sb"is
"\<lambda> sb. Abs_lsb(\<lambda>c. smap (Timed o TFin)\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb \<^enum> (tstimedToOrigin c)))))"
  apply(intro cont2cont)
  by(simp)

definition inconvOutSBE :: "('cs::echan) sb \<Rightarrow> ('cs tstimed)\<^sup>\<surd>" where
"inconvOutSBE \<equiv> \<lambda>sb. Abs_sbElem (if chDomEmpty TYPE('cs) then None else Some (\<lambda>c. (Timed (TFin (s2list (smap (inv EventMsg)\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  tstimedToOrigin c))))))))"

definition bMerge::"('cs::{echan,enum} sb \<rightarrow> ('cs) msgWithChan event stream) set" where
"bMerge = (\<lambda>f. emap Abs_msgWithChan oo outconv oo f oo convertSem oo inconv) ` (mergeSem)"

definition listoutconv::"(('out::{echan,finite} \<times> msg) event stream) \<Rightarrow> ('out\<^sup>\<Omega>)" where
"listoutconv ls =  uSplit\<cdot>(emap Abs_msgWithChan\<cdot>(ls))"

(*
lemma [ccode]:"convertSem\<cdot>(\<bottom>::'cs::{somechan,enum,tschan}\<^sup>\<Omega>) = \<epsilon>"
  by(simp add: convertSem_def,subst convertAut_def,simp add: bot_nc_stream_def stream_bottom_nc_def)

lemma [ccode]:"convertSem\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb::'cs::{somechan,enum,tschan}\<^sup>\<Omega>) =
\<up>  (map (\<lambda>c. map (\<lambda>e. (c,e)) (m2list (sbegetch c sbe))) Enum.enum) \<Zcat> convertSem\<cdot>sb"
  by(simp add: convertSem_def convtrans_def convertAut_def)
 *)

typedef 'cs::"{countable,chan}" eventwellstream ="{s::('cs\<times>msg) event stream | s. \<forall>e\<in>eValues\<cdot>s. well e}"
  apply auto[1]
  by(rule_tac x=\<epsilon> in exI,simp)
  
setup_lifting type_definition_eventwellstream

typedef 'cs::"{countable,chan}" listwellstream ="{s::('cs\<times>msg) list stream | s. \<forall>e\<in>\<Union>(set ` sValues\<cdot>s). well e}"
  apply auto[1]
  by(rule_tac x=\<epsilon> in exI,simp)
  
setup_lifting type_definition_listwellstream


fun wellOrdered :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"wellOrdered [] ys = True" |
"wellOrdered xs [] = False" |
"wellOrdered (x#xs) (y#ys) = (if x = y then (x \<in> set ys \<longrightarrow> x \<in> set xs) \<and> wellOrdered xs ys else (wellOrdered (x#xs) ys) \<and> (y \<notin> set xs))"

primrec multilist_distinct :: "'a list list \<Rightarrow> bool" where
"multilist_distinct [] \<longleftrightarrow> True" |
"multilist_distinct (x#xs) \<longleftrightarrow> (\<forall>y \<in> set xs. set x \<inter> set y = {}) \<and> multilist_distinct xs"



lemma tstimedwell[simp]:"well (TSTIMED a, b) \<Longrightarrow> well (a,b)"
  apply(simp add: well_def)
  by(cases "Rep a \<in> chDom TYPE('a)",simp_all)


lemma smap_m2event_timedtlive_inv_eq:
  assumes "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)"
  shows "smap m2event\<cdot>s = smap (inv TLive \<circ> inv Timed)\<cdot>s"
  using assms
  by (induction s, auto)

lemma smap_timedtlive_inv_rule:
  assumes "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)" 
    and "smap (inv TLive \<circ> inv Timed)\<cdot>s = x"
  shows "s = smap (Timed \<circ> TLive)\<cdot>x"
  by (metis assms helper smap_m2event_timedtlive_inv_eq smapsmap2smap)

lemma smap_timedtlive_h:
  "smap (Timed \<circ> TLive)\<cdot>s \<Zcat> \<up>(Timed (TLive a)) \<Zcat> smap (Timed \<circ> TLive)\<cdot>s2 = smap (Timed \<circ> TLive)\<cdot>(s \<Zcat> \<up>a \<Zcat> s2)"
  by (simp add: smap_split)

lemma tlen_timedtlive_zero_gt:
  assumes "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)"
    and "0 < #\<^sub>\<surd>s"
  shows "(Timed (TLive Tick)) \<in> sValues\<cdot>s"
proof (rule ccontr)
  assume "Timed (TLive Tick) \<notin> sValues\<cdot>s"
  hence "Tick \<notin> (inv TLive \<circ> inv Timed) ` sValues\<cdot>s"
    using assms(1) by auto
  hence "#\<^sub>\<surd>(smap (inv TLive \<circ> inv Timed)\<cdot>s) = 0"
    by (simp add: smap_sValues)
  hence "#\<^sub>\<surd>s = 0"
    apply (subst (asm) smap_tlen)
    using \<open>#\<^sub>\<surd> (smap (inv TLive \<circ> inv Timed)\<cdot>(s::M stream)) = (0::lnat)\<close> assms(1) assms(2) inj_def by auto
  thus False
    using assms(2) by auto
qed

lemma tlen_timedtlive_zero:
  assumes "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)"
    and "#\<^sub>\<surd>s = 0"
  shows "(Timed (TLive Tick)) \<notin> sValues\<cdot>s"
  using assms
  apply(induction s,simp_all)
  apply(rule adm_imp,simp_all)+
  apply(rule adm_upward)
  apply (metis Fin_0 gr_implies_not0 leI lnat_well_h1 mono_tlen order_antisym_conv)
  apply(case_tac a,simp_all) 
  apply blast
  apply(case_tac x2,simp_all) apply blast+
  apply(case_tac x3,simp_all)
  apply(simp add: lnat_suc_plus) 
  by blast
  
lemma ttlive_tick_in_tlen:
  assumes "Timed (TLive Tick) \<in> sValues\<cdot>s"
    and "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)"
  shows "#\<^sub>\<surd>s > 0"
  by (metis assms(1) assms(2) bot_is_0 lnless_def minimal tlen_timedtlive_zero)

lemma ttlive_stream_set_in:
  assumes "sValues\<cdot>s \<subseteq> range (Timed \<circ> TLive)"
    and "x \<in> (inv TLive \<circ> inv Timed) ` sValues\<cdot>s"
  shows "(Timed (TLive x)) \<in> sValues\<cdot>s"
  using assms(1) assms(2) by auto

lemma ttlive_stream_set_nin:
  assumes "x \<notin> (inv TLive \<circ> inv Timed) ` sValues\<cdot>s"
  shows "(Timed (TLive x)) \<notin> sValues\<cdot>s"
  using assms image_iff by fastforce

lemma tlive_cases:
  "\<And>x P. \<lbrakk>x \<in> range (Timed \<circ> TLive); x = Timed (TLive Tick) \<Longrightarrow> P; \<And>e. x = Timed (TLive (EventMsg e)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by fastforce

lemma tlive_scases:
  "\<And>x P. \<lbrakk>sValues\<cdot>x \<subseteq> range (Timed \<circ> TLive); x = \<epsilon> \<Longrightarrow> P; \<And>a s. x = \<up>(Timed (TLive a)) \<Zcat> s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (metis (no_types, opaque_lifting) Un_iff in_mono insert_iff sValues2un surj_scons tlive_cases)

lemma sbvalues_m2list_cmsg:
  assumes "(c,m) \<in> sbValues\<cdot>(sb::'cs::chan\<^sup>\<Omega>)"
  shows "set (m2list m) \<subseteq> cMsg (Rep c)"
proof-
  have m_in_ctypec: "m \<in> ctype (Rep c)"
    by (metis assms fst_conv sbvalues_ctypewell2(1) snd_conv)
  hence cmsg_nempty: "cMsg (Rep c) \<noteq> {}"
    using ctype_empty_iff by blast
  thus ?thesis
    apply (insert m_in_ctypec)
    apply (simp add: ctype_def cmsg_nempty)
    apply (cases m; simp)
    apply (cases "cTime (Rep c)"; simp; blast)
    apply (cases "cTime (Rep c)"; simp)
    apply (case_tac x2; simp)
    apply (case_tac x1; simp)
    by fastforce+
qed

lemma timed_tlive_event_smap_id:
  "smap (inv EventMsg)\<cdot>
          (smap (inv TLive \<circ> inv Timed)\<cdot>
           (smap (Timed \<circ> TLive)\<cdot>
            (smap EventMsg\<cdot>s))) = s"
  apply (subst smap_m2event_timedtlive_inv_eq [symmetric])
  using smap_sValues_range apply blast
  apply (subst (2) smapsmap2smap, simp)
  by (subst smapsmap2smap, simp)

lemma pairsnd_emap:
  "emap snd\<cdot>(emap (Pair c)\<cdot>s) = s"
  apply (induction s)
  apply simp_all
  by (case_tac a; simp)


lemma eshdts_svalues_cmsg: "\<And>(c::'a::{echan,one_chan} tstimed).
       sValues\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  tstimedToOrigin c)))
       \<subseteq> cMsg (Rep c)"
proof (rule subsetI)
  fix x c
  assume "x \<in> sValues\<cdot>
            (eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  tstimedToOrigin c)))"
  hence event_x_svalues: "EventMsg x \<in> sValues\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  tstimedToOrigin c))"
    by (metis image_subset_iff eshdts_svalues smap_sValues)
  have "sValues\<cdot>(sb  \<^enum>  tstimedToOrigin c) \<subseteq> range (Timed \<circ> TLive)"
    by (metis echan_svalues empty_iff sValues_notempty sbgetch_empty subsetI)
  hence m_x_in_svalues: "(Timed (TLive (EventMsg x))) \<in> sValues\<cdot>(sb  \<^enum>  tstimedToOrigin c)"
    apply (insert event_x_svalues)
    apply (subst (asm) smap_sValues)
    apply (simp add: image_iff)
    using \<open>sValues\<cdot> ((sb::'a\<^sup>\<Omega>) \<^enum> tstimedToOrigin (c::'a tstimed)) \<subseteq> range (Timed \<circ> TLive)\<close> by auto
  have chdom_nempty: "\<not> chDomEmpty TYPE('a tstimed)"
    by (metis \<open>Timed (TLive (EventMsg (x::msg))) \<in> sValues\<cdot> ((sb::'a\<^sup>\<Omega>) \<^enum> tstimedToOrigin (c::'a tstimed))\<close> chandomchdomeq chdom_empty equals0D sValues_notempty sbgetch_empty2)
  obtain originC where originC_def: "c = TSTIMED originC"
    by (meson tstimedToOrigin.elims)
  have "sValues\<cdot>(sb \<^enum> originC) \<subseteq> ctype (Rep originC)"
    using sbgetch_ctypewell by blast
  hence x_in_ctype_originc: "(Timed (TLive (EventMsg x))) \<in> ctype (Rep originC)"
    by (metis m_x_in_svalues originC_def subsetD tstimedToOrigin.simps)
  thus "x \<in> cMsg (Rep c)"
    apply (insert x_in_ctype_originc)
    apply (subst rep_tstimed_def2)
    apply fastforce
    apply (simp add: originC_def)
    apply (subst (asm) ctype_echan_def)
    apply (metis chandomchdomeq chdom_empty chdom_nempty)
    by fastforce
qed

lemma sbhdts_getch:
   "sbHdTs\<cdot>sb \<^enum> c = smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c))))"
  apply (simp add: sbHdTs.rep_eq sbgetch_insert2)
  apply (subst Abs_lsb_inverse, simp_all)
  apply (rule lsbwellI)
  by (metis (no_types, opaque_lifting) sbgetch_ctypewell sbhdts_svalues order_trans sbgetch_insert2)

lemma sbhdts_bot[simp]:
  "sbHdTs\<cdot>\<bottom> = \<bottom>"
  apply (rule sb_eqI)
  by (simp add: sbhdts_getch)

lemma sbhdts_getch_len:
  assumes "(Timed (TLive Tick)) \<in> sValues\<cdot>(sb \<^enum> c)"
  shows "#(sbHdTs\<cdot>sb \<^enum> c) < \<infinity>"
  apply (simp add: sbHdTs.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  apply simp
  using lsb_well_def sbgetch_ctypewell sbhdts_svalues apply blast
  apply simp
  apply (rule eshdts_len)
  by (metis assms smap_sValues ttlive_stream_set_nin)

lemma sbhdts_sbgetch_len2:
  assumes "#\<^sub>\<surd>(sb::('cs::echan)\<^sup>\<Omega>) > 0"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "#(sbHdTs\<cdot>sb \<^enum> c) < \<infinity>"
proof-
  have h1:"#\<^sub>\<surd>(sb \<^enum> c) > 0"
    by (metis (mono_tags, lifting) assms(1) assms(2) dual_order.strict_trans2 lnle_def lnless_def sbtlen_min_len)
  have h2:"sValues\<cdot>(sb \<^enum> c) \<subseteq> range (Timed \<circ> TLive)"
    by (meson assms(2) chdom_in echan_svalues)
  have "Tick \<in> sValues\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c))"
    by (metis (no_types, lifting) h1 h2 inj_timed inj_tlive 
        sValues_smapl1 smap_timedtlive_inv_rule smapsmap2smap 
        tlen_timedtlive_zero_gt)
  hence "(Timed (TLive Tick)) \<in> sValues\<cdot>(sb \<^enum> c)"
    by (metis (mono_tags, opaque_lifting) \<open>sValues\<cdot>((sb::'cs\<^sup>\<Omega>) \<^enum> (c::'cs)) \<subseteq> range (Timed \<circ> TLive)\<close> comp_apply imageI smap_sValues smap_timedtlive_inv_rule)
  thus ?thesis
    using sbhdts_getch_len by blast
qed

lemma sbhdts_sbgetch_m2event: "smap m2event\<cdot>
         ((sbHdTs\<cdot>sb  \<^enum> c)) = smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c)))"
  apply (simp add: sbHdTs.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  apply simp
  using lsb_well_def sbgetch_ctypewell sbhdts_svalues apply blast
proof-
  obtain s where s_def: "smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c) = s"
    by blast
  have "smap m2event\<cdot>
    (smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(s)))) =
    smap EventMsg\<cdot>(eshdts\<cdot>(s))"
    apply (induction s)
    apply (rule adm_eq)
    apply (intro cont2cont)+
    apply simp
    apply (case_tac a; simp)
    by (simp add: eshdts_event)
  thus "smap m2event\<cdot>
    (smap (Timed \<circ> TLive)\<cdot>(smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c))))) =
    smap EventMsg\<cdot>(eshdts\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c)))"
    using s_def by blast
qed

lemma sbhdts_split_eq:
  assumes "#\<^sub>\<surd>sb > 0"
  shows "sbHdTs\<cdot>(sbHdTs\<cdot>sb \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sb2) = sbHdTs\<cdot>sb"
  apply (rule sb_eqI)
  apply (simp add: sbhdts_getch)
  apply (subst (2) sbgetch_insert)
  apply (subst ticksb_insert, blast)
  apply simp
  apply (simp add: smap_split)
  apply (subst eshdts_split_eq)
  apply simp
  apply (rule eshdts_len)
  apply (simp add: smap_sValues image_iff)
  apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
  apply (rule tlen_timedtlive_zero_gt)
  apply (meson echan_svalues)
  apply (metis assms empty_iff less_le_trans sbtlen_min_len)
  apply (metis Tick_notin_image_Event echan_svalues sbhdts_getch sbhdts_sbgetch_m2event smap_m2event_timedtlive_inv_eq smap_sValues)
  apply (subst smap_m2event_timedtlive_inv_eq [symmetric])
  apply (meson smap_sValues_range)
  apply (subst(4) smapsmap2smap)
  apply simp
  apply (subst (3) smapsmap2smap)
  by simp

lemma sbhdts_getch_tlen:
  "#\<^sub>\<surd>(sbHdTs\<cdot>(sb::'cs::echan\<^sup>\<Omega>) \<^enum> c) = 0"
  apply (simp add: sbhdts_getch)
  apply (subst smap_tlen)
  apply(case_tac x;simp)
  by (metis Tick_notin_image_Event smap_sValues tlentosvalues)

lemma sbhdts_sbgetch_tlengr_len:
  assumes "#\<^sub>\<surd>(sb \<^enum> c) > 0"
  shows "#(sbHdTs\<cdot>sb \<^enum> c) < \<infinity>"
  apply (simp add: sbhdts_getch)
  apply (rule eshdts_len)
  by (metis assms echan_svalues lnless_def sbgetch_empty smap_sValues stream_tlen_eps tlen_timedtlive_zero_gt ttlive_stream_set_nin)


lemma sbrtts_sbgetch:
  "sbRtTs\<cdot>(sb::'cs::echan\<^sup>\<Omega>) \<^enum> c = smap (Timed \<circ> TLive)\<cdot>(tsrt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c)))"
  apply (simp add: sbgetch_insert2 sbRtTs.rep_eq)
  apply (subst Abs_lsb_inverse, simp_all)
  apply (rule lsbwellI)
  by (metis (no_types, opaque_lifting) order_trans sbgetch_ctypewell sbgetch_insert2 sbrtts_svalues)

lemma sbrtts_sbrt_leq:
  "#(sbRtTs\<cdot>(sb::'cs::echan\<^sup>\<Omega>)) \<le> #(sbRt\<cdot>sb)"
  apply (subgoal_tac "\<And>c. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> #(sbRtTs\<cdot>sb \<^enum> c) \<le> #(sbRt\<cdot>sb \<^enum> c)")
  apply (metis chdomnotempty_rangeeq order_refl repinrange sblen_empty sblengeq sblenleq)
  apply (simp add: sbrtts_sbgetch)
  apply (simp add: sbdrop_insert)
  apply (subst (2) sbgetch_insert2)
  apply simp
  apply (subgoal_tac "#(tsrt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c))) \<le> #(srt\<cdot>((smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c))))")
  apply (metis sdrop_0 sdrop_back_rt sdrop_smap slen_smap)
  using tsrt_srt_len by blast

lemma sbrtts_split_eq:
  assumes "#\<^sub>\<surd>sb > 0"
    and "\<And>c::'cs::echan. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> #\<^sub>\<surd>(sb1 \<^enum> c) = 0"
    and "\<And>c::'cs. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> #(sb1  \<^enum>  c) < \<infinity>"
  shows "sbRtTs\<cdot>(sb1 \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb) = sbRtTs\<cdot>sb"
  apply (rule sb_eqI)
  apply (simp add: sbrtts_sbgetch)
  apply (subst (2) sbgetch_insert2)
  apply (subst ticksb_insert)
  apply blast
  apply (simp add: smap_split)
  apply (subst tsrt_split_eq)
  apply (simp add: assms)
  apply (metis assms(2) echan_svalues smap_sValues tlen_timedtlive_zero ttlive_stream_set_in)
  apply (subst smap_m2event_timedtlive_inv_eq [symmetric])
  using smap_sValues_range apply blast
  by (simp add: smapsmap2smap)


lift_definition sbDropCh :: "nat \<Rightarrow> 'cs::chan \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"\<lambda>n x sb. Abs_lsb (\<lambda>c::'cs. (if c = x then sdrop n\<cdot>(sb \<^enum> c) else sb \<^enum> c))"
  apply (intro cont2cont)
  apply (rule lsbwellI)
  apply simp
  apply (rule impI)
  by (meson sbgetch_ctypewell sdrop_sValues subset_trans)

abbreviation sbRtCh :: "'cs::chan \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"  where 
"sbRtCh \<equiv> sbDropCh 1"

lemma sbdropch_cheq_getch:
  "(sbDropCh n c\<cdot>sb) \<^enum> c = sdrop n\<cdot>(sb \<^enum> c)"
  apply (simp add: sbDropCh.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse, simp_all)
  apply (rule lsbwellI, simp)
  apply (rule impI)
  by (meson sbgetch_ctypewell sdrop_sValues subset_trans)

lemma sbdropch_chneq_getch:
  assumes "x \<noteq> c"
  shows "(sbDropCh n x\<cdot>sb) \<^enum> c = (sb \<^enum> c)"
  apply (simp add: sbDropCh.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  apply simp
  apply (rule lsbwellI, simp)
  apply (rule impI)
  apply (meson sbgetch_ctypewell sdrop_sValues subset_trans)
  using assms by fastforce

lemma sbdropch_tlen_eq:
  assumes "#\<^sub>\<surd>(sdrop n\<cdot>(sb \<^enum> c)) = #\<^sub>\<surd>(sb \<^enum> c)"
  shows "#\<^sub>\<surd>(sbDropCh n c\<cdot>(sb::'cs::tchan\<^sup>\<Omega>)) = #\<^sub>\<surd>sb"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  then show ?thesis
    by simp
next
  case False
  obtain cmin where cmin_def: "#\<^sub>\<surd>(sbDropCh n c\<cdot>sb) = #\<^sub>\<surd>(sbDropCh n c\<cdot>sb \<^enum> cmin)"
    using False sbtlen2stlen by blast
  have "\<And>c1. #\<^sub>\<surd>(sbDropCh n c\<cdot>sb \<^enum> c1) = #\<^sub>\<surd>(sb \<^enum> c1)"
    by (metis assms sbdropch_cheq_getch sbdropch_chneq_getch)
  then show ?thesis 
    by (metis False cmin_def sbtlen2stlen_h sbtlen_min_len)
qed


lemma sb_step:
  assumes "\<And>c. Rep c \<in> chDom TYPE('a::echan) \<Longrightarrow> (Timed (TLive Tick)) \<in> sValues\<cdot>((sb::'a\<^sup>\<Omega>) \<^enum> c)"
  shows "sb = sbHdTs\<cdot>sb \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb"
  apply (rule sb_eqI)
  apply simp
  apply (subst (2 3 4) sbgetch_insert2)                  
  apply (simp add: sbHdTs.rep_eq sbRtTs.rep_eq)
  apply (subst Abs_lsb_inverse)
  apply (metis (no_types, lifting) mem_Collect_eq lsb_well_def sbgetch_ctypewell sbhdts_svalues subset_trans)
  apply (subst ticksb_insert)                                                 
  apply blast   
  apply (subst Abs_lsb_inverse)                                   
  apply (metis (mono_tags, lifting) mem_Collect_eq lsb_well_def sbgetch_ctypewell sbrtts_svalues subset_trans)
  apply (simp add: smap_timedtlive_h)
  apply (rule_tac s="sb \<^enum> c" in smap_timedtlive_inv_rule)       
  apply (meson echan_svalues)
  apply (subst s_split)                                               
  apply (metis (no_types, lifting) assms echan_svalues image_iff m2event.simps(1) smap_m2event_timedtlive_inv_eq smap_sValues)
  by (metis echan_svalues smap_m2event_timedtlive_inv_eq)       

lemma sb_step_tlen_gr0:
  assumes "\<And>c::'cs::echan. Rep c \<in> chDom TYPE('cs) \<Longrightarrow>  #(sb1 \<^enum> c) < \<infinity>"
  shows "#\<^sub>\<surd>(sb1 \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sb2) > 0"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  then show ?thesis
    by simp
next
  case False
  then obtain c where c_def: "#\<^sub>\<surd>(sb1 \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sb2) = #\<^sub>\<surd>(sb1 \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sb2 \<^enum> c)"
    using sbtlen2stlen by blast
  then show ?thesis
    apply (simp add: c_def)
    apply (subst(2) sbgetch_insert2)
    apply (subst ticksb_insert)
    apply (simp add: False)
    apply (subst tlen_wellformed_sconc)
    apply (simp add: wellformed_stream_def)
    apply (rule impI)
    using False assms chdom_in lnless_def apply blast
    apply (subst tlen_wellformed_sconc)
    apply (simp_all add: wellformed_stream_def)
    by (metis Fin_02bot add.left_commute less_linear lnat.con_rews lnat_suc_plus lnat_well_h1 lnzero_def not_less_zero)
qed


lemma listmerge_rempty[simp]: "listmerge xs [] = [xs]"
  by (induction xs, simp_all)

lemma listmerge_nempty[simp]:"listmerge ls1 ls2 \<noteq> []"
  apply(induction ls1,simp)
  by(induction ls2,simp_all)

lemma listmerge_set:
  assumes "xs \<in> set (listmerge as bs)"
  shows "set xs = set as \<union> set bs"
  using assms
  apply (induction xs arbitrary: as bs)
  by (case_tac as;case_tac bs; fastforce)+

lemma listmerge_union_set: "\<Union>(set ` set (listmerge xs ys)) = set xs \<union> set ys"
  by (simp add: listmerge_set)

lemma listmerge_nth_set: 
  assumes "n < length (listmerge xs ys)"  
  shows "set (listmerge xs ys ! n) = set xs \<union> set ys"
  by (metis assms listmerge_set nth_mem)

lemma listmerge_nth_length:
  assumes "n < length (listmerge xs ys)"  
  shows "length (listmerge xs ys ! n) = length xs + length ys"
  using assms
  apply (induction xs ys arbitrary: n rule: listmerge.induct)
  by (simp_all add: nth_append)


lemma tsmerge_nempty[simp]: "tsmerge ls \<noteq> []"
  by (induction ls rule: tsmerge.induct, simp_all)

lemma tsmerge_set:
  assumes "xs \<in> set (tsmerge ls)"
  shows "set xs = \<Union>(set ` set ls)"
  using assms
  apply (induction ls arbitrary: xs rule: tsmerge.induct, simp_all)
  by (metis listmerge_set sup_assoc)

lemma tsmerge_union_set: "\<Union>(set ` set (tsmerge ls)) = \<Union>(set ` set ls)"
  by (simp add: tsmerge_set)

lemma tsmerge_nth_len:
  assumes "n < length (tsmerge ls)"
  shows "length (tsmerge ls ! n) = sum_list (map length ls)"
  using assms
proof (induction ls arbitrary: n rule: tsmerge.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 a)
  then show ?case 
    by simp
next
  case (3 a b ls)
  hence "n < length
     (concat (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b)))"
    by simp
  then obtain l k where l_in_listmergeset: "l \<in> set (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b))"
    and l_def: "concat (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b)) ! n = l ! k" and "k \<le> n"
      and k_l_length_le: "k < length l"
    using concat_nth
    by blast
  then obtain lrep where lrep_def: "l = tsmerge (lrep # ls)" and lrep_set_listmerge: "lrep \<in> set (listmerge a b)"
    by auto
  then show ?case
    apply (simp add: l_def)
    by (metis "3.IH" add.assoc concat.simps(2) in_set_conv_nth k_l_length_le length_append length_concat listmerge_nth_length)
qed


lemma wellOrderedI1:
  assumes "x = y"
    and "(x \<in> set ys \<longrightarrow> x \<in> set xs)"
    and "wellOrdered xs ys"
  shows "wellOrdered (x#xs) (y#ys)"
  using assms by auto

lemma wellOrderedI2:
  assumes "x \<noteq> y"
    and "y \<notin> set xs"
    and "wellOrdered (x#xs) ys"
  shows "wellOrdered (x#xs) (y#ys)"
  using assms by auto

lemma wellordered_refl: "wellOrdered xs xs"
  by (induction xs, simp_all)

lemma wellordered_set:
  assumes "wellOrdered (x#xs) ys"
  shows "x \<in> set ys"
  using assms
  apply (induction ys arbitrary: x xs, simp)
  by (metis list.set_intros(1) list.set_intros(2) wellOrdered.simps(3))

lemma wellordered_subset:
  assumes "wellOrdered xs ys"
  shows "set xs \<subseteq> set ys"
  using assms
  apply (induction xs ys rule: wellOrdered.induct, simp_all)
  by blast

lemma wellordered_nth_ex1:
  assumes "wellOrdered (x#xs) ys"
  shows "\<exists>n < length ys. ys ! n = x \<and> (x \<in> set (drop (Suc n) ys) \<longrightarrow> x \<in> set xs) \<and> wellOrdered xs (drop (Suc n) ys) \<and> (\<forall>y \<in> set (x#xs). y \<notin> set (take n ys))"
  using assms
  apply (induction ys arbitrary: x xs)
  apply simp_all
  apply (case_tac "a = x"; simp)
  apply (rule_tac x="0" in exI)
  apply simp
  apply (subgoal_tac "\<exists>n < length ys. ys ! n = x \<and> (x \<in> set (drop (Suc n) ys) \<longrightarrow> (x \<in> set xs)) \<and> wellOrdered xs (drop (Suc n) ys) \<and> (\<forall>y \<in> set (x#xs). y \<notin> set (take n ys))")
  apply (metis Suc_less_eq nth_Cons_Suc set_ConsD take_Suc_Cons)
  by (simp)

lemma wellordered_nth_ex2:
  assumes "wellOrdered xs ys"
  shows "\<forall>x \<in> set xs. \<exists>n < length ys. ys ! n = x"
  by (meson assms from_set_to_nth subsetD wellordered_subset)
    
lemma drop_wellordered:
  assumes "wellOrdered xs (drop n ys)"
    and "set (take n ys) \<inter> set xs = {}"
  shows "wellOrdered xs ys"
  using assms
  apply (induction xs ys arbitrary: n rule: wellOrdered.induct)
  apply simp_all
  by (case_tac n; fastforce)

lemma wellordered_filter:
  assumes "wellOrdered xs ys"
    and "\<forall>x \<in> set xs. P x"
    and "\<forall>y \<in> set ys. y \<notin> set xs \<longrightarrow> \<not>P y"
  shows "filter P ys = xs"
  using assms
  apply (induction ys arbitrary: xs)
  using wellOrdered.elims(2) apply fastforce
  apply simp
  apply (erule wellOrdered.elims(2))
  apply simp
  by (metis insert_iff list.inject list.set(2))

lemma wellordered_appendR:
  assumes "wellOrdered xs zs"
    and "\<forall>y \<in> set xs. y \<notin> set ys"
  shows "wellOrdered xs (ys @ zs)"
  using assms
  apply (induction ys arbitrary: xs zs, simp_all)
  apply (case_tac xsa; simp)
  by blast

lemma wellordered_appendL:
  assumes "wellOrdered xs ys"
    and "\<forall>x \<in> set xs. x \<notin> set zs"
  shows "wellOrdered xs (ys @ zs)"
  using assms
  apply (induction xs ys arbitrary: zs rule: wellOrdered.induct, simp_all)
  by fastforce

lemma wellordered_step:
  assumes "wellOrdered xs (drop (Suc n) ys)"
    and "\<forall>y \<in> set (x#xs). y \<notin> set (take n ys)"
    and "(x \<in> set (drop (Suc n) ys) \<Longrightarrow> x \<in> set xs)"
    and "ys ! n = x"
    and "n < length ys"
  shows "wellOrdered (x#xs) ys"
  using assms
  apply (subst(3) append_take_nth_drop_id [where n="n" ,symmetric])
  apply simp
  apply (rule wellordered_appendR)
  apply (metis Cons_eq_appendI self_append_conv2 wellOrderedI1)
  apply (rule ballI)
  by blast

lemma wellordered_trans:
  assumes "wellOrdered xs ys"
    and "wellOrdered ys zs"
  shows "wellOrdered xs zs"
  using assms
proof (induction xs ys arbitrary: zs rule: wellOrdered.induct)
  case (1 ys)
  then show ?case
    by simp
next
  case (2 v va)
  thus ?case
    using wellOrdered.elims(2) by fastforce
next
  case (3 x xs y ys)
  then show ?case
  proof (cases "x = y")
    case True
    hence wellordered_xs_ys: "wellOrdered xs ys" and x_set_iff: "(x \<in> set ys \<longrightarrow> x \<in> set xs)"
      using "3.prems"(1) by force+
    obtain i where "i < length zs" and "zs ! i = y" and "(y \<in> set (drop (Suc i) zs) \<longrightarrow> y \<in> set ys)"
      and "wellOrdered ys (drop (Suc i) zs)" and "\<forall>x \<in> set (y#ys). x \<notin> set (take i zs)"
      by (metis "3.prems"(2) wellordered_nth_ex1)
    hence "x = y \<Longrightarrow> wellOrdered xs (drop (Suc i) zs) \<Longrightarrow> (x \<in> set (drop (Suc i) zs) \<longrightarrow> x \<in> set xs)  \<Longrightarrow> wellOrdered (x#xs) zs"
      apply (subst wellordered_step [where n="i"], simp_all)
      by (metis subsetD wellordered_subset wellordered_xs_ys)
    then show ?thesis
      using "3.prems"(2)
      apply (case_tac zs)
      apply simp
      apply simp
      apply (case_tac "y = a")
      apply simp
      apply (simp add: True)
      apply (rule conjI)
      using True x_set_iff apply force
      apply (rule "3.IH"(1))
      using True apply blast
      using wellordered_xs_ys apply blast
      using "3.IH"(1) True apply blast
      apply (simp add: True)
      apply (erule conjE)
      by (metis "3.IH"(1) True \<open>(y::'a) \<in> set (drop (Suc (i::nat)) (zs::'a list)) \<longrightarrow> y \<in> set (ys::'a list)\<close> \<open>wellOrdered (ys::'a list) (drop (Suc (i::nat)) (zs::'a list))\<close> drop_Suc_Cons wellordered_xs_ys x_set_iff)
  next
    case False
    hence x_xs_ys_wellordered: "wellOrdered (x#xs) ys" and y_notin_xs: "(y \<notin> set xs)"
      using "3.prems"(1) False by fastforce+
    then obtain k where "k < length ys" and "ys ! k = x" and "(x \<in> set (drop (Suc k) ys) \<longrightarrow> x \<in> set xs)"
      and "wellOrdered xs (drop (Suc k) ys)" and "\<forall>x \<in> set (x#xs). x \<notin> set (take k ys)"
      by (metis wellordered_nth_ex1)
    then obtain i where "i < length zs" and "zs ! i = y" and "(y \<in> set (drop (Suc i) zs) \<longrightarrow> y \<in> set ys)"
      and "wellOrdered ys (drop (Suc i) zs)" and "\<forall>x \<in> set (y#ys). x \<notin> set (take i zs)"
      by (metis "3.prems"(2) wellordered_nth_ex1)
    hence "\<forall>x \<in> set(x#xs). x \<notin> set (take i zs)"
      by (metis "3.prems"(1) nth_mem wellordered_nth_ex2)
    have "wellOrdered (x#xs) (drop (Suc i) zs)"
      apply (rule "3.IH"(2))
      apply (simp add: False)
      apply (simp add: x_xs_ys_wellordered)
      by (simp add: \<open>wellOrdered (ys::'a list) (drop (Suc (i::nat)) (zs::'a list))\<close>)
    then show ?thesis
      apply (rule drop_wellordered)
      apply (subgoal_tac "take (Suc i) zs = take i zs @ [y]")
      apply (simp add: Int_def)
      apply (rule allI)
      apply (meson "3.prems"(1) False \<open>\<forall>x::'a\<in>set ((x::'a) # (xs::'a list)). x \<notin> set (take (i::nat) (zs::'a list))\<close> \<open>\<forall>x::'a\<in>set ((y::'a) # (ys::'a list)). x \<notin> set (take (i::nat) (zs::'a list))\<close> set_subset_Cons subsetD wellordered_set y_notin_xs)
      by (simp add: \<open>(i::nat) < length (zs::'a list)\<close> \<open>(zs::'a list) ! (i::nat) = (y::'a)\<close> take_Suc_conv_app_nth)
  qed
qed

lemma listmerge_lwellOrdered:
  assumes "n < length (listmerge xs ys)"
    and "set xs \<inter> set ys = {}"
  shows "wellOrdered xs (listmerge xs ys ! n)"
  using assms
  apply (induction xs ys arbitrary: n rule: listmerge.induct)
  apply simp
  apply simp
  apply (simp add: wellordered_refl)
  apply simp
  apply (case_tac "n < length (listmerge as (b # bs))")
  apply (simp add: nth_append)+
  apply (rule impI)
  apply (metis UnE listmerge_nth_set set_ConsD)
  apply (simp add: nth_append)
  apply (rule impI)
  by simp

lemma listmerge_rwellOrdered:
  assumes "n < length (listmerge xs ys)"
    and "set xs \<inter> set ys = {}"
  shows "wellOrdered ys (listmerge xs ys ! n)"
  using assms
  apply (induction ys xs arbitrary: n rule: listmerge.induct)
  apply simp
  apply (simp add: wellordered_refl)
  apply simp
  apply (case_tac "n < length (listmerge bs (a#as))")
  apply simp
  apply (simp add: nth_append)+
  apply (rule impI)
  by (simp add: listmerge_nth_set)

lemma tsmerge_nth_wellordered:
  assumes "\<exists>l \<in> set ls. wellOrdered xs l"
    and "n < length (tsmerge ls)"
    and "multilist_distinct ls"
  shows "wellOrdered xs (tsmerge ls ! n)"
  using assms
proof (induction ls arbitrary: n xs rule: tsmerge.induct)
  case 1
  then show ?case
    by simp
next
  case (2 a)
  then show ?case
    using wellordered_refl by auto
next
  case (3 a b ls)
  hence "n < length
     (concat (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b)))"
    by simp
  then obtain l k where l_in_listmergeset: "l \<in> set (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b))"
    and l_def: "concat (map (\<lambda>merged::'a list. tsmerge (merged # ls)) (listmerge a b)) ! n = l ! k" and "k \<le> n"
      and k_l_length_le: "k < length l"
    using concat_nth
    by blast
  then obtain lrep where lrep_def: "l = tsmerge (lrep # ls)" and lrep_set_listmerge: "lrep \<in> set (listmerge a b)"
    by auto
  then have "wellOrdered xs a \<or> wellOrdered xs b \<Longrightarrow> wellOrdered xs lrep"
    apply (cases "wellOrdered xs a"; simp)
    apply (metis (mono_tags, lifting) "3.prems"(3) in_set_conv_nth list.set_intros(1) listmerge_lwellOrdered multilist_distinct.simps(2) wellordered_trans)
    by (metis (mono_tags, lifting) "3.prems"(3) in_set_conv_nth list.set_intros(1) listmerge_rwellOrdered multilist_distinct.simps(2) wellordered_trans)
  then show ?case
    apply (simp add: l_def lrep_def)
    apply (rule "3.IH")
    apply (simp add: lrep_set_listmerge)
    using "3.prems"(1) apply auto[1]
    using k_l_length_le lrep_def apply force
    apply simp
    apply (rule conjI)
    apply (rule ballI)
    apply (subst listmerge_set [where as="a" and bs="b"])
    using lrep_set_listmerge apply force
    apply (metis (no_types, lifting) "3.prems"(3) inf_sup_distrib2 list.set_intros(2) multilist_distinct.simps(2) sup_bot.right_neutral)
    using "3.prems"(3) multilist_distinct.simps(2) by blast
qed


lemma multilist_distinctI:
  assumes "\<forall>i < length ls. \<forall>k < length ls. (k \<noteq> i \<longrightarrow> set (ls ! i) \<inter> set (ls ! k) = {})"
  shows "multilist_distinct ls"
  using assms
  apply (induction ls, simp_all)
  apply (rule conjI)
  apply (metis Suc_less_eq in_set_conv_nth nat.distinct(1) nth_Cons_0 nth_Cons_Suc zero_less_Suc)
  by (metis Suc_inject lessI lift_Suc_mono_less_iff nth_Cons_Suc)


lemma inconv_bot[simp]:"inconv\<cdot>\<bottom> = \<bottom>"
  apply(simp add: inconv.rep_eq)
  by(simp add: bot_sb)

lemma [ccodeAbs]:"Rep_lsb (inconv\<cdot>sb) =  (\<lambda>c. smap (Timed o TFin)\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb \<^enum> (tstimedToOrigin c)))))"
  by(simp add: inconv.rep_eq)

lemma inconv_len[simp]:"#\<^sub>\<surd>(inconv\<cdot>sb) = #\<^sub>\<surd>sb"
  apply (rule sbtlen_tstimed_eqI)
  apply (simp add: inconv.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  apply simp+
proof-
  fix c :: 'a
  assume c_in_chdom: "Rep c \<in> chDom TYPE('a)"
  hence timed_tlive_svalues_subset: "sValues\<cdot>(sb  \<^enum>  c) \<subseteq> range (Timed \<circ> TLive)"
    using c_in_chdom echan_svalues by blast
  thus "#\<^sub>\<surd> (smap (Timed \<circ> TFin)\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb  \<^enum>  c)))) =
       #\<^sub>\<surd> (sb  \<^enum>  c)"
    apply (subst (2) smap_tlen [where f="m2event", symmetric])
    apply (auto)[1]
    apply (subst stimedtolistlen[symmetric])
    apply (rule smap_list_tlen)
    by simp
qed

lemma inconv_split:
  assumes "\<And>c. Rep c \<in> chDom TYPE('a::echan) \<Longrightarrow> (Timed (TLive Tick)) \<in> sValues\<cdot>((sb::'a\<^sup>\<Omega>) \<^enum> c)"
  shows "inconv\<cdot>sb = inconv\<cdot>(sbHdTs\<cdot>sb \<Zcat>\<^sup>\<Omega> ticksb) \<Zcat>\<^sup>\<Omega> inconv\<cdot>(sbRtTs\<cdot>sb)"
  apply (subst sb_step)
  apply (simp add: assms)
  apply (rule sb_eqI)
  apply (simp add: sbgetch_insert2)
  apply (simp add: inconv.rep_eq)
  apply (subst Abs_lsb_inverse)
  apply (metis (no_types, lifting) BundleMergeTs.c0_nc mem_Collect_eq rep_sb_well lsb_well_def sbconc_getch)
  apply (subst sbConc.rep_eq)
  apply (subst (4) sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  apply (metis (no_types, lifting) mem_Collect_eq lsb_well_def sbconc_getch sbgetch_ctypewell sbgetch_insert2)
  apply (subst (6) sbgetch_insert2)
  apply (subst Abs_lsb_inverse, simp)
  apply (metis (mono_tags, lifting) BundleMergeTs.c0_nc rep_sb_well lsb_well_def sbconc_getch)
  apply (subst Abs_lsb_inverse, simp)
  apply (subst (1 2) smap_m2event_timedtlive_inv_eq)
  apply (metis echan_svalues empty_iff sValues_notempty sbconc_getch sbgetch_empty subsetI)
  apply (metis assms echan_svalues sb_step sbconc_getch sbgetch_empty smap_sValues_range strict_smap)
  apply (subst (2) sbgetch_insert2)
  apply (subst ticksb_insert)
  using chandomchdomeq chdom_empty apply blast
  apply (simp add: smap_split)
  apply (subst stimedtolist_split)
  apply (metis Zero_lnless_infty assms only_empty_has_length_0 sbgetch_empty sbhdts_getch_len slen_smap)
  apply (subst smap_split)
  apply (subgoal_tac "\<up>Tick = smap (inv TLive \<circ> inv Timed)\<cdot>(ticksb \<^enum> tstimedToOrigin c)")
  apply simp
  apply (subst smap_split [symmetric])
  apply (metis (no_types, opaque_lifting) cnotempty_cdom echan_svalues
      sbgetch_empty2 smap_m2event_timedtlive_inv_eq smap_split strict_smap)
  apply (simp add: sbgetch_insert2)
  apply (subst ticksb_insert)
  using chandomchdomeq chdom_empty apply blast
  by simp

lemma inconv_sbhdts_tlen_zero_gt:
  assumes "#\<^sub>\<surd>sb > 0"
  shows "inconv\<cdot>(sbHdTs\<cdot>sb \<Zcat>\<^sup>\<Omega> ticksb) = sbe2sb (inconvOutSBE (sbHdTs\<cdot>sb))"
  apply (rule sb_eqI)
  apply (subst inconv.rep_eq)
  apply (subst sbgetch_insert2)
  apply (subst Abs_lsb_inverse)
  using inconv_well apply blast
  apply (subst stimedtolist_tsstep)
  apply (simp)
  apply (subst (2) sbgetch_insert2)
  apply (subst ticksb_insert)
  using chandomchdomeq chdom_empty apply blast
  apply (subst smap_m2event_timedtlive_inv_eq)
  apply (metis chandomchdomeq chdom_empty chdom_in echan_svalues equals0D sbconc_getch sbgetch_insert2 ticksb_insert)
  apply (subst smap_split)
  apply (rule svalues_sconc_in)
  apply (rule disjI2)
  apply simp
  apply (subst slen_smap)
  apply (metis SB.slen_empty_eq Zero_lnless_infty assms sbhdts_sbgetch_len2)
  apply (subst smap_split)
  apply simp
  apply (subst (4) sbgetch_insert2)
  apply (subst ticksb_insert)
  using chandomchdomeq chdom_empty apply blast
  apply (subst (2) smap_split)
  apply (subst (3) smap_m2event_timedtlive_inv_eq)
  apply simp
  apply simp
  apply (subst (14) sconc_snd_empty [symmetric])
  apply (subst tsrt_split_eq)
  apply simp
  apply (rule sbhdts_sbgetch_tlengr_len)
  apply (metis assms chandomchdomeq chdom_empty emptyE leI less_le_trans lnless_def sbtlenleq')
  apply (subst sbhdts_sbgetch_m2event)
  apply (metis image_iff not_Event_eq smap_sValues)
  apply simp
  apply (subst (2) sbgetch_insert2)
  apply (subst ticksb_insert)
  using chandomchdomeq chdom_empty apply blast
  apply (subst smap_split)
  apply (subst (2)smap_m2event_timedtlive_inv_eq)
  apply simp
  apply simp
  apply (subst (6) sconc_snd_empty [symmetric])
  apply (subst eshdts_split_eq)
  apply (subst sbhdts_sbgetch_m2event)
  apply simp
  apply (rule eshdts_len)
  apply (simp add: smap_sValues image_iff)
  apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
  apply (rule tlen_timedtlive_zero_gt)
  apply (metis echan_svalues empty_subsetI sValues_notempty sbgetch_empty)
  apply (metis assms empty_iff less_le_trans neq_iff sbtlen_bot' sbtlen_min_len sbtlen_tstimed_eqI)
  apply (subst smap_m2event_timedtlive_inv_eq)
  apply (metis echan_svalues empty_subsetI sValues_notempty sbgetch_empty)
  apply (subgoal_tac "Timed (TLive Tick) \<notin> sValues\<cdot>(sbHdTs\<cdot>sb  \<^enum>  tstimedToOrigin c)")
  apply (metis echan_svalues empty_iff sValues_notempty sbgetch_insert smap_sValues strict_smap ttlive_stream_set_in)
  apply (metis echan_svalues empty_iff sValues_notempty sbgetch_insert sbhdts_getch_tlen tlen_timedtlive_zero)
  apply (subst sbhdts_sbgetch_m2event)
  apply (simp add: smapsmap2smap)
  apply (subst(2) sbgetch_insert2)
  apply (simp add: inconvOutSBE_def sbe2sb.rep_eq)
  apply (rule conjI)
  apply (rule impI)
  using chandomchdomeq chdom_empty apply blast
  apply (simp add: sbhdts_getch)
  apply (subst (2) smap_m2event_timedtlive_inv_eq [symmetric])
  using smap_sValues_range apply blast
  apply (subst (2) smapsmap2smap)
  apply simp
  apply (subst smapsmap2smap)
  apply simp
  apply (subst Abs_sbElem_inverse)
  apply simp
  apply (subst ctype_tfinchan_def)
  apply (metis chandomchdomeq chdom_empty empty_iff tstimed_ctime)
  apply blast
  apply (simp add: image_iff)
  apply (subst set2svalues)
  apply (rule eshdts_len)
  apply (simp add: smap_sValues image_iff)
  apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
  apply (rule tlen_timedtlive_zero_gt)
  apply (metis echan_svalues empty_subsetI sValues_notempty sbgetch_empty)
  apply (metis assms empty_iff less_le_trans neq_iff sbtlen_bot' sbtlen_min_len sbtlen_tstimed_eqI)
  using eshdts_svalues_cmsg apply blast
  by simp

declare tlen_len_eq[simp del]

lemma inconv_sb_tlen_zero:
  assumes "#\<^sub>\<surd>(sb) = 0"
  shows "#(inconv\<cdot>sb) = 0"
  by (subst tlen_len_eq [symmetric], simp add: assms)


lemma convertsem_step [simp]:
  "convertSem\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>(convtrans sbe) \<Zcat> convertSem\<cdot>sb"
  apply (simp add: convertSem_def convertAut_def tsExecStateSem_def)
  by (subst dastatesem_step, simp add: case_prod_unfold)

lemma convsem_empty[simp]:
  assumes "chDom TYPE('cs::{tschan,enum}) = {}"
  shows "convertSem\<cdot>(sb::'cs\<^sup>\<Omega>) = ((\<up>[])\<^sup>\<infinity>)"
  apply (subst sbtypeepmpty_sbbot, simp add: assms)
  apply (rule rek2sinftimes)
  apply (simp add: convertSem_def)
  apply (subst convertAut_def, simp)
  apply (subst (2) convertAut_def, simp)
  apply (simp add: tsExecStateSem_def convertAut_def)
  apply (subst dastatesem_step, simp)
  by (simp_all add: sb_steps_sbe_empty2 assms convtrans_def)

lemma convertsem_len[simp]:"#(convertSem\<cdot>sb) = #\<^sub>\<surd>sb"
  apply (induction sb, simp_all)
  apply (rule adm_eq)
  apply (rule cont_compose_mix)
  apply (intro cont2cont)+
  by (simp add: convertSem_def tsExecStateSem_def convertAut_def tlen_len_eq)

lemma convertsem_sb_len_zero:
  assumes "#sb = 0"
  shows "convertSem\<cdot>sb = \<bottom>"
  apply (simp add: convertSem_def convertAut_def tsExecStateSem_def)
  apply (subst dastatesem_step)
  by (simp add: assms)

lemma convertsem_sbvalues_subset:
  "\<Union>(set ` \<Union>(set ` sValues\<cdot>(convertSem\<cdot>(sb::('cs::{tschan,enum})\<^sup>\<Omega>)))) \<subseteq> \<Union>((\<lambda>(c, m). Pair c ` set (m2list m)) ` sbValues\<cdot>sb)"
  apply (induction sb)
  apply (subst less_set_def[symmetric])
  apply (rule adm_below)
  apply (rule cont_compose_mix)+
  apply (rule cont_compose [where f="(\<lambda>a. \<Union> (set ` a))"])
  using Union_set_image_cont cont_compose image_cont apply blast
  apply (intro cont2cont)
  apply (rule contI2)
  apply (rule monofunI)
  apply (subgoal_tac "sbValues\<cdot>x \<sqsubseteq> sbValues\<cdot>y")
  apply (simp add: set_cpo_simps case_prod_unfold)
  apply blast
  using monofun_cfun_arg apply blast
  apply (simp add: contlub_cfun_arg)
  apply (simp add: set_cpo_simps case_prod_unfold)
  apply simp
  apply (simp add: convertSem_def tsExecStateSem_def)
  apply (subst convertAut_def, simp)
  apply (subst sbecons_sbvalues)
  apply simp
  apply (simp only: convertsem_step)
  apply (subst sValues_sconc2un [where k="1"])
  apply simp
  apply (simp only: convtrans_def)
  apply (subst if_not_P)
  apply simp
  apply (simp only: image_Un Union_Un_distrib)
  apply (rule Un_mono)
  apply (subst sbValues_sbe2sb)
  apply simp
  apply (simp only: enum_UNIV image_iff case_prod_unfold)
  apply (simp only: sbelist_def)
  apply (rule subsetI)
  by auto

lemma convertsem_well:
  assumes "x \<in> \<Union>(set ` \<Union>(set ` sValues\<cdot>(convertSem\<cdot>(sb::'cs::{tschan,enum}\<^sup>\<Omega>))))"
  shows "well x"
proof-
  obtain c m where c_m_def: "x = (c,m)"
    by (meson surj_pair)
  have x_sbvalues: "x \<in> \<Union>((\<lambda>(c, m). Pair c ` set (m2list m)) ` sbValues\<cdot>sb)"
    apply (rule subsetD [where A="\<Union>(set ` \<Union>(set ` sValues\<cdot>(convertSem\<cdot>(sb::'cs::{tschan,enum}\<^sup>\<Omega>))))"])
    apply (metis convertsem_sbvalues_subset)
    using assms by blast
  hence "\<exists>y. m \<in> set (m2list y) \<and> (c,y) \<in> sbValues\<cdot>sb"
    apply (simp add: image_iff case_prod_unfold c_m_def)
    by (metis prod.collapse)
  then obtain mls where mls_def: "m \<in> set (m2list mls)" and "(c,mls) \<in> sbValues\<cdot>sb"
    by blast
  hence "set (m2list mls) \<subseteq> cMsg (Rep c)"
    by (meson sbvalues_m2list_cmsg)
  thus "well x"
    apply (simp add: well_def c_m_def)
    using mls_def by blast
qed

lemma convertsem_multilist_distinct:
  "\<forall>x \<in> sValues\<cdot>(convertSem\<cdot>(sb::'cs::{tschan, enum}\<^sup>\<Omega>)). multilist_distinct x"
  apply (induction sb)
  apply (rule admI)
  apply (rule ballI)
  apply (simp add: contlub_cfun_arg)
  apply (metis (no_types, lifting) UN_iff lub_eq_Union)
  apply simp
  apply (metis convertsem_sb_len_zero emptyE sValues_notempty)
  apply simp
  apply (rule multilist_distinctI)
  by (simp add: convtrans_def image_def Int_def enum_distinct nth_eq_iff_index_eq)

lemma convertsem_onechannel_predicate:
  assumes "\<not>chDomEmpty TYPE('cs::{tschan,enum})"
    and "\<exists>!x \<in> set enum_class.enum. P x"
  shows "\<forall>x \<in> sValues\<cdot>(convertSem\<cdot>(sb::'cs\<^sup>\<Omega>)). (\<exists>a \<in> set x. (\<forall>y \<in> set a. (\<lambda>(c,m). P c) y) \<and> (\<forall>z \<in> \<Union>(set ` set x). z \<notin> set a \<longrightarrow> \<not> (\<lambda>(c,m). P c) z))"
  apply (rule ballI)
  apply (induction sb)
  apply (rule adm_all)
  apply (rule adm_imp)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg)
  apply (simp add: lub_eq_Union)
  apply simp
  apply (simp add: assms)
  apply simp
  using convertsem_sb_len_zero sValues_notempty apply blast
  apply simp
  apply (erule disjE)
  apply (simp add: convtrans_def)
  defer
  apply blast
proof-
  fix sbe x
  obtain c where c_in_enum: "c \<in> set enum_class.enum" and c_p_true: "P c" 
      and c_neq_p_false: "(\<forall>y \<in> set enum_class.enum. c \<noteq> y \<longrightarrow> \<not>P y)"
    using assms(2) by blast
  thus "chDom TYPE('cs) \<noteq> {} \<Longrightarrow>
       x = map (\<lambda>c::'cs. map (Pair c) (sbelist c sbe)) enum_class.enum \<Longrightarrow>
       \<exists>a::'cs\<in>set enum_class.enum.
          ((\<exists>y::msg. y \<in> set (sbelist a sbe)) \<longrightarrow> P a) \<and>
          (\<forall>y::'cs\<in>set enum_class.enum.
              (\<exists>z::msg\<in>set (sbelist y sbe). (y, z) \<notin> Pair a ` set (sbelist a sbe)) \<longrightarrow> \<not> P y)"
    apply (rule_tac x="c" in bexI)
    apply (metis image_iff)
    by (simp add: enum_UNIV)
qed


lemma mergesem_mergestatesem_eq: "mergeSem = mergeStateSem s"
  by(simp add: execToAut.rep_eq mergeAut_def listfun_def mergeStateSem_def mergeSem_def sem_def 
     listToExec_def autInitConfig_def)

lemma mergesem_bot[simp]:"f\<in>mergeSem \<Longrightarrow> f\<cdot>\<epsilon> = \<epsilon>"
  apply (subst stateSem_bot [where step="stream_step" and aut="(execToAut (listToExec mergeAut))"])
  apply (subst (asm) mergesem_mergestatesem_eq)
  apply (simp add: mergeStateSem_def )
  apply (metis stream_step_eps)
  by simp

lemma mergesem_trans_out:
  assumes "(ns, out) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) s msg"
  shows "\<exists>n. out = \<up>((listfun (tsmerge msg) n))"
  apply (insert assms)
  by (auto simp add: execToAut.rep_eq listToExec_def mergeAut_def listfun_def)

lemma mergesem_trans_out_len:
  assumes "(nextState,out) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) s msg"
  shows "#out = 1"
  using assms lnzero_def mergesem_trans_out one_lnat_def by fastforce

lemma mergesem_step:
  assumes "f \<in> mergeSem"
  shows "\<exists>f2 \<in> mergeSem. \<exists>k. f\<cdot>(\<up>m \<Zcat> s) = \<up>(listfun (tsmerge m) k) \<Zcat> f2\<cdot>s"
proof-
  have f_in_mergestatesem: "f \<in> mergeStateSem ()"
    using assms mergesem_mergestatesem_eq by blast
  hence f_in_step: "f\<in>stateSem_step stream_step (execToAut (listToExec mergeAut)) (stateSem stream_step (execToAut (listToExec mergeAut))) ()"
    by (simp add: mergeStateSem_def stateSem_stepI)
  then obtain g where g_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) nextState 
        \<and>  (\<forall>sb. g msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and f_def: "f = stream_step\<cdot>g"
    by (auto simp add: f_in_mergestatesem mergeStateSem_def stateSem_step_def)
  then obtain out nextState nextSPF where 
    nextstate_out_def: "(nextState,out) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () m"
    and nextSPF_in: "nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) nextState"
    and g_def2: "(\<And> input. g m\<cdot>input = out \<Zcat>\<Zcat> nextSPF\<cdot>input)"
    by blast
  obtain k where k_def: "out = \<up>(listfun (tsmerge m) k)"
    using mergesem_trans_out nextstate_out_def by blast
  thus ?thesis
    apply (simp add: Bex_def)
    apply (rule_tac x="nextSPF" in exI)
    apply (rule conjI)
    apply (metis mergeStateSem_def mergesem_mergestatesem_eq nextSPF_in)
    apply (rule_tac x="k" in exI)
    by (simp add: f_def g_def2 listfun_def)
qed

lemma mergesem_els[simp]:"f\<in> mergeSem \<Longrightarrow> \<exists>f2 \<in> mergeSem. f\<cdot>(\<up>[] \<Zcat> s) = \<up>[] \<Zcat> f2\<cdot>s"
proof-
  assume f_mergesem: "f \<in> mergeSem"
  then obtain f2 k where f2_mergesem: "f2 \<in> mergeSem" and f_apply: "f\<cdot>(\<up>[] \<Zcat> s) = \<up>(listfun (tsmerge []) k) \<Zcat> f2\<cdot>s"
    using mergesem_step by blast
  thus ?thesis
    by (auto simp add: f_apply listfun_def)
qed

lemma mergesem_len[simp]:
  assumes "f \<in> mergeSem"
  shows "#(f\<cdot>s) = #s"
  using assms
proof (induction s arbitrary: f)
  case adm
  then show ?case
    apply (rule adm_all, rule adm_imp)
    apply (rule adm_upward)
    apply simp
    apply (rule adm_eq)
    apply (rule cont_compose_mix)
    by (intro cont2cont)+
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then obtain f2 k where f2_mergesem:"f2 \<in> mergeSem" and f_apply: "f\<cdot>(\<up>a \<Zcat> s) = \<up>(listfun (tsmerge a) k) \<Zcat> f2\<cdot>s"
    using mergesem_step by blast
  then show ?case
    by (simp add: f_apply step.IH f2_mergesem)
qed

lemma mergesem_emptylist[simp]:
  assumes "f \<in> mergeSem"
  shows "f\<cdot>((\<up>[])\<^sup>\<infinity>) = ((\<up>[])\<^sup>\<infinity>)"
proof (rule snths_eq)
  show "#(f\<cdot>\<up>[]\<^sup>\<infinity>) = #\<up>[]\<^sup>\<infinity>"
    by (simp add: assms)
next
  show "\<forall>n::nat. Fin n < #(f\<cdot>\<up>[]\<^sup>\<infinity>) \<longrightarrow> snth n (f\<cdot>\<up>[]\<^sup>\<infinity>) = snth n \<up>[]\<^sup>\<infinity>"
  proof (rule allI, rule impI)
    fix n
    assume f_n_le: "Fin n < #(f\<cdot>\<up>[]\<^sup>\<infinity>)"
    thus "snth n (f\<cdot>\<up>[]\<^sup>\<infinity>) = snth n \<up>[]\<^sup>\<infinity>"
      using assms
    proof (induction n arbitrary: f)
      case 0
      then obtain f2 :: "'a list list stream \<rightarrow> 'a list stream" where f_apply: "f\<cdot>(\<up>[] \<Zcat> ((\<up>[])\<^sup>\<infinity>)) = \<up>[] \<Zcat> f2\<cdot>((\<up>[])\<^sup>\<infinity>)" 
        and f2_mergesem: "f2 \<in> mergeSem"
        using mergesem_els by blast
      then show ?case
        by (metis shd1 sinftimes_unfold snth_shd)
    next
      case (Suc n)
      then obtain f2 :: "'a list list stream \<rightarrow> 'a list stream" where f_apply: "f\<cdot>(\<up>[] \<Zcat> ((\<up>[])\<^sup>\<infinity>)) = \<up>[] \<Zcat> f2\<cdot>((\<up>[])\<^sup>\<infinity>)" 
        and f2_mergesem: "f2 \<in> mergeSem"
        using mergesem_els by blast
      then show ?case
        by (metis Suc.IH Suc.prems(1) Suc.prems(2) convert_inductive_asm mergesem_len sinftimes_unfold snth_scons)
    qed
  qed
qed

lemma mergesem_svalues:
  assumes "f \<in> mergeSem"
  shows "\<Union>(set ` sValues\<cdot>(f\<cdot>s)) = \<Union>(set ` \<Union>(set ` (sValues\<cdot>s)))"
  using assms
proof (induction s arbitrary: f)
case adm
  then show ?case
    apply (rule adm_all, rule adm_imp)
    apply simp
    apply (rule adm_eq)
    apply (rule cont_compose_mix)+
    apply (intro cont2cont)
    apply (rule cont_compose_mix)+
    apply (rule cont_compose [where f="(\<lambda>x. \<Union> (set ` x))"])
    by (intro cont2cont)+
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  obtain nextSpf k where nextSpf_in_mergesem: "nextSpf \<in> mergeSem" and f_apply: "f\<cdot>(\<up>a \<Zcat> s) = \<up>(listfun (tsmerge a) k) \<Zcat> nextSpf\<cdot>s"
    using mergesem_step step.prems by blast
  have "set (listfun (tsmerge a) k) = \<Union>(set ` set a)"
    by (metis tsmerge_set listfuninset tsmerge_nempty)
  thus ?case
    by (auto simp add: f_apply nextSpf_in_mergesem step.IH)
qed

lemma mergesem_filter_eq:
  assumes "spf1 \<in> mergeSem"
    and "spf2 \<in> mergeSem"
    and "\<forall>x \<in> sValues\<cdot>s. multilist_distinct x"
    and "\<forall>x \<in> sValues\<cdot>s. (\<exists>a \<in> set x. (\<forall>y \<in> set a. (\<lambda>(c,m). P c) y) \<and> (\<forall>z \<in> \<Union>(set ` set x). z \<notin> set a \<longrightarrow> \<not> (\<lambda>(c,m). P c) z))"
  shows "smap (filter (\<lambda>(c,m). P c))\<cdot>(spf1\<cdot>s) = smap (filter (\<lambda>(c,m). P c))\<cdot>(spf2\<cdot>s)"
  using assms
proof (induction s arbitrary: spf1 spf2)
  case adm
  then show ?case
    apply (rule adm_all, rule adm_imp, simp)+
    apply (rule adm_imp)
    apply simp
    apply (rule adm_upward)
    using svalues_belowelem apply blast
    apply (rule adm_imp)
    apply (rule adm_upward)
    using svalues_belowelem apply blast
    apply (rule adm_eq)
    by (intro cont2cont)+
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then obtain xs where xs_set_a: "xs \<in> set a" and xs_P_true: "\<forall>x \<in> set xs. (\<lambda>(c,m). P c) x" and not_xs_P_false: "\<forall>z \<in> \<Union>(set ` set a). z \<notin> set xs \<longrightarrow> \<not>(\<lambda>(c,m). P c)z"
    by auto
  have spf1_mergestatesem: "spf1 \<in> mergeStateSem ()"
    using mergesem_mergestatesem_eq step.prems(1) by auto
  hence spf1_in_step: "spf1\<in>stateSem_step stream_step (execToAut (listToExec mergeAut)) (stateSem stream_step (execToAut (listToExec mergeAut))) ()"
    by (simp add: mergeStateSem_def stateSem_stepI)
  then obtain g1 where g1_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) nextState 
        \<and>  (\<forall>sb. g1 msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and spf1_def: "spf1 = stream_step\<cdot>g1"
    by (auto simp add: spf1_mergestatesem mergeStateSem_def stateSem_step_def)
  then obtain nextSPF1 state1 out1 where state1_out1_def: "(state1, out1) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () a"
      and g1_apply: "g1 a\<cdot>s = out1 \<Zcat>\<Zcat> nextSPF1\<cdot>s"
      and nextspf1_statesem: "nextSPF1 \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) state1"
    by blast
  hence nextspf1_mergesem: "nextSPF1 \<in> mergeSem"
    apply simp
    apply (subst (asm) mergeStateSem_def [symmetric])
    using mergesem_mergestatesem_eq by blast
  have spf2_mergestatesem: "spf2 \<in> mergeStateSem ()"
    using mergesem_mergestatesem_eq step.prems(2) by blast
  hence spf2_in_step: "spf2\<in>stateSem_step stream_step (execToAut (listToExec mergeAut)) (stateSem stream_step (execToAut (listToExec mergeAut))) ()"
    by (simp add: mergeStateSem_def stateSem_stepI)
  then obtain g2 where g2_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) nextState 
        \<and>  (\<forall>sb. g2 msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and spf2_def: "spf2 = stream_step\<cdot>g2"
    by (auto simp add: spf1_mergestatesem mergeStateSem_def stateSem_step_def)
  then obtain nextSPF2 state2 out2 where state2_out2_def: "(state2, out2) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () a"
      and g2_apply: "g2 a\<cdot>s = out2 \<Zcat>\<Zcat> nextSPF2\<cdot>s"
      and nextspf2_statesem: "nextSPF2 \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) state2"
    by blast
  hence nextspf2_mergesem: "nextSPF2 \<in> mergeSem"
    apply simp
    apply (subst (asm) mergeStateSem_def [symmetric])
    using mergesem_mergestatesem_eq by blast
  then obtain k where k_def: "out1 = \<up>((listfun (tsmerge a) k))"
    using mergesem_trans_out state1_out1_def by blast
  then obtain n where n_def: "out2 = \<up>((listfun (tsmerge a) n))"
    using mergesem_trans_out state2_out2_def by blast
  have "\<forall>x \<in> set (tsmerge a). filter (\<lambda>(c::'a, m::'b). P c) x = xs"
    apply (simp add: all_set_conv_all_nth)
    apply (rule allI)
    apply (rule impI)
    apply (rule wellordered_filter)
    apply (rule tsmerge_nth_wellordered)
    using wellordered_refl xs_set_a apply blast
    apply simp
    using step(4) apply fastforce
    using xs_P_true apply blast
    apply (rule ballI, rule impI)
    using not_xs_P_false tsmerge_union_set by fastforce
  thus ?case
    apply (simp add: spf1_def spf2_def g1_apply g2_apply smap_split)
    apply (subst step.IH [where ?spf2.0="nextSPF2"])
    using nextspf1_mergesem apply blast
    using nextspf2_mergesem apply blast
    using step(4) apply fastforce
    using step(5) apply fastforce
    apply (rule arg_cong [where f="(\<lambda>out. out \<Zcat> smap (filter (\<lambda>(c::'a, m::'b). P c))\<cdot>(nextSPF2\<cdot>s))"])
    by (simp add: k_def n_def listfun_def)
qed

lemma mergesem_convertsem_filter_eq:
  assumes "spf1 \<in> mergeSem"
    and "spf2 \<in> mergeSem"
    and "\<not>chDomEmpty TYPE('cs::{tschan,enum})"
    and "\<exists>!x \<in> set enum_class.enum. P x"
  shows "smap (filter (\<lambda>(c::'cs,m). P c))\<cdot>(spf1\<cdot>(convertSem\<cdot>sb)) = smap (filter (\<lambda>(c,m). P c))\<cdot>(spf2\<cdot>(convertSem\<cdot>sb))"
  apply (rule mergesem_filter_eq)
  apply (simp_all add: assms)
  using convertsem_multilist_distinct apply blast
  using convertsem_onechannel_predicate assms(3) assms(4) by auto


lemma outconv_eps[simp]:"outconv\<cdot>\<epsilon> = \<epsilon>"
and "outconv\<cdot>(updis [] && s) = \<up>Tick \<Zcat> outconv\<cdot>s"
and "outconv\<cdot>(updis ((c,a)#as) && s) = \<up>(EventMsg ( (tstimedToOrigin c,a))) \<Zcat> outconv\<cdot>(\<up> as \<Zcat> s)"
and outconv_empty[simp]:"outconv\<cdot>(\<up>[] \<Zcat> s) = \<up>Tick \<Zcat> outconv\<cdot>s"
and outconv_msg[simp]:"outconv\<cdot>(\<up>((c,a)#as) \<Zcat> s) = \<up>(EventMsg ( (tstimedToOrigin c,a))) \<Zcat> outconv\<cdot>(\<up> as \<Zcat> s)"
  by(simp_all add: outconv_def lscons_conv)

lemma outconv_len[simp]:"#\<^sub>\<surd>(outconv\<cdot>s) = #s"
proof(induction s)
  case adm
  then show ?case
    apply (rule adm_eq)
    apply (rule cont_compose_mix)
    apply(intro cont2cont)
    by simp
next
  case bottom
  then show ?case 
     by simp
next
  case (step a s)
  then show ?case
  proof(induction a)
    case Nil
    then show ?case
      by (simp add: lnat_suc_plus)
  next
    case (Cons a1 a2)
    then show ?case
      by(cases a1; simp)
  qed
qed

lemma outconv_smap_pair:
  "smap (\<lambda>(c::'cs::{countable, one_chan} tstimed, y::msg). (tstimedToOrigin c, y))\<cdot>(smap (Pair (TSTIMED c))\<cdot>s)
    = smap (Pair c)\<cdot>s"
  by (induction s, simp_all)

lemma efilter_outconv_in:
  "efilter (\<lambda>(x::'cs::{echan,enum}, e::msg). x = c)\<cdot>(outconv\<cdot>s) = outconv\<cdot>(smap (\<lambda>ls. filter (\<lambda>(x::'cs tstimed, e::msg). x = TSTIMED c) ls) \<cdot>s)"
  apply (induction s)
  apply (rule adm_eq)
  apply (intro cont2cont)+
  apply simp
  apply (induct_tac a; simp)
  apply (case_tac aa; simp)
  by (metis (mono_tags, lifting) case_prodD efilter_not_P tstimedToOrigin.elims)

lemma outconv_step:
  assumes "#as < \<infinity>"
    and "sValues\<cdot>as \<subseteq> \<Union>{range (Pair (TSTIMED c)) | c. True}"
  shows "outconv\<cdot>(\<up>(s2list as) \<Zcat> bs) = smap EventMsg\<cdot>(smap (\<lambda>(c,m). (tstimedToOrigin c, m))\<cdot>as) \<Zcat> \<up>Tick \<Zcat> outconv\<cdot>bs"
  apply (simp add: outconv_def)
  apply (simp add: assms slisttoevent_s2list_sconc)
  apply (simp add: emap_def smap_split)
  by (metis (no_types, lifting) emap_def emap_smap_event)


lemma "listoutconv(emap Rep_msgWithChan\<cdot>s) = Rep_cfun uSplit s"
  apply(simp add: listoutconv_def)
  using emap_repabs_id
  by (metis (no_types, lifting) ID1 cfcomp2)

lemma [ccodeAbs]:"Rep_lsb (uSplit\<cdot>(s::'cs msgWithChan event stream)) = (if chDom TYPE ('cs::{echan,finite}) = {} then (\<lambda>c. sbot) else (\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>s)))))"
  apply(simp)
  apply (rule conjI)
  apply(simp add: uSplit.rep_eq)
  apply (metis Rep_lsb_strict app_strict)
  apply (rule impI)
  by (simp_all add: demerge_rep_eq)
  
lemma [code]:"Rep_msgWithChan (Abs_msgWithChan(cs, n)) = (cs,n)"
  oops

lemma [code]:"Rep_cfun (emap f) = Rep_cfun (smap (map_event f))"
  by(simp add: emap_def)


lemma bmerge_evalues_wellI:
  assumes "mergesem \<in> mergeSem"    
    and "x \<in> eValues\<cdot>(outconv\<cdot>(mergesem\<cdot>(convertSem\<cdot>(inconv\<cdot>(sb::('cs::{echan,enum})\<^sup>\<Omega>)))))"
  shows "well x"
  apply (insert assms)
  apply (simp add: outconv_def emap_evalues image_iff case_prod_unfold slisttoevent_evalues)
proof-
  assume "\<exists>y::('cs tstimed \<times> msg) list\<in>sValues\<cdot>(mergesem\<cdot>(convertSem\<cdot>(inconv\<cdot>sb))).
       \<exists>xa::'cs tstimed \<times> msg\<in>set y. x = (tstimedToOrigin (fst xa), snd xa)"
  then obtain y m where "y \<in> sValues\<cdot>(mergesem\<cdot>(convertSem\<cdot>(inconv\<cdot>sb)))"
    and "m \<in> set y" and m_def: "x = (tstimedToOrigin (fst m), snd m)"
    by blast
  hence "m \<in> \<Union>(set ` \<Union>(set ` sValues\<cdot>(convertSem\<cdot>(inconv\<cdot>sb))))"
    by (metis (no_types, opaque_lifting) UN_iff assms(1) mergesem_svalues)
  hence "well m"
    using convertsem_well by blast
  thus "well x"
    by (metis m_def prod.collapse tstimedToOrigin.elims tstimedwell)
qed

lemma bmerge_tlen_zero:
  assumes "spf \<in> bMerge"
    and "#\<^sub>\<surd>sb = 0"
  shows "spf\<cdot>sb = \<epsilon>"
proof-
  obtain mergesem where spf_def:"spf = emap Abs_msgWithChan oo outconv oo mergesem oo convertSem oo inconv"
    and sem_in_mergesem: "mergesem \<in> mergeSem"
    using bMerge_def assms by blast
  thus ?thesis
    by (simp add: assms spf_def convertsem_sb_len_zero inconv_sb_tlen_zero)
qed

lemma bmerge_lenwell[simp]:assumes"spf \<in> bMerge"
  shows"#\<^sub>\<surd> (spf\<cdot>sb) = #\<^sub>\<surd> sb"
  using assms 
  by(auto simp add: bMerge_def)

lemma bmerge_filter_eq:
  assumes "spf1 \<in> bMerge"
    and "spf2 \<in> bMerge"
    and "\<not>chDomEmpty TYPE('cs::{echan,enum})"
    and "\<exists>!x \<in> set enum_class.enum. P x"
  shows "efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf1\<cdot>(sb::'cs\<^sup>\<Omega>))) = efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf2\<cdot>(sb::'cs\<^sup>\<Omega>)))"
proof-
  obtain mergesem1 where spf1_def: "spf1 = emap Abs_msgWithChan oo outconv oo mergesem1 oo convertSem oo inconv"
      and sem1_in_mergesem: "mergesem1 \<in> mergeSem"
    using assms bMerge_def by blast
  obtain mergesem2 where spf2_def: "spf2 = emap Abs_msgWithChan oo outconv oo mergesem2 oo convertSem oo inconv"
    and sem2_in_mergesem: "mergesem2 \<in> mergeSem"
    using assms bMerge_def by blast
  thus ?thesis
    apply (simp add: spf1_def spf2_def)
    apply (subst emap_absrep_id)
    using bmerge_evalues_wellI sem1_in_mergesem apply blast
    apply (simp add: efilter_outconv_in)
    apply (subst mergesem_convertsem_filter_eq [where ?spf2.0="mergesem2"])
    apply (simp add: sem1_in_mergesem)
    apply simp
    apply (metis assms(3) chandom_chdom_eq chdom_empty)
    apply (simp add: enum_UNIV)
    apply (simp add: efilter_outconv_in [symmetric])
    apply (subst emap_absrep_id, simp_all)
    using bmerge_evalues_wellI by blast
qed

lemma bmerge_efilter_split:
  assumes "spf \<in> bMerge"
    and "\<not>chDomEmpty TYPE('cs::{echan,enum})"
    and "#\<^sub>\<surd>sb > 0"
  shows "efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf\<cdot>(sb::'cs\<^sup>\<Omega>))) = smap EventMsg\<cdot>
          (smap (Pair c)\<cdot>
           (smap (inv EventMsg)\<cdot>
            (smap (inv TLive \<circ> inv Timed)\<cdot>
             (sbHdTs\<cdot>sb  \<^enum>  c)))) \<Zcat> \<up>Tick \<Zcat> efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf\<cdot>(sbRtTs\<cdot>sb)))"
proof-
  obtain mergesem where spf_def:"spf = emap Abs_msgWithChan oo outconv oo mergesem oo convertSem oo inconv"
    and sem_in_mergesem: "mergesem \<in> mergeSem"
    using assms bMerge_def by blast
  hence f_in_mergestatesem: "mergesem \<in> mergeStateSem ()"
    using mergesem_mergestatesem_eq by blast
  hence f_in_step: "mergesem\<in>stateSem_step stream_step (execToAut (listToExec mergeAut)) (stateSem stream_step (execToAut (listToExec mergeAut))) ()"
    by (simp add: mergeStateSem_def stateSem_stepI)
  then obtain g where g_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) nextState 
        \<and>  (\<forall>sb. g msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and f_def: "mergesem = stream_step\<cdot>g"
    by (auto simp add: f_in_mergestatesem mergeStateSem_def stateSem_step_def)
  then obtain nextSPF state out where state_out_def: "(state, out) \<in> (autTransition\<cdot>(execToAut (listToExec mergeAut))) () (convtrans (inconvOutSBE (sbHdTs\<cdot>sb)))"
      and g_apply: "g (convtrans (inconvOutSBE (sbHdTs\<cdot>sb)))\<cdot>(convertSem\<cdot>(inconv\<cdot>(sbRtTs\<cdot>sb))) = out \<Zcat>\<Zcat> nextSPF\<cdot>(convertSem\<cdot>(inconv\<cdot>(sbRtTs\<cdot>sb)))"
      and nextspf_statesem: "nextSPF \<in> (stateSem stream_step (execToAut (listToExec mergeAut))) state"
    by blast
  hence nextspf_mergesem: "nextSPF \<in> mergeSem"
    apply simp
    apply (subst (asm) mergeStateSem_def [symmetric])
    using mergesem_mergestatesem_eq by blast
  then obtain bmergeSPF :: "'cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream" where bmergeSPF_def: "bmergeSPF = (\<Lambda> sb. ((emap Abs_msgWithChan\<cdot>(outconv\<cdot>(nextSPF\<cdot>(convertSem\<cdot>(inconv\<cdot>sb)))))))"
    by simp
  hence bmergeSPF_in_bmerge: "bmergeSPF \<in> bMerge"
    apply (simp add: bMerge_def)
    apply (simp add: image_iff)
    apply (rule_tac x="nextSPF" in bexI)
    apply (simp add: cfcomp1)
    using nextspf_mergesem by blast
  then obtain k where k_def: "out = \<up>(listfun (tsmerge (convtrans (inconvOutSBE (sbHdTs\<cdot>sb)))) k)"
    using mergesem_trans_out state_out_def by blast
  have sb_channel_nempty: "\<And>c. (sb \<^enum> c) \<noteq> \<epsilon>"
    by (metis assms(2) assms(3) less_le_trans lnless_def sbtlen_min_len stream_tlen_eps)
  have nextspf_bmergespf_eq: "\<forall>sb. emap Abs_msgWithChan\<cdot>(outconv\<cdot>(nextSPF\<cdot>(convertSem\<cdot>(inconv\<cdot>(sb))))) = bmergeSPF\<cdot>sb"
    by (simp add: bmergeSPF_def)
  have sb_svalues_ttlive_range: "\<And>c. sValues\<cdot>(sb \<^enum> c) \<subseteq> range (Timed \<circ> TLive)"
    by (meson \<open>\<And>c::'cs. (sb::'cs\<^sup>\<Omega>) \<^enum> c \<noteq> \<epsilon>\<close> echan_svalues sbgetch_empty)
  thus ?thesis
    apply (subst spf_def, simp)
    apply (subst emap_absrep_id)
    using bmerge_evalues_wellI sem_in_mergesem apply blast
    apply (subst inconv_split)
    apply (rule tlen_timedtlive_zero_gt)
    using echan_svalues apply blast
    apply (meson assms(2) assms(3) less_le_trans sbtlen_min_len)
    apply (subst inconv_sbhdts_tlen_zero_gt)
    apply (simp add: assms)
    apply (simp add: efilter_outconv_in)
    apply (simp add: f_def g_apply k_def smap_split)
    apply (simp add: convtrans_def)
    apply (rule conjI)
    apply (rule impI)
    apply (insert assms (2))
    apply simp
    apply (rule impI)
    apply (simp add: listfunmaptof)
    apply (simp add: listfun_def)
    apply (subst wellordered_filter [where xs="map (Pair (TSTIMED c)) (sbelist (TSTIMED c) (inconvOutSBE (sbHdTs\<cdot>sb)))"])
    apply (rule tsmerge_nth_wellordered)
    apply (subgoal_tac "TSTIMED c \<in> set (enum_class.enum)")
    using wellordered_refl apply fastforce
    apply (simp add: enum_UNIV)
    apply simp
    apply (rule multilist_distinctI)
    apply simp
    apply (rule allI, rule impI)+
    apply (rule impI)
    apply (simp add: image_def Int_def eq_commute enum_distinct nth_eq_iff_index_eq)
    apply (simp add: enum_distinct nth_eq_iff_index_eq)
    apply simp
    apply (simp add: case_prod_unfold)
    apply (rule ballI, rule impI)
    apply (subst (asm) tsmerge_set [where ls="(map (\<lambda>c::'cs tstimed. map (Pair c) (sbelist c (inconvOutSBE (sbHdTs\<cdot>sb)))) enum_class.enum)"])
    apply fastforce
    apply fastforce
    apply (simp add: inconvOutSBE_def)
    apply (simp add: sbelist_def)
    apply (subst sbegetch_insert)
    apply (metis chandomchdomeq chdom_empty chdom_in)
    apply (subst abs_rep_id)
    apply (subst Abs_sbElem_inverse)
    apply simp
    apply (subst ctype_tfinchan)
    using tstimed_ctime apply blast
    apply (metis ctype_empty_iff dom2ctypenempty tstimedtoorigin_cmsg)
    apply simp
    apply (rule allI) 
    apply (rule imageI)
    apply (simp)
    apply (subst set2svalues)
    apply (simp add: sbhdts_getch)
    apply (rule eshdts_len)
    apply (case_tac c; simp)
    apply (subgoal_tac "Timed (TLive Tick) \<in> sValues\<cdot>(sb \<^enum> x)")
    apply (metis smap_sValues ttlive_stream_set_nin)
    apply (metis assms(3) less_le_trans sb_svalues_ttlive_range sbtlen_min_len tlen_timedtlive_zero_gt)
    apply (subst smap_m2event_timedtlive_inv_eq [symmetric])
    apply (simp add: sbhdts_getch)
    using sbhdts_svalues apply blast
    apply (simp add: sbhdts_getch)
    apply (subst (2) smapsmap2smap, simp)
    apply (simp add: smapsmap2smap)
    using eshdts_svalues_cmsg apply blast
    apply simp
    apply (subst s2list_mapsmap, simp add: sbhdts_getch)
    apply (rule eshdts_len)
    apply (simp add: smap_sValues image_iff)
    apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
    apply (meson assms(3) less_le_trans sb_svalues_ttlive_range sbtlen_min_len tlen_timedtlive_zero_gt)
    apply (subst outconv_step, simp add: sbhdts_getch)
    apply (rule eshdts_len)
    apply (simp add: smap_sValues image_iff)
    apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
    apply (meson assms(3) less_le_trans sb_svalues_ttlive_range sbtlen_min_len tlen_timedtlive_zero_gt)
    apply (metis (mono_tags, lifting) Sup_upper2 mem_Collect_eq smap_sValues_range)
    apply (simp add: outconv_smap_pair)
    apply (simp add: efilter_outconv_in [symmetric])
    apply (subst (6) emap_absrep_id [symmetric])
    using bmerge_evalues_wellI nextspf_mergesem apply blast
    apply (simp add: nextspf_bmergespf_eq)
    apply (subst bmerge_filter_eq [where ?spf2.0="spf" and P="(\<lambda>x. x = c)"])
    using bmergeSPF_in_bmerge apply blast
    using assms(1) apply force
    apply blast
    apply (simp add: enum_UNIV)
    by simp
qed

lemma bmerge_sbrt_efilter_split:
  assumes "spf \<in> bMerge"
    and "\<not>chDomEmpty TYPE('cs::{echan,enum})"
    and "#\<^sub>\<surd>sb > 0"
    and "#\<^sub>\<surd>(sbRtCh c\<cdot>sb) > 0"
  shows "efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf\<cdot>(sbHdTs\<cdot>(sbRtCh c\<cdot>(sb::'cs\<^sup>\<Omega>)) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>(sb))))
 = smap EventMsg\<cdot>
      (smap (Pair c)\<cdot>
       (eshdts\<cdot>
        (smap (inv TLive \<circ> inv Timed)\<cdot>
         (srt\<cdot>(sb  \<^enum>  c))))) \<Zcat> \<up>Tick \<Zcat> efilter (\<lambda>(x::'cs, e::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(spf\<cdot>(sbRtTs\<cdot>sb)))"
proof-
  obtain tlenc where tlenc_def: "#\<^sub>\<surd> (sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb) = #\<^sub>\<surd> ((sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb) \<^enum> tlenc)"
    using sbtlen2stlen assms(2) by blast
  have sbrtch_tlen_eq: "#\<^sub>\<surd>(shd (sb \<^enum> c)) = 0 \<Longrightarrow> #\<^sub>\<surd>(sbRtCh c\<cdot>sb) = #\<^sub>\<surd>(sb)"
    apply (rule sbdropch_tlen_eq)
    apply (subst (2 3)surj_scons[symmetric])
    apply (metis assms(2) assms(3) leD sbtlen_min_len stream_tlen_eps)
    by simp
  have tick_sbhdts_splitted_in: "\<And>c1. Timed (TLive Tick) \<in> sValues\<cdot>((sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb) \<^enum> c1)"
  proof-
    fix c1
    have "#(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<^enum> c1) < \<infinity>"
      apply (rule sbhdts_sbgetch_tlengr_len)
      by (meson assms(2) assms(4) less_le_trans sbtlen_min_len)
    then obtain n where "#(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<^enum> c1) = Fin n"
      by (meson assms(2) assms(3) lnat_well_h2 sbhdts_sbgetch_len2)
    thus "Timed (TLive Tick) \<in> sValues\<cdot>((sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb) \<^enum> c1)"
      apply simp
      apply (subst sValues_sconc2un [where k="n"])
      apply blast
      apply simp
      apply (rule disjI2)
      apply (subst sbgetch_insert2)
      apply (subst ticksb_insert)
      using assms(2) apply blast
      by (metis Un_iff insert_iff sValues2un)
  qed
  thus ?thesis
    apply (subst bmerge_efilter_split)
    apply (simp add: assms)
    apply (simp add: assms)
    apply (metis assms(2) chdom_in echan_svalues sbtlen2stlen ttlive_tick_in_tlen)
    apply (subst sbhdts_split_eq)
    using assms(4) apply blast
    apply (subst sbrtts_split_eq)
    using assms(3) apply blast
    using sbhdts_getch_tlen apply blast
    using assms(4) sbhdts_sbgetch_len2 apply blast
    apply (simp add: sbhdts_getch sbdropch_cheq_getch)
    apply (subst sdrop_back_rt)+
    apply (subst smap_m2event_timedtlive_inv_eq [symmetric])
    apply (meson smap_sValues_range)
    apply (subst (4) smapsmap2smap, simp)
    by (subst (3) smapsmap2smap, simp)
qed

section\<open>Splitting the output of @{const bMerge} is prefix of input\<close>

lemma ssplit_prefix_snth_h:
  assumes "spf \<in> bMerge"
    and "\<not> chDomEmpty TYPE('cs::{echan,enum})"
    and "#\<^sub>\<surd>sb > 0"
    and "Fin n < #(efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf\<cdot>(sb::'cs\<^sup>\<Omega>))))"
  shows "snth n
              (smap (Timed \<circ> TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x, e). x = c)\<cdot>(emap (Rep_msgWithChan)\<cdot>(spf\<cdot>sb))))) =
       snth n (sb \<^enum> c)"
  using assms
proof (induction n arbitrary: spf sb)
  case 0
  then show ?case
    apply (subst bmerge_efilter_split)
    using "0.prems"(1) apply blast
    using assms(2) apply blast
    using "0.prems"(3) apply blast
    apply (simp add: sbhdts_getch)
    apply (case_tac "(sb  \<^enum> c)" rule: tlive_scases)
    apply (meson cnotempty_cdom echan_svalues)
    apply (metis leD sbtlen_min_len stream_tlen_eps)
    apply (case_tac a; simp)
    by (simp add: eshdts_event)
next
  case (Suc n)
  have sb_channel_nempty: "sb \<^enum> c \<noteq> \<epsilon>"
    by (metis Suc.prems(3) assms(2) leD sbtlen_min_len stream_tlen_eps)
  then show ?case
    apply (subst bmerge_efilter_split)
    using Suc.prems(1) apply blast
    using assms(2) apply blast
    using Suc.prems(3) apply blast
    apply (insert Suc.prems(4))
    apply (subst (asm) bmerge_efilter_split)
    using Suc.prems(1) apply blast
    apply (simp add: assms(2))
    using Suc.prems(3) apply blast
    apply (simp add: sbhdts_getch)
    apply (simp add: timed_tlive_event_smap_id)
    apply (subst (4) sb_step)
    apply (meson Suc.prems(3) assms(2) echan_svalues less_le_trans sbtlen_min_len tlen_timedtlive_zero_gt)
    apply simp
    apply (simp add: sbhdts_getch)
    apply (cases "#\<^sub>\<surd>(sbRtTs\<cdot>sb) = 0")
    apply (simp add: bmerge_tlen_zero Suc)
    apply (simp add: emap_smap_event [symmetric])
    apply (subst (asm) emaptick2 [where f="Pair c", symmetric])
    apply (subst (asm) emap_split[symmetric], simp)
    apply (simp add: emap_split pairsnd_emap)
    apply (subst (3)sbgetch_insert2)
    apply (subst ticksb_insert)
    using assms(2) apply blast
    apply (simp add: smap_split)
    apply (metis (no_types, lifting) assoc_sconc sconc_snd_empty
        slen_smap slen_snth_prefix smap_timedtlive_h strict_smap)
    apply (subst (asm) emap_smap_event [symmetric])
    apply (subst (asm) (7) surj_scons [symmetric])
    using sb_channel_nempty apply blast
    apply (subst (7 18) surj_scons [symmetric])
    using sb_channel_nempty apply blast
    apply (case_tac "shd (sb \<^enum> c)" rule: tlive_cases)
    apply (metis (mono_tags, opaque_lifting) Fin_02bot Stream.slen_empty_eq assms(2) bot_is_0 chdom_in echan_svalues lnless_def minimal sb_channel_nempty snth2sValues snth_shd subsetD)
    apply simp
    apply (subst sbgetch_insert2)
    apply (subst ticksb_insert)
    using assms(2) apply blast
    apply simp
    apply (rule Suc.IH)
    using Suc.prems(1) apply blast
    using assms(2) apply blast
    apply (metis lnless_def lnzero_def minimal)
    apply simp
    apply simp
    apply (simp add: eshdts_event)
    apply (subst bmerge_sbrt_efilter_split [symmetric])
    using Suc.prems(1) apply blast
    using assms(2) apply blast
    using Suc.prems(3) apply blast
    apply (subst sbdropch_tlen_eq)
    apply (subst (2 3) surj_scons [symmetric])
    using sb_channel_nempty apply blast
    apply simp
    using Suc.prems(3) apply blast
    apply (subst (10) sdrop_0 [symmetric])
    apply (subst sdrop_forw_rt [symmetric])
    apply (subst sbdropch_cheq_getch [symmetric])
    apply (subst timed_tlive_event_smap_id [symmetric])
    apply (subst sbhdts_getch [symmetric])
    apply (subst (2) smapsmap2smap)
    apply (subst smap_inv_id)
    apply (metis echan_svalues sb_channel_nempty sbgetch_empty sbhdts_sbgetch_m2event smap_m2event_timedtlive_inv_eq smap_sValues_range)
    apply (subst smap_m2event_timedtlive_inv_eq [symmetric])    
    apply (meson echan_svalues sb_channel_nempty sbgetch_empty)
    apply (simp add: smapsmap2smap)
    apply (subst helper)
    using echan_svalues sb_channel_nempty sbgetch_empty apply blast
    apply (subst sbconc_getch [symmetric])+
    apply (rule Suc.IH)
    using Suc.prems(1) apply blast
    using assms(2) apply blast
    apply (rule sb_step_tlen_gr0)
    apply (rule sbhdts_getch_len)
    apply (subgoal_tac "#\<^sub>\<surd>(sb \<^enum> c) > 0")
    apply (case_tac "ca = c")
    apply simp
    apply (simp add: sbdropch_cheq_getch)
    apply (subst (2) surj_scons [symmetric])
    using sb_channel_nempty apply fastforce
    apply (subst (asm) (16) surj_scons [symmetric])
    using sb_channel_nempty apply fastforce
    apply simp
    apply (rule tlen_timedtlive_zero_gt)
    apply (metis (no_types, opaque_lifting) echan_svalues sdrop_0 sdrop_forw_rt sdrop_sValues subset_trans)
    apply blast
    apply (rule tlen_timedtlive_zero_gt)
    apply (meson echan_svalues)
    apply (metis Suc.prems(3) assms(2) less_le_trans sbdropch_chneq_getch sbtlen_min_len)
    apply (meson Suc.prems(3) assms(2) less_le_trans sbtlen_min_len)
    apply (simp add: emap_smap_event)
    apply (subst (asm) bmerge_sbrt_efilter_split [symmetric])
    using Suc.prems(1) apply blast
    using assms(2) apply blast
    using Suc.prems(3) apply blast
    apply (subst sbdropch_tlen_eq)
    apply (subst (2 3) surj_scons [symmetric])
    using sb_channel_nempty apply blast
    apply simp
    using Suc.prems(3) apply blast
    by simp
qed

lemma bmerge_efilter_leq:
  assumes "spf \<in> bMerge"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "#(efilter (\<lambda>(x, e). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(spf\<cdot>(sb::('cs::{echan,enum})\<^sup>\<Omega>)))) \<le> #(sb \<^enum> c)"
  using assms
proof (cases "#(sb \<^enum> c)")
  case (Fin n)
  then show ?thesis
    using assms(1)
  proof (induction n arbitrary: spf sb)
    case 0
    hence "#\<^sub>\<surd>sb = 0"
      by (metis Fin_02bot assms(2) less_le_trans lnless_def lnzero_def
          minimal sblen_min_len tlensmallerbundle)
    then show ?case
      by (simp add: bmerge_tlen_zero "0.prems"(2))
  next
    case (Suc n)
    have "#(sbRtTs\<cdot>sb \<^enum> c) \<le> #(srt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb \<^enum> c)))"
      by (simp add: sbrtts_sbgetch tsrt_srt_len)
    hence sbrtts_sbc_srt_leq: "#(sbRtTs\<cdot>sb \<^enum> c) \<le> #(srt\<cdot>(sb \<^enum> c))"
      apply (subst (2) sdrop_0 [symmetric])
      by (metis (no_types, lifting) sdrop_0 sdrop_forw_rt sdrop_smap slen_smap)
    have srt_sbc_len: "#(srt\<cdot>(sb \<^enum> c)) = Fin n"
      by (metis Fin_Suc Suc.prems(1) srtlen_lnsuc)
    then obtain k where k_def: "#(sbRtTs\<cdot>sb \<^enum> c) = Fin k" and "Fin k \<le> Fin n"
      apply (simp add: sbrtts_sbgetch)
      by (metis (no_types, lifting) leI less2nat_lemma lnat_well_h2 notinfI3 sbrtts_sbc_srt_leq sbrtts_sbgetch slen_smap trans_lnle)
    have sbc_nbot: "sb \<^enum> c \<noteq> \<epsilon>"
      by (metis Fin_Suc Suc.prems(1) lnat.con_rews lnzero_def slen_zero)
    have sbrtch_split_tick_leq: "shd (sb \<^enum> c) \<noteq> Timed (TLive Tick) \<Longrightarrow> #\<^sub>\<surd>sb > 0 \<Longrightarrow>
  #(efilter (\<lambda>(x, e). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(spf\<cdot>(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>(sb))))) \<le> #(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb \<^enum> c)"
      apply (rule Suc.IH)
      apply (simp add: sbhdts_getch sbrtts_sbgetch sbdropch_cheq_getch)
      apply (subst (2) sbgetch_insert2)
      apply (subst ticksb_insert)
      using assms(2) apply blast
      apply (subst slen_smap [where f="inv TLive \<circ> inv Timed", symmetric])
      apply (simp add: smap_split)
      apply (subst (1 3) smap_m2event_timedtlive_inv_eq [symmetric])
      apply (meson smap_sValues_range)+
      apply (subst smapsmap2smap, simp)
      apply (simp add: smapsmap2smap)
      apply (subst sdrop_smap [symmetric])
      apply (subst eshdts_sdrop [symmetric])
      apply (subst (3)surj_scons [symmetric])
      using sbc_nbot apply blast
      apply simp
      apply (cases "shd (sb \<^enum> c)" rule: tlive_cases)
      apply (rule rev_subsetD [where A="sValues\<cdot>(sb \<^enum> c)"])
      apply (metis Fin_02bot Suc.prems(1) Suc_neq_Zero leI lnle_Fin_0 lnzero_def snth2sValues snth_shd)
      apply (meson echan_svalues sbc_nbot sbgetch_empty)
      apply blast
      apply auto[1]
      apply (subst sdrop_smap [symmetric])
      apply (subst sdrop_split [symmetric])
      apply (subst (4) surj_scons [symmetric])
      using sbc_nbot apply blast
      apply (cases "shd (sb \<^enum> c)" rule: tlive_cases)
      apply (rule rev_subsetD [where A="sValues\<cdot>(sb \<^enum> c)"])
      apply (metis Fin_02bot Suc.prems(1) Suc_neq_Zero leI lnle_Fin_0 lnzero_def snth2sValues snth_shd)
      apply (meson echan_svalues sbc_nbot sbgetch_empty)
      apply blast
      apply (simp add: eshdts_event)
      apply (subst s_split [symmetric])
      apply (simp add: smap_sValues image_iff)
      apply (rule_tac x="Timed (TLive Tick)" in bexI, simp)
      apply (rule tlen_timedtlive_zero_gt)
      apply (meson assms(2) chdom_in echan_svalues)
      apply (meson assms(2) less_le_trans sbtlen_min_len)
      apply (metis \<open>#(srt\<cdot>((sb::'cs\<^sup>\<Omega>) \<^enum> (c::'cs))) = Fin (n::nat)\<close> sdrop_0 sdrop_forw_rt sdrop_smap slen_smap)
      using Suc.prems(2) by blast
    show ?case
      apply (cases "#\<^sub>\<surd>sb = 0")
      apply (simp add: "Suc.prems"(2) bmerge_tlen_zero)
      apply (subst bmerge_efilter_split)
      using Suc.prems(2) apply blast
      using Suc.prems(1) apply fastforce
      apply (metis Fin_0 dual_order.order_iff_strict less_linear lnle_Fin_0 neq02Suclnle order.strict_trans1)
      apply (simp add: sbhdts_getch)
      apply (subst (9) surj_scons [symmetric])
      using sbc_nbot apply blast
      apply (subst (5) sb_step)
      apply (metis assms(2) echan_svalues leI lnmin_eqasmthmin sbtlen_min_len strict_lnmin_snd tlen_timedtlive_zero_gt)
      apply (simp add: sbhdts_getch sbrtts_sbgetch)
      apply (subst (4) sbgetch_insert2)
      apply (simp add: assms ticksb_insert)
      apply (subst (24) surj_scons [symmetric])
      using sbc_nbot apply blast
      apply (cases "shd (sb  \<^enum> c)" rule: tlive_cases)
      apply (rule rev_subsetD [where A="sValues\<cdot>(sb \<^enum> c)"])
      apply (metis Fin_0 Fin_02bot Suc.prems(1) Zero_neq_Suc lnless_def minimal snth2sValues snth_shd)
      using echan_svalues sbc_nbot sbgetch_empty apply blast
      apply simp
      apply (subgoal_tac "#(efilter (\<lambda>(x::'cs, e::msg). x = c)\<cdot>
      (emap Rep_msgWithChan\<cdot>(spf\<cdot>(sbRtTs\<cdot>sb))))
    \<le> #(smap (Timed \<circ> TLive)\<cdot>(tsrt\<cdot>(smap (inv TLive \<circ> inv Timed)\<cdot>(sb  \<^enum>  c))))")
      apply simp
      apply (subst sbrtts_sbgetch [symmetric])
      apply (rule Suc.IH)
      apply (simp add: sbrtts_sbgetch)
      apply (subst (3) surj_scons [symmetric])
      using sbc_nbot apply blast
      apply simp
      using srt_sbc_len apply blast
      using Suc.prems(2) apply blast
      apply (simp add: eshdts_event)
      apply (subgoal_tac "#(efilter (\<lambda>(x, e). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(spf\<cdot>(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>(sb))))) \<le> #(sbHdTs\<cdot>(sbRtCh c\<cdot>sb) \<Zcat>\<^sup>\<Omega> ticksb \<Zcat>\<^sup>\<Omega> sbRtTs\<cdot>sb \<^enum> c)")
      apply (subst (asm) bmerge_sbrt_efilter_split)
      using Suc.prems(2) apply blast
      using assms(2) apply blast
      apply (metis lnless_def lnzero_def minimal)
      apply (subst sbdropch_tlen_eq)
      apply (subst (2 3) surj_scons [symmetric])
      using sbc_nbot apply blast
      apply simp
      apply (metis lnless_def lnzero_def minimal)
      apply (simp add: sbhdts_getch sbrtts_sbgetch sbdropch_cheq_getch)
      apply (subst (asm) (4) sbgetch_insert2)
      apply (simp add: assms ticksb_insert)
      apply (metis (no_types, lifting) sdrop_0 sdrop_forw_rt timed_tlive_event_smap_id)
      by (metis bot_is_0 lnless_def m2event.simps(1) minimal not_Event_eq sbrtch_split_tick_leq)
  qed
next
  case Inf'
  then show ?thesis
    using inf_ub by presburger
qed

lemma bmerge_prefwell[simp]:assumes"spf \<in> bMerge"
  shows"uSplit\<cdot>(spf\<cdot>sb) \<sqsubseteq> sb"
  apply (cases "chDomEmpty TYPE('a)")
  apply (metis (full_types) below_refl sb_empty_eq)
  apply(rule sb_belowI)
  apply(simp add: sbgetch_insert2)
  apply(simp add: uSplit.rep_eq eventFilter_def toM.simps)
  apply (cases "#\<^sub>\<surd>sb = 0")
  apply (simp add: assms bmerge_tlen_zero)
  apply(rule sbelowI)
  apply simp_all
  apply (subst sbgetch_insert2 [symmetric])
  apply (rule ssplit_prefix_snth_h)
  using assms apply blast
  apply blast
  apply (metis bot_is_0 lnless_def minimal)
  apply simp
  apply (subst sbgetch_insert2 [symmetric])
  by (simp add: bmerge_efilter_leq assms)

section\<open>@{const bMerge} behavior for empty channel sets\<close>

lemma bmerge_cemptywell[simp]:
  assumes"spf \<in> bMerge"
  and "chDom TYPE('cs) = {}"
shows"spf\<cdot>(\<bottom>::'cs::{echan,enum}\<^sup>\<Omega>) = ((\<up>Tick)\<^sup>\<infinity>)"
proof-
  obtain mergesem where spf_def:"spf = emap Abs_msgWithChan oo outconv oo mergesem oo convertSem oo inconv"
  and sem_in_mergesem: "mergesem \<in> mergeSem"
    using assms bMerge_def by blast
  then show ?thesis
    by (simp add: assms outconv_def emap_def)
qed

text\<open>@{const bMerge} is a refinement of @{const mergeTimed}\<close>
lemma bmergerefbundlemerge:
  "bMerge \<subseteq> mergeTimed"
  apply auto[1]
  apply(rule bundlemerge_rule)
  by simp_all

lemma bMergeRefBundleMergeId:
  assumes "\<not> is_singleton(chDom TYPE('cs))"
  shows "(bMerge::('cs::{echan,enum} sb \<rightarrow> ('cs) msgWithChan event stream) set) \<subseteq> mergeTimedId"
  unfolding mergeTimedId_def 
  using assms bmergerefbundlemerge 
  by auto

lemma bmergenotempty:"bMerge \<noteq> {}"
  apply(simp add: bMerge_def mergeSem_def)
  by (simp add: sem_notempty)

lemma bundlemergenotempty:
"(mergeTimed::('cs::{echan,enum} sb \<rightarrow> 'cs msgWithChan event stream) set) \<noteq> {}"
  using bmergerefbundlemerge bmergenotempty by blast

lemma bundlemergeidnotempty:
"(mergeTimedId::('cs::{echan,enum} sb \<rightarrow> 'cs msgWithChan event stream) set) \<noteq> {}"
  using bMergeRefBundleMergeId bmergenotempty bMergeRefBundleMergeId ifSingletonNotEmptyId
  apply (cases "is_singleton (chDom (TYPE ('cs)))")
  by auto

context eventGen
begin

lemma bmergerefsem: 
  assumes "\<not> is_singleton(chDom TYPE('in))"
  shows "(bMerge \<then> eSem (eaut p)) \<subseteq> Sem p"
  apply (simp add: Sem_def)
  apply (rule seqcomp_subset, simp_all)
  using assms bMergeRefBundleMergeId
  by auto

lemma sem_nempty: "Sem p \<noteq> {}"
  apply (simp add: Sem_def)
  apply (rule seqcomp_nempty)
  using bundlemergeidnotempty apply blast
  by (simp add: eSem_def sem_notempty)

end
declare tlen_len_eq[simp]

end