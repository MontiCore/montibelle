theory BundleMergeExec
  imports BundleMergeTs
          eventcomponent.EventAutomatonExec bundle.SBCodegen
begin


definition execMergeSem::"seed \<Rightarrow> ('a::countable list list stream \<rightarrow> 'a list stream)" where
"execMergeSem seed = execSem (execToDa (listToExec mergeAut) seed)"

lemma [ccode]:"execMergeSem seed\<cdot>s = (execSem (execToDa (listToExec mergeAut) seed))\<cdot>s"
  by(simp add: execMergeSem_def)

lemma execmergesem_mergesem:
  "execMergeSem seed \<in> mergeSem"
  by (simp add: execMergeSem_def execSem_def mergeSem_def)

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

lemma eventwellstream_eqI:
  assumes"Rep_eventwellstream s1 = Rep_eventwellstream s2"
  shows "s1 =s2"
  using assms Rep_eventwellstream_inject by auto
setup_lifting type_definition_eventwellstream


definition ews2ees::"'cs::{chan,countable} eventwellstream \<Rightarrow> 'cs msgWithChan event stream" where
"ews2ees = (\<lambda>s. emap Abs_msgWithChan\<cdot>( Rep_eventwellstream s))"

lift_definition ees2ews::" 'cs msgWithChan event stream \<Rightarrow> 'cs::{chan,countable} eventwellstream" is
"(\<lambda>s. emap Rep_msgWithChan\<cdot>(efilter (\<lambda>e. well (Rep_msgWithChan e))\<cdot>s))"
proof auto
  fix stream::"'cs msgWithChan event stream" and a::'cs and b::msg
  have "(a, b) \<in> eValues\<cdot>(emap Rep_msgWithChan\<cdot>(efilter (\<lambda>e::'cs msgWithChan. well (Rep_msgWithChan e))\<cdot>stream)) \<longrightarrow> well (a, b)"
  proof(induction stream)
    case adm
    then show ?case 
      apply(rule adm_imp,simp_all)
      apply(rule admI)
      by(simp add: contlub_cfun_arg lub_eq_Union)
  next
    case bottom
    then show ?case 
      by simp
  next
    case (step c stream)
    then show ?case
      apply auto[1]
      apply(cases c,simp_all)
      by(case_tac "well (Rep_msgWithChan aa)",simp_all)
  qed
  thus "(a, b) \<in> eValues\<cdot>(emap Rep_msgWithChan\<cdot>(efilter (\<lambda>e::'cs msgWithChan. well (Rep_msgWithChan e))\<cdot>stream)) \<Longrightarrow> well (a, b)"
    by auto
qed

lemma "ees2ews o ews2ees = id"
  apply(rule fun_eqI)
  apply(rule eventwellstream_eqI)
  apply(simp)
  apply(simp add: ees2ews.rep_eq ews2ees_def)
  oops

lemma assumes "chDom TYPE('a::{chan,countable}) \<noteq> {}"
  shows"ews2ees o ees2ews = (id::'a msgWithChan event stream \<Rightarrow> 'a msgWithChan event stream)"
  apply(rule fun_eqI)
  apply(induct_tac x,simp_all)
  apply(simp add: ews2ees_def ees2ews.rep_eq)+
  apply(case_tac a,simp_all)
  apply(subgoal_tac "well (Rep_msgWithChan aa)")
  by (simp add: Rep_msgWithChan_inverse assms)+

lemma assumes "chDom TYPE('a::{chan,countable}) = {}"
  shows"ews2ees (ees2ews (s::'a msgWithChan event stream)) = sfilter {Tick}\<cdot>s"
  apply(induction s)
  apply(simp add: ews2ees_def ees2ews.rep_eq)+
  apply(case_tac a,simp_all)
  apply(subgoal_tac "\<not>well (Rep_msgWithChan aa)")
  by (simp add: Rep_msgWithChan_inverse assms)+
  
typedef 'cs::"{countable,chan}" listwellstream ="{s::('cs\<times>msg) list stream | s. \<forall>e\<in>\<Union>(set ` sValues\<cdot>s). well e}"
  apply auto[1]
  by(rule_tac x=\<epsilon> in exI,simp)
  
setup_lifting type_definition_listwellstream

lift_definition outconv2::"('cs::{echan,countable} tstimed) listwellstream \<Rightarrow> 'cs eventwellstream"is
"\<lambda>s. (emap (\<lambda>(c,e). (tstimedToOrigin c,e))\<cdot>(sListToEvent\<cdot>s))"
proof auto
  fix stream::"('cs tstimed \<times> msg) list stream" and a::'cs and b::msg
  assume a1:"\<forall>y::('cs tstimed \<times> msg) list\<in>sValues\<cdot>stream. \<forall>x::'cs tstimed \<times> msg\<in>set y. well x"
  have"(a, b) \<in> eValues\<cdot>(emap (\<lambda>(c::'cs tstimed, y::msg). (tstimedToOrigin c, y))\<cdot>(sListToEvent\<cdot>stream)) \<longrightarrow> well (a,b)"
    using a1
  proof(induction stream)
    case adm
    then show ?case
      apply(simp add: split_beta')
      apply (rule adm_imp)
      apply(rule admI)
      apply(simp add: contlub_cfun_arg lub_eq_Union)
      apply(rule adm_imp,simp_all)
      apply(rule admI)
      by(simp add: contlub_cfun_arg lub_eq_Union)
  next
    case bottom
    then show ?case
      by simp
  next
    case (step c stream)
    then show ?case 
      apply simp
      apply(induction c)
      apply(simp)
      apply(case_tac aa,simp)
      by(case_tac aaa,simp)
  qed
  thus"(a, b) \<in> eValues\<cdot>(emap (\<lambda>(c::'cs tstimed, y::msg). (tstimedToOrigin c, y))\<cdot>(sListToEvent\<cdot>stream)) \<Longrightarrow> well (a, b)"
    by auto
qed

definition execBMerge::"seed \<Rightarrow> 'cs::{echan,enum} sb \<Rightarrow> ('cs) eventwellstream"where
"execBMerge seed = (\<lambda>sb. outconv2 (Abs_listwellstream (execMergeSem seed\<cdot>(convertSem\<cdot>(inconv\<cdot>sb)))))"

lemma [code]:"Rep_eventwellstream (execBMerge seed sb) =
(\<lambda>s. emap (\<lambda>(c,e). (tstimedToOrigin c,e))\<cdot>(sListToEvent\<cdot>s)) (execMergeSem seed\<cdot>(convertSem\<cdot>(inconv\<cdot>sb)))"
  apply(simp add: execBMerge_def outconv2.rep_eq)
  apply(subst Abs_listwellstream_inverse,auto)
  apply (rule convertsem_well [where sb="inconv\<cdot>sb"])
  by (metis (no_types, opaque_lifting) UN_iff execmergesem_mergesem mergesem_svalues)

lemma [ccodeAbs]:"Rep_lsb (inconv\<cdot>sb) =  (\<lambda>c. smap (Timed o TFin)\<cdot>(sEventToList\<cdot>(smap m2event\<cdot>(sb \<^enum> (tstimedToOrigin c)))))"
  by(simp add: inconv.rep_eq)

lemma [ccodeAbs]:"Rep_lsb (uSplit\<cdot>(s::'cs msgWithChan event stream)) = (if chDom TYPE ('cs::{echan,finite}) = {} then (\<lambda>c. sbot) else (\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>s)))))"
  apply(simp)
  apply(rule conjI)
  apply(simp add: uSplit.rep_eq)
  apply (metis Rep_lsb_strict app_strict)
  apply(rule impI)
  by(simp add: demerge_rep_eq)

lemma [code]:"Rep_cfun uSplit = uSplit_nc"
  by(simp add: uSplit_nc_def)


lemma [code]:"Rep_cfun (emap f) = Rep_cfun (smap (map_event f))"
  by(simp add: emap_def)

lemma execbmerge_bmerge_ref:"Rep_eventwellstream o execBMerge seed \<in> (\<lambda>f sb. emap Rep_msgWithChan\<cdot>(f sb)) ` (Rep_cfun) ` bMerge"
  apply(auto simp add: execBMerge_def bMerge_def)
  oops

lemma[code]:"Rep_lsb bot_nc = (\<lambda>c. bot_nc)"
  by (metis botnc_eq_bot sbbot_getch sbgetch_insert2)

end