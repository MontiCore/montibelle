theory GeneralBundleMerge

imports bundle.SBFin bundle.MsgWithChan
  stream.EventStream inc.Causality sps.SPS
begin

default_sort type



fun toM::"timeType \<Rightarrow>msg event stream \<rightarrow> M stream"where
"toM TUntimed  = smap Untimed oo e2ustream"|
"toM TTFin  = smap (Timed o TFin) oo sEventToList"|
"toM TTLive = smap (Timed o TLive)" |
"toM _ = undefined"

fun toMsg::"timeType \<Rightarrow>msg event stream \<rightarrow> msg combinedstream"where
"toMsg TUntimed  = (Abs_cfun UNTIMED) oo e2ustream"|
"toMsg TTFin  = (Abs_cfun TSLICED) oo sEventToList"|
"toMsg TTLive = Abs_cfun TEVENT" |
"toMsg _ = undefined"
declare toM.simps [simp del]

lemma tom_eps[simp]:
    fixes c::"'chan::mult_msg_chan"
  assumes "chDom TYPE('chan) \<noteq> {}"
  shows "toM (cTime (Rep c))\<cdot>\<epsilon> = \<epsilon>"
  apply(cases "cTime (Rep c)")
  using mult_msg_chan_ctime2[OF assms] toM.simps apply auto[5]
  apply (metis timeType.distinct(1) timeType.distinct(11) timeType.distinct(9))
  by (metis timeType.distinct(17) timeType.distinct(19) timeType.distinct(7))
    
lemma tom_well[simp]:
  fixes c::"'chan::{mult_msg_chan, countable}"
  assumes "chDom TYPE('chan) \<noteq> {}"
    and "eValues\<cdot>s \<subseteq> cMsg (Rep c)"
  shows "sValues\<cdot>(toM (cTime (Rep c))\<cdot>s) \<subseteq> ctype (Rep c)"
  apply(subgoal_tac "(cTime (Rep c)) \<in> {TUntimed, TTFin, TTLive}")

   apply(cases "(cTime (Rep c))")
      apply (simp_all add: assms smap_sValues image_iff ctype_def toM.simps)
    apply(simp add:  eValues_def[symmetric] cfcomp2[symmetric])
  using assms(2) apply blast
   apply(rule image_mono)
  using assms(2) stimedtolist_well svalues_evalues apply fastforce
  using assms(2) stimedtolist_well svalues_evalues apply fastforce

  by (metis assms(1) empty_iff insert_iff mult_msg_chan_ctime2)


lemma fixes c::"'cs::{tchan,mult_msg_chan}"
  assumes "chDom TYPE('cs) \<noteq> {}"
  shows "#\<^sub>\<surd> ((toM (cTime (Rep c)))\<cdot>s) = #\<^sub>\<surd>s"
  apply(cases "(cTime (Rep c))"; simp)
  using assms tchan_class.sometschan apply blast 
     apply (metis mult_msg_chan_ctime2 assms emptyE insert_iff timeType.distinct(1) timeType.distinct(11) timeType.distinct(9))
    apply(simp add: toM.simps) 
    apply(induction s; simp?)
  apply(intro adm_imp, simp)
  oops

definition eventFilter:: "'cs \<Rightarrow> 'cs::{countable,chan} msgWithChan event stream \<rightarrow> msg event stream" where
"eventFilter c = (emap snd) oo (efilter (\<lambda>(ch,m). ch=c)) oo (emap Rep_msgWithChan)"

lemma eventfilter_eps[simp]: "eventFilter c\<cdot>\<epsilon>= \<epsilon>"
  and eventfilter_tick[simp]: "eventFilter c\<cdot>(\<up>Tick \<Zcat> s) = \<up>Tick \<Zcat> (eventFilter c\<cdot>s)"
  and eventfilter_tickf[simp]: "eventFilter c\<cdot>(\<up>Tick) = \<up>Tick"
  and eventfilter_in [simp]: "fst(Rep_msgWithChan m) = c \<Longrightarrow> 
        eventFilter c\<cdot>(\<up>(EventMsg m) \<Zcat> s) = \<up>(EventMsg (snd(Rep_msgWithChan m))) \<Zcat> (eventFilter c\<cdot>s)"
  and eventfilter_inf [simp]: "fst(Rep_msgWithChan m) = c \<Longrightarrow> 
        eventFilter c\<cdot>(\<up>(EventMsg m)) = \<up>(EventMsg (snd(Rep_msgWithChan m)))"
  and eventfilter_notin[simp]:"fst(Rep_msgWithChan m) \<noteq> c \<Longrightarrow> 
        eventFilter c\<cdot>(\<up>(EventMsg m) \<Zcat> s) = (eventFilter c\<cdot>s)"
  and eventfilter_notinf[simp]:"fst(Rep_msgWithChan m) \<noteq> c \<Longrightarrow> 
        eventFilter c\<cdot>(\<up>(EventMsg m)) = \<epsilon>"
  by (auto simp add: eventFilter_def case_prod_beta)


lemma eventfilter_well[simp]:
  fixes c::"'chan::{chan, countable}"
  assumes "chDom TYPE('chan) \<noteq> {}"
  shows "eValues\<cdot>(eventFilter c\<cdot>s) \<subseteq> cMsg (Rep c)"
  apply(induction s; simp?)
  apply(rename_tac msg s, case_tac msg; simp)
  apply(rename_tac msgWithCh)
  apply(case_tac "fst (Rep_msgWithChan msgWithCh) = c"; simp)
  using repincMsg2 by (metis assms(1) prod.collapse)

lemma eventfilter_typecast: 
  assumes "chDom (TYPE ('csSmall)) \<subseteq> chDom (TYPE ('csGreat))"
    and "eValues\<cdot>s \<subseteq> {x | x. Rep (fst (Rep_msgWithChan x)) \<in> chDom (TYPE ('csSmall))}" 
  shows  "(eventFilter c)\<cdot>
            ((emap (ewcTypeCast::'csGreat::{chan,countable} msgWithChan \<Rightarrow> 'csSmall::{chan,countable} msgWithChan))\<cdot>
              s) 
          = (eventFilter (Abs (Rep c))\<cdot>s)"
  using assms(2) apply(induction s, simp)
  apply simp
  apply(case_tac a; simp)
  apply(rename_tac msg)
  apply(case_tac "Rep (fst(Rep_msgWithChan msg)) = (Rep c)")

   apply(subst eventfilter_in, subst ewctypecast_rep; simp add: assms)
   apply(subst eventfilter_in, metis abs_rep_id)
   apply(subst ewctypecast_rep; simp add: assms)

  apply(subst eventfilter_notin, subst ewctypecast_rep; simp add: assms)
  apply force
  apply(subst eventfilter_notin)
  apply (metis assms(1) chdom_in emptyE rep_reduction_alt subset_eq)
  by auto


lemma eventfilter_efilter:
  assumes ch_ref:  "Rep c \<in> chDom (TYPE ('csSmall::chan))" 

  shows "(eventFilter (((c::'csGreat::{chan,countable}))))\<cdot>
         ((efilter (\<lambda>(x::'csGreat::{chan,countable} msgWithChan). ((Rep (fst (Rep_msgWithChan x))) \<in> (chDom TYPE('csSmall)))))\<cdot>
          s) = 
  eventFilter c\<cdot>s"
  apply(induction s; simp?)
  apply(case_tac a; simp)
  apply(rename_tac msg, 
      case_tac "(Rep (fst (Rep_msgWithChan msg))) \<in> (chDom TYPE('csSmall))"; simp?
   ; case_tac "(Rep (fst (Rep_msgWithChan msg))) = (Rep c)"; simp?)
     apply (metis eventfilter_in eventfilter_notin)
    apply (metis  eventfilter_notin)
  using ch_ref apply blast
  by (metis eventfilter_notin)


lemma usplit_well[simp]:
  assumes "chDom TYPE('chan::{mult_msg_chan, countable}) \<noteq> {}"
  shows "lsb_well (\<lambda>c::'chan. toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s))"
  apply(rule lsbwellI)
  apply(intro tom_well eventfilter_well; simp add: assms)
  done


lift_definition uSplit::"'cs::{countable,mult_msg_chan} msgWithChan event stream \<rightarrow> 'cs sb" is
"\<lambda> s. if chDom TYPE ('cs) = {}
                  then \<bottom> 
                  else Abs_lsb(\<lambda>c. toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s))"
  apply(cases "chDomEmpty TYPE('cs)";simp add: cfun_def)
  apply(rule Cpo.contI2)
  apply(rule monofunI)
  apply(rule sb_belowI)
   apply(simp add: sbgetch_insert2)
   apply (simp add: monofun_cfun_arg)
  by (simp add: contlub_cfun_arg contlub_cfun_fun contlub_lambda lub_lsb)

lemma demerge_bot[simp]:"uSplit\<cdot>(\<epsilon>::('cs::{countable,mult_msg_chan} msgWithChan event stream)) = \<bottom>"
  by(simp add: uSplit.rep_eq bot_sb eventFilter_def toM.simps)

lemma usplit_insert:
   shows "Rep_lsb (uSplit\<cdot>s) = (if chDom TYPE ('cs::{countable,mult_msg_chan}) = {} 
                  then \<bottom> else (\<lambda>c::'cs. toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s)))"
  apply(simp add: uSplit.rep_eq)
  using Rep_lsb_strict by blast
 
lemma rep_lsb2sbnew2legacy:
  assumes "sb_well f"
  shows "Rep_lsb (Abs_sb f) = sbnew2legacy (f)"
  apply(simp add: Rep_lsb_def)
  by(subst Abs_sb_inverse, simp_all add: assms)

lemma sEventToList_listValues_step:"listValues\<cdot>((sscanlA toListHelper ls\<cdot>s)) \<subseteq> set ls \<union> (listValues\<cdot>(sEventToList\<cdot>s))"
  apply(cases "Tick \<in> sValues\<cdot>s")
   apply(induction s arbitrary: ls rule: tslice_ind)
     apply(rule adm_imp,simp,rule adm_all,simp add: SetPcpo.less_set_def[symmetric], rule adm_below,simp_all)
  using union_cont cont_compose_mix
   apply (metis cont_Rep_cfun2 cont_compose)
  by (simp add: sEventToList_def sup.coboundedI2)

lemma combValues2eValues:
  assumes "tt \<in> {TUntimed, TTFin, TTLive}"
  shows"combValues\<cdot>(toMsg tt\<cdot>s) \<subseteq> eValues\<cdot>s"
  apply(induction s,simp)
  apply(cases tt)
  using assms valueleast[of tt] apply simp_all
  apply(cases tt;case_tac a,simp_all)
  apply blast
  apply(simp add: combValues_def combstreamcases_insert)
  using sEventToList_listValues_step list.simps(15) subset_iff apply fastforce
  by blast


lemma combgettime_tomsg:assumes"tt \<in> {TUntimed, TTFin, TTLive}"
  shows"combGetTime (toMsg tt\<cdot>s) =tt"
  apply(cases tt,simp_all)
  using assms by blast+

lemma usplit_abseq:
   shows "(uSplit\<cdot>s) = (if chDom TYPE ('cs::{countable,mult_msg_chan}) = {} 
                  then \<bottom> else Abs_sb(\<lambda>c::'cs. toMsg (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s)))"
  apply(rule sb_rep_eqI)
  apply(simp add: usplit_insert)
  apply rule
  apply(subst rep_lsb2sbnew2legacy) defer
   apply(simp add: sbnew2legacy_def combined2mstream_def combstreamcases_insert)
   apply(subgoal_tac "cTime (Rep c) \<in> {TUntimed, TTFin, TTLive}")
  apply auto[1]
      apply(simp_all add: toM.simps)
  using mult_msg_chan_ctime2
   apply blast
  apply(rule newsb_wellI)
  apply simp_all
  using combValues2eValues 
  apply (meson dual_order.trans eventfilter_well mult_msg_chan_ctime2)
  using combgettime_tomsg mult_msg_chan_ctime2 by blast

lemma usplit_insert2:
  assumes "Rep c \<in> chDom TYPE('cs::{mult_msg_chan,countable})"
  shows "(uSplit\<cdot>s) \<^enum> (c::'cs) = toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s)"
  apply(auto simp add: sbgetch_insert usplit_insert)[1]
  using assms by blast

lemma usplit_insert3:
  assumes "Rep c \<in> chDom TYPE('cs::{mult_msg_chan,countable})"
  shows "Rep_lsb (uSplit\<cdot>s) (c::'cs) = toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>s)"
  apply(auto simp add: sbgetch_insert usplit_insert)[1]
  using assms by blast


lemma usplit_conc:
  shows "(uSplit\<cdot>(\<up>msg \<Zcat> xs2)::'cs::{echan, countable}\<^sup>\<Omega>) = uSplit\<cdot>(\<up>msg) \<Zcat>\<Zcat> uSplit\<cdot>(xs2)"
  apply(rule sb_eqI)
  unfolding sbconc_getch_split usplit_insert2
  apply(simp)
  apply(cases msg; simp add: toM.simps)
  by (metis (no_types, lifting) eventfilter_in eventfilter_inf eventfilter_notin eventfilter_notinf sconc_fst_empty smap_split)

lemma usplit_conc_general:
  shows "(uSplit\<cdot>(\<up>msg \<Zcat> xs2)::'cs::{tchan,mult_msg_chan,countable}\<^sup>\<Omega>) = uSplit\<cdot>(\<up>msg) \<Zcat>\<Zcat> uSplit\<cdot>(xs2)"
  apply(rule sb_eqI)
  unfolding sbconc_getch_split usplit_insert2
  apply(simp)
  apply(cases msg; simp add: toM.simps)
  proof -
    fix c::"'cs::{tchan,mult_msg_chan,countable}" and a::"'cs msgWithChan"
    assume "Rep c \<in> chDom TYPE('cs)"

    then have cTimeDef: "cTime (Rep c) \<in> {TUntimed, TTFin, TTLive}"
      using mult_msg_chan_ctime by auto
      
    then show "toM (cTime (Rep c))\<cdot>(\<up>\<surd> \<Zcat> eventFilter c\<cdot>xs2) =
       toM (cTime (Rep c))\<cdot>(\<up>\<surd>) \<Zcat> toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>xs2)"
      apply (cases "cTime (Rep c)")
      apply auto
      by (simp_all add: toM.simps)

    then show "toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>(\<up>(EventMsg a) \<Zcat> xs2)) =
       toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>(\<up>(EventMsg a))) \<Zcat> toM (cTime (Rep c))\<cdot>(eventFilter c\<cdot>xs2)"
      using cTimeDef
      apply (cases "cTime (Rep c)")
      apply auto
      apply (simp_all add: toM.simps)
      apply (metis (no_types, lifting) e2ustream_eps e2ustream_event e2ustream_eventend eventfilter_in eventfilter_inf eventfilter_notin eventfilter_notinf sconc_fst_empty smap_split)
      defer
      apply (metis (no_types, lifting) eventfilter_in eventfilter_inf eventfilter_notin eventfilter_notinf sconc_fst_empty smap_split)
      apply (cases "fst(Rep_msgWithChan a) = c")
      apply (simp_all add: sEventToList_def)
  oops
  

lemma ssplit_sbgetch_tlen:
  assumes "\<not>chDomEmpty TYPE('a::{tchan,finite,mult_msg_chan})"
  shows "#\<^sub>\<surd>((uSplit\<cdot>s::'a\<^sup>\<Omega>) \<^enum> c) = #\<^sub>\<surd>s"
  apply (induction s)
  apply (rule adm_eq)
   apply (simp add: tlen_stream_def)
   apply (intro cont2cont)+
   apply simp
  apply(simp add: sbgetch_insert2 usplit_insert assms)
  apply (case_tac a; simp)
  oops


lemma usplit_tick_cast: 
  assumes "chDom TYPE('csSub) \<subseteq> chDom TYPE('csSuper)"
  shows "(uSplit\<cdot>(\<up>Tick)::'csSuper::{mult_msg_chan,countable}\<^sup>\<Omega>)\<star> 
        = (uSplit\<cdot>(\<up>Tick)::'csSub::{mult_msg_chan,countable}\<^sup>\<Omega>)"
  apply(rule sb_eqI, simp add: usplit_insert2)
  apply(auto simp add: sbgetch_insert)[1]
   apply(auto simp add: usplit_insert)[1]
  using assms by blast


lemma eventfilter_cast:
  assumes "chDom TYPE('csSub::{chan,countable}) \<subseteq> chDom TYPE('csSuper::{chan,countable})"
      and "Rep c \<in> chDom TYPE('csSub)"
    and "Rep (getChannel msg) \<in> chDom TYPE('csSub)"
  shows "eventFilter (Abs (Rep c))\<cdot>(\<up>(EventMsg msg)) 
      = eventFilter (c::'csSub)\<cdot>(\<up>(EventMsg (ewcTypeCast (msg::'csSuper msgWithChan))))"
  apply(cases "Rep (getChannel msg) = Rep c")
  apply(subst eventfilter_inf) 
    apply (metis abs_rep_id getChannel_def)
   apply(subst eventfilter_inf)
  apply(subst ewctypecast_rep,metis assms(3) getChannel_def)
  apply (simp add: getChannel_def)
  apply(subst ewctypecast_rep, metis assms(3) getChannel_def )
   apply simp

  apply(subst eventfilter_notinf)
  apply(simp add: getChannel_def)
  apply (metis assms(1) assms(2) in_mono rep_reduction)
  apply(subst eventfilter_notinf)
  apply(subst ewctypecast_rep,metis assms(3) getChannel_def )
  apply (metis assms(3) comp_def fst_apfst getChannel_def rep_reduction)
  ..

lemma usplit_cast_in:
  assumes  "chDom TYPE('csSub) \<subseteq> chDom TYPE('csSuper)"
    and "Rep (getChannel msg) \<in> chDom TYPE('csSub)"
  shows  "(uSplit\<cdot>(\<up>(EventMsg msg))::'csSuper::{mult_msg_chan,countable}\<^sup>\<Omega>)\<star>
        = (uSplit\<cdot>(\<up>(EventMsg (ewcTypeCast msg)))::'csSub::{mult_msg_chan,countable}\<^sup>\<Omega>)"
  apply(rule sb_eqI, simp add: usplit_insert2)
  apply(auto simp add: sbgetch_insert)[1]
   apply(auto simp add: usplit_insert3)[1]
   apply(rule cfun_arg_cong)
  using eventfilter_cast using assms apply blast
  using assms(1) by blast

lemma usplit_cast_notin:
  assumes "Rep (getChannel msg) \<notin>  chDom TYPE('csSub)"
  shows  "(uSplit\<cdot>(\<up>(EventMsg msg))::'csSuper::{mult_msg_chan,countable}\<^sup>\<Omega>)\<star>
        = (\<bottom>::'csSub::{mult_msg_chan,countable}\<^sup>\<Omega>)"
  apply(rule sb_eqI)
  apply(auto simp add: sbgetch_insert usplit_insert3)[1]
   apply(subst eventfilter_notinf,metis assms getChannel_def rep_reduction)
   apply (metis emptyE sbbot_getch sbgetch_insert2 tom_eps)
  by (simp add: Rep_lsb_strict)

lemma usplit_e_insert[simp]:
  fixes c::"'cs::{echan,countable}"
  assumes "getChannel msg = c" and "Rep c \<in> chDom TYPE('cs)"
  shows "((uSplit\<cdot>(\<up>(EventMsg msg))) \<^enum> c) = \<up>(Timed (TLive (EventMsg (getMsg msg))))"
  apply(subst usplit_insert2)
   apply (simp add: assms(2))
  apply (subst echan_ctime, simp add: assms(2))
  apply (simp add: toM.simps eventFilter_def )
  apply(subst efilter_P2)
   apply (metis (mono_tags, lifting) assms(1) getChannel_def split_beta)
  by (simp add: getMsg_def)

lemma usplit_e_insert_notin[simp]:
  fixes c::"'cs::{mult_msg_chan,countable}"
  assumes "getChannel msg \<noteq> c" and "Rep c \<in> chDom TYPE('cs)"
  shows "((uSplit\<cdot>(\<up>(EventMsg msg))) \<^enum> c) = \<epsilon>"
  apply(subst usplit_insert2)
   apply (simp add: assms(2))
  by (metis assms(1) assms(2) eventfilter_notinf ex_in_conv getChannel_def tom_eps)


definition mergeGen::"('cs::{mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set"where
"mergeGen = {f | f. \<forall>sb. uSplit\<cdot>(f\<cdot>sb) \<sqsubseteq> sb}"

definition mergeTimed::"('cs::{tchan,finite,mult_msg_chan} sb \<rightarrow> 'cs msgWithChan event stream) set" where
"mergeTimed= mergeGen 
  \<inter> {f| f. if chDom TYPE ('cs) = {} 
      then \<forall>sb. f\<cdot>sb = ((\<up>Tick)\<^sup>\<infinity>)
      else \<forall>sb. #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(f\<cdot>sb))}"

lemma mergeTimed_eq_len: 
  fixes spf::"'cs::{tchan,finite,mult_msg_chan} sb \<rightarrow> 'cs msgWithChan event stream"
  assumes "spf\<in>mergeTimed"
  shows "#\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(spf\<cdot>sb))"
  apply(cases "chDom TYPE ('cs) = {}")
  using assms by(simp add: mergeTimed_def)+

lemma mergeTimed_inftick[simp]: 
  assumes "chDom TYPE ('cs) = {}"
  shows "(mergeTimed::(('cs::{tchan,finite,mult_msg_chan} sb \<rightarrow> 'cs msgWithChan event stream) set))
             = {(\<Lambda> _. ((\<up>Tick)\<^sup>\<infinity>))}"
  using assms apply(auto simp add: mergeTimed_def)[1]
   apply(rule cfun_eqI, subst beta_cfun, intro cont2cont, simp)
  by(simp add: mergeGen_def uSplit_def)

lemma mergeTimed_usplit: assumes "spf\<in>mergeTimed"
  shows "uSplit\<cdot>(spf\<cdot>sb) \<sqsubseteq> sb"
  using assms by(simp add: mergeTimed_def mergeGen_def)

lemma mergetimed_insert_leg: "(mergeTimed::('cs::{tchan,finite,mult_msg_chan} sb \<rightarrow> 'cs msgWithChan event stream) set)
     = (if chDom TYPE ('cs::{tchan,finite,mult_msg_chan}) = {} then {f | f. \<forall>sb. f\<cdot>sb = ((\<up>Tick)\<^sup>\<infinity>)} 
                  else {f | f. \<forall>sb. uSplit\<cdot>(f\<cdot>sb) \<sqsubseteq> sb
                               \<and>    #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(f\<cdot>sb))})"
  apply(auto simp add: mergeTimed_def mergeGen_def)[1]
  using sb_belowI2 by blast

lemma mergetimed_in: 
  fixes spf::"'cs::{tchan,finite,mult_msg_chan}\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream"
  assumes "\<And>sb. chDom TYPE ('cs) = {} \<Longrightarrow> spf\<cdot>sb =  ((\<up>Tick)\<^sup>\<infinity>)"
    and "\<And>sb. chDom TYPE ('cs) \<noteq> {} \<Longrightarrow> uSplit\<cdot>(spf\<cdot>sb) \<sqsubseteq> sb" 
    and "\<And>sb. chDom TYPE ('cs) \<noteq> {} \<Longrightarrow> #\<^sub>\<surd>sb = #\<^sub>\<surd>(uSplit\<cdot>(spf\<cdot>sb))"
  shows "spf \<in> mergeTimed"
  unfolding mergetimed_insert_leg
  apply(simp add: assms(1))
  using assms(2) assms(3) by fastforce

lemma mergetimed_complete [simp]:"spsComplete mergeTimed = mergeTimed"
  apply(auto simp add: mergeTimed_def spsComplete_def)[1]
  apply (subst Int_Collect mergeGen_def mergeTimed_def mergeTimed_usplit)
  apply (simp add: mergeGen_def)
  apply (metis (no_types, lifting) Int_Collect mem_Collect_eq)
  by (metis (mono_tags, lifting) IntD2 empty_iff mem_Collect_eq)

definition mergeUntimed::"('cs::{uchan,finite,mult_msg_chan} sb \<rightarrow> 'cs msgWithChan stream) set" where
"mergeUntimed = (\<lambda>f. e2ustream oo f) ` mergeGen"



definition mergeTimedId::"('cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream) set" where
"mergeTimedId = mergeTimed \<inter> {f| f. if is_singleton (chDom TYPE('cs)) 
                               then (\<forall>sb. uSplit\<cdot>(f\<cdot>sb) = sb)
                               else True }"

lemma mergeIdInTimed: "mergeTimedId \<subseteq> mergeTimed" 
  unfolding mergeTimedId_def
  by auto

lemma mergeIdInGen: "mergeTimedId \<subseteq> mergeGen" 
  using mergeIdInTimed
  apply (subst (asm) mergeTimed_def)
  by auto

fun mapToMsgWithChan :: "'a::chan \<Rightarrow> M \<Rightarrow> 'a msgWithChan event" where
"mapToMsgWithChan cha (Timed (TLive (EventMsg x))) = EventMsg (Abs_msgWithChan (cha, x))" |
"mapToMsgWithChan cha (Timed (TLive Tick)) = Tick" |
"mapToMsgWithChan _ _ = undefined"

definition mergeIdFunc2:: "'cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream" where
"mergeIdFunc2 = (\<Lambda> sb. if is_singleton (chDom TYPE ('cs)) 
  then smap (mapToMsgWithChan (Abs(the_elem (chDom TYPE('cs)))))\<cdot>(sb \<^enum> (Abs(the_elem (chDom TYPE('cs)))))  
  else undefined
)"

lift_definition mergeIdFunc:: "'cs::{echan, mult_msg_chan,finite} sb \<rightarrow> 'cs msgWithChan event stream" is
"\<lambda>sb. if is_singleton (chDom TYPE ('cs)) 
  then smap (mapToMsgWithChan (Abs(the_elem (chDom TYPE('cs)))))\<cdot>(sb \<^enum> (Abs(the_elem (chDom TYPE('cs)))))  
  else undefined"
  by (intro cont2cont)+

lemma sbLenInSingletonSame:
  assumes "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"
  shows "\<And>(sb:: 'cs sb) (c::'cs). #sb = #(sb \<^enum> c)"
  using assms
proof -
  assume "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"
  then have domNotEmpty: "\<not> chDomEmpty TYPE('cs)"
    unfolding is_singleton_def by auto

  show "\<And>(sb:: 'cs sb) (c::'cs). #sb = #(sb \<^enum> c)"
    using assms
    by (metis (mono_tags, opaque_lifting) chan_single_eq domNotEmpty dual_order.refl sblen_rule)
  
qed

lemma mergeIdFuncUSplitId: 
  assumes "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"
  shows "\<And>input:: 'cs msgWithChan event stream . mergeIdFunc\<cdot>(uSplit\<cdot>input) = input"
  using assms
    proof -
      fix input::"'cs msgWithChan event stream"
      assume "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"

      then have domNotEmpty: "\<not> chDomEmpty TYPE('cs)"
        unfolding is_singleton_def by auto


      obtain c::'cs where cDef: "c = (Abs (the_elem (chDom TYPE('cs))))"
        by auto
      hence rep_c_in_dom: "Rep c \<in> chDom TYPE ('cs)"
        using domNotEmpty by auto
      hence cTimeDef: "cTime (Rep c) = TTLive"
        using echan_ctime by auto
      hence ctype_c: "ctype (Rep c) = (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"
        apply (auto simp add: ctype_def)    
        by (simp add: domNotEmpty)
  
      
      show "mergeIdFunc\<cdot>(uSplit\<cdot>input) = input"
        using assms
        unfolding mergeIdFunc_def apply auto
        apply (subst usplit_insert2[of "Abs (the_elem (chDom TYPE('cs)))" input])
        using cDef cTimeDef rep_c_in_dom apply auto
        apply (auto simp add: toM.simps)
        apply (subst smaps2smap) apply auto
        apply (induct_tac input)
        apply auto
        apply (case_tac a)
        apply auto
        apply (subst eventfilter_in)
        using chan_single_eq apply blast
        by (metis (mono_tags, lifting) Rep_msgWithChan_inverse chan_single_eq mapToMsgWithChan.simps(1) prod.collapse smap_split smap_sup)
    qed

lemma [simp]: "is_singleton (chDom TYPE('cs::{echan, finite})) \<Longrightarrow> (mergeIdFunc\<cdot>(\<bottom>::'cs sb) = \<epsilon>)"
  unfolding mergeIdFunc_def
  by auto

lemma mergeIdFuncFulfillsId: 
  assumes "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"
  shows "\<forall>sb::'cs\<^sup>\<Omega>. uSplit\<cdot>(mergeIdFunc\<cdot>sb) = sb"
  using assms apply auto
  proof -
    fix sb :: "'cs\<^sup>\<Omega>"
    assume "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"

    hence domNotEmpty: "\<not> chDomEmpty TYPE('cs)"
      unfolding is_singleton_def by auto

    have "\<And>(sb:: 'cs sb) (c::'cs). #sb = #(sb \<^enum> c)"
      using assms sbLenInSingletonSame by auto

    then have "\<And>(sb::'cs\<^sup>\<Omega>) c. #sb = 0 \<Longrightarrow> #(sb \<^enum> c) = 0"
      by simp
    then have "\<And>(sb::'cs\<^sup>\<Omega>). #sb = 0 \<Longrightarrow> (\<forall>c. (sb \<^enum> c = \<epsilon>))"
      by simp

    then have empty: "\<And>sb::'cs\<^sup>\<Omega>. #sb = 0 \<Longrightarrow> sb = \<bottom>"
      by (meson sbbot_getch)
    hence "mergeIdFunc\<cdot>(\<bottom>::'cs sb) = \<epsilon>"
      unfolding mergeIdFunc_def
      by (auto simp add: assms)
    hence mergeIdEmpty: "\<And>sb::'cs\<^sup>\<Omega>. #sb = 0 \<Longrightarrow> mergeIdFunc\<cdot>sb = \<epsilon>"
      using empty by auto
  
    
    obtain c::'cs where cDef: "c = (Abs (the_elem (chDom TYPE('cs))))"
      by auto
    hence rep_c_in_dom: "Rep c \<in> chDom TYPE ('cs)"
      using domNotEmpty by auto
    hence cTimeDef: "cTime (Rep c) = TTLive"
      using echan_ctime by auto
    hence ctype_c: "ctype (Rep c) = (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"
      apply (auto simp add: ctype_def)    
      by (simp add: domNotEmpty)
  
  
    have sbeconc: "\<And>(sbe::'cs\<^sup>\<surd>) (sb:: 'cs sb). ((sbe2sb sbe) \<Zcat>\<Zcat> sb) = (sbe \<Zcat>\<^sup>\<surd> sb)"
        by (simp add: conc_sb_def)
  
    
    have mergeIdIS: "\<And>(sbe::'cs\<^sup>\<surd>) (sb:: 'cs sb).
      mergeIdFunc\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = 
      \<up>((mapToMsgWithChan c) (sbegetch c sbe)) \<Zcat> mergeIdFunc\<cdot>(sb)"
    proof -
      fix sbe::"'cs\<^sup>\<surd>" and sb:: "'cs sb"
      have sbeGetEq: "(sbe2sb sbe) \<^enum> c = \<up>(sbegetch c sbe)"
        by (simp add: domNotEmpty sbe2sb_getch)
      hence "smap (mapToMsgWithChan c)\<cdot>((sbe2sb sbe  \<^enum> c) \<Zcat> sb  \<^enum>  c) 
      = \<up>(mapToMsgWithChan c (sbegetch c sbe)) \<Zcat> smap (mapToMsgWithChan (c))\<cdot>(sb  \<^enum>  c)"
        by auto
      thus "mergeIdFunc\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = 
      \<up>((mapToMsgWithChan c) (sbegetch c sbe)) \<Zcat> mergeIdFunc\<cdot>(sb)"
        unfolding mergeIdFunc_def by (simp add: assms cDef)
        
    qed
       
  
    have uSplitSbe: "\<And>(sbe::'cs\<^sup>\<surd>). uSplit\<cdot>(\<up>((mapToMsgWithChan c) (sbegetch c sbe))) = sbe2sb sbe"
      unfolding uSplit.rep_eq apply (auto simp add: domNotEmpty)
      unfolding toM.simps mapToMsgWithChan.simps
      proof -
        fix sbe::"'cs\<^sup>\<surd>"
        have sbeWell: "sbElem_well (Rep_sbElem sbe)"
          using Rep_sbElem[of sbe] by auto
        hence "the (Rep_sbElem sbe) c \<in> ctype(Rep c)"
          by (metis domNotEmpty option.collapse sbElem_well.simps(2) sbenotnone)
        hence candidates: "the (Rep_sbElem sbe) c \<in> (Timed \<circ> TLive) ` ({\<surd>} \<union> EventMsg ` cMsg (Rep c))"
          using ctype_c by auto
  
        have notNone: "Rep_sbElem sbe \<noteq> None"
          using domNotEmpty by auto
  
        have allC: "\<And>d::'cs. d = c"
          using cDef assms chan_single_eq by auto
          
        show "Abs_lsb (\<lambda>ca::'cs. smap (Timed \<circ> TLive)\<cdot>(eventFilter ca\<cdot>(\<up>(mapToMsgWithChan c (sbegetch c sbe))))) =
           sbe2sb sbe"
          unfolding sbegetch_def apply (auto simp add: rep_c_in_dom)
          using candidates apply auto
          unfolding sbe2sb_def apply auto
          using notNone apply auto
          apply (metis (full_types) assms chan_single_eq)
          apply (subst allC)
          proof -
            fix xa :: msg and y::"'cs \<Rightarrow> M"
            assume yc_def: "y c = Timed (TLive (EventMsg xa))" 
            and "xa \<in> cMsg (Rep c)" 
            and "Rep_sbElem sbe = Some y"
  
            hence "well (c, xa)"
              unfolding well_def by simp
            hence "Rep_msgWithChan (Abs_msgWithChan (c, xa)) = (c,xa)"
              using Abs_msgWithChan_inverse2 by auto
            thus "Abs_lsb (\<lambda>ca::'cs. smap (Timed \<circ> TLive)\<cdot>(eventFilter c\<cdot>(\<up>(EventMsg (Abs_msgWithChan (c, xa)))))) 
                  = Abs_lsb (\<lambda>c::'cs. \<up>(y c))"
              using eventfilter_in[of "Abs_msgWithChan (c, xa)" c] yc_def apply auto
              apply (subst allC) by simp
          qed
      qed
      
  
    have "\<And>(sbe::'cs\<^sup>\<surd>) (sb:: 'cs sb) msg. 
      uSplit\<cdot>(\<up>(msg:: 'cs msgWithChan event) \<Zcat> mergeIdFunc\<cdot>(sb)) 
      = uSplit\<cdot>(\<up>(msg)) \<Zcat>\<Zcat> uSplit\<cdot>(mergeIdFunc\<cdot>(sb))"
      using usplit_conc by auto
  
    hence "\<And>(sbe::'cs\<^sup>\<surd>) (sb:: 'cs sb). uSplit\<cdot>(mergeIdFunc\<cdot>sb) = sb \<Longrightarrow>
      uSplit\<cdot>(\<up>((mapToMsgWithChan c) (sbegetch c sbe)) \<Zcat> mergeIdFunc\<cdot>(sb)) 
      = sbe2sb sbe \<Zcat>\<Zcat> sb"
      using uSplitSbe by auto
  
    hence uSplitIS: "\<And>(sbe::'cs\<^sup>\<surd>) (sb:: 'cs sb). uSplit\<cdot>(mergeIdFunc\<cdot>sb) = sb \<Longrightarrow>
      uSplit\<cdot>(\<up>((mapToMsgWithChan c) (sbegetch c sbe)) \<Zcat> mergeIdFunc\<cdot>(sb)) 
      = sbe \<Zcat>\<^sup>\<surd> sb"
      using sbeconc by simp
    hence IS: "\<And>(sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>.
         uSplit\<cdot>(mergeIdFunc\<cdot>sb) = sb \<Longrightarrow>
         uSplit\<cdot>(mergeIdFunc\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb)) = sbe \<Zcat>\<^sup>\<surd> sb"
      using mergeIdIS by auto
    
    show "uSplit\<cdot>(mergeIdFunc\<cdot>sb) = sb"
      apply (induction sb)
      apply (auto simp add: assms domNotEmpty)
      apply (auto simp add:  mergeIdEmpty empty)
      using IS by auto
  qed



lemma mergeIdFuncInMergeTimedId: 
  assumes "is_singleton(chDom TYPE('cs::{echan,mult_msg_chan,finite}))"
  shows "mergeIdFunc \<in> (mergeTimedId:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set)"
using assms
proof -
  
  assume isSingleton: "is_singleton(chDom TYPE('cs::{echan, mult_msg_chan,finite}))"

  hence domNotEmpty: "\<not> chDomEmpty TYPE('cs)"
    unfolding is_singleton_def by auto

  have lenEqual: "\<forall>sb::'cs\<^sup>\<Omega>. #\<^sub>\<surd> sb = #\<^sub>\<surd> (uSplit\<cdot>(mergeIdFunc\<cdot>sb))"
    using isSingleton apply auto
    using mergeIdFuncFulfillsId
    by metis
    
  have "\<forall>sb::'cs\<^sup>\<Omega>. uSplit\<cdot>(mergeIdFunc\<cdot>sb) \<sqsubseteq> sb"
    using isSingleton apply auto
    using mergeIdFuncFulfillsId
    by fastforce
    
  hence "mergeIdFunc \<in> (mergeGen:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set)"
    unfolding mergeGen_def by simp
  
  hence "mergeIdFunc \<in> (mergeTimed:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set)"
    unfolding mergeTimed_def apply auto
    using domNotEmpty lenEqual by auto

  thus "mergeIdFunc \<in> (mergeTimedId:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set)"
    unfolding mergeTimedId_def
    using isSingleton mergeIdFuncFulfillsId by simp

qed

lemma ifSingletonNotEmptyId:
  assumes "is_singleton(chDom TYPE('cs::{echan, mult_msg_chan,finite}))"
  shows "(mergeTimedId:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set) \<noteq> {}"
  using assms
proof -
  
  assume "is_singleton(chDom TYPE('cs::{tchan, echan, mult_msg_chan,finite}))"

  have "\<exists>f. f \<in> (mergeTimedId:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set)" 
    apply (rule_tac x=mergeIdFunc in exI)
    using mergeIdFuncInMergeTimedId assms by auto

  thus "(mergeTimedId:: ('cs\<^sup>\<Omega> \<rightarrow> 'cs msgWithChan event stream) set) \<noteq> {}"
    by auto
qed


end