theory bundlemerge_test_add_channel

imports bundle_button bundle_button_mintime
      eventcomponent.BundleMerge eventcomponent.EventAutomaton_AddChannel
      sps.SPS
begin
default_sort type

lemma echan_tick_in_type: assumes "Rep c \<in> chDom TYPE('cs2::echan)"
  shows "Timed (TLive Tick) \<in> ctype (Rep c)"
  apply(cases "cTime (Rep c)")
      apply (metis assms echan_ctime rep_reduction_alt timeType.distinct)
     apply (metis assms echan_ctime rep_reduction_alt timeType.distinct)
    apply (metis assms echan_ctime rep_reduction_alt timeType.distinct)
  defer
  apply (metis assms echan_ctime rep_reduction_alt timeType.distinct)
  apply(simp add: ctype_def) 
  by (metis assms ctype_empty_iff dom2ctypenempty empty_iff rep_reduction_alt)




lemma helper[simp]:assumes"\<And>x. x\<in>sValues\<cdot>s \<Longrightarrow> x=y"
  shows "s \<sqsubseteq> ((\<up>y)\<^sup>\<infinity>)"
  using assms proof(induction s)
  case adm
  then show ?case
    apply (rule adm_imp)
    apply auto
    apply(rule admI)
    by (meson in_mono sValues_chain2lub)
next
  case bottom
  then show ?case 
    by simp
next
  case (step a s)
  then have "a = y"
    by simp
  then show ?case
    apply simp
    apply(subst sinftimes_unfold)
    apply(rule monofun_cfun_arg)
    by (simp add:step.IH step.prems)
qed

lemma smapsvalues[simp]:"e\<in>sValues\<cdot>s \<Longrightarrow> f e\<in> sValues\<cdot>(smap f\<cdot>s)"
proof(induction s)
  case adm
  then show ?case
    apply(rule adm_imp,simp_all)
    apply(rule admI)
    by (metis in_mono sValues_chain2lub smap_sValues subset_image_iff)
next
  case bottom
  then show ?case
    by simp
next
  case (step a s)
  then show ?case
    by auto
qed

(*
lemma bundlemerge_ticksinf[simp]: assumes "\<And>c::'cs::{echan,finite}. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> sb \<^enum> c = ((\<up>(Timed (TLive Tick)))\<^sup>\<infinity>)"
    and "merge \<in> mergeTimed"
  shows "merge\<cdot>sb = ((\<up>((Tick)))\<^sup>\<infinity>)"
  apply(insert assms)
  apply(auto simp add: bundlemerge_alt_eq[symmetric] mergeTimed_alt_def )
  apply(cases "chDomEmpty TYPE('cs)"; simp)
proof(rule ccontr)
  assume onlyticks:"(\<And>c::'cs. sb  \<^enum>  c = \<up>(Timed (TLive Tick))\<^sup>\<infinity>)"
  and bmerge:"\<forall>sb::'cs\<^sup>\<Omega>. (\<forall>c::'cs. smap (Timed \<circ> TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x::'cs, m::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(merge\<cdot>sb)))) \<sqsubseteq> sb  \<^enum>  c) \<and> #\<^sub>\<surd> sb = #\<^sub>\<surd> (merge\<cdot>sb)"
  and chdomnotempty:" chDom TYPE('cs) \<noteq> {}"
  and contr:"merge\<cdot>sb \<noteq> \<up>Tick\<^sup>\<infinity>"
  have svaluestick:"\<And>c::'cs. sValues\<cdot>(sb  \<^enum>  c) = {(Timed (TLive Tick))}"
    by(simp add: onlyticks)
  have "\<infinity> \<le> #\<^sub>\<surd> sb" apply(rule sbtlengeq', simp add: assms)
    by(rule steam_tlen_inf, simp)
  hence "#\<^sub>\<surd>sb = \<infinity>" by (meson inf_less_eq)
  hence "#\<^sub>\<surd>(merge\<cdot>sb) = \<infinity>" by(simp add: bmerge)
  hence "#(merge\<cdot>sb) = \<infinity>"
    by (metis eventlenleqlen inf_less_eq)
  then obtain x where x_def:"x\<in>sValues\<cdot>(merge\<cdot>sb) \<and> x \<noteq> Tick"
    by (meson contr eq_less_and_fst_inf helper)
  then obtain c msg where c_def:"(map_event Rep_msgWithChan) x = Event (c,msg)"
    by fastforce
  then have " Event (c,msg) \<in> sValues\<cdot>(emap Rep_msgWithChan\<cdot>(merge\<cdot>sb))"
    apply(subst(1) emap_def)
    by (metis rev_image_eqI smap_sValues x_def)
  then have "Event (c,msg) \<in> sValues\<cdot>(((efilter (\<lambda>(x::'cs, m::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(merge\<cdot>sb)))))"
    apply(subst efilter_def)
    by (rule sValues_sfilter2;simp)
  then have "Event (msg) \<in> sValues\<cdot>(emap snd\<cdot>((efilter (\<lambda>(x::'cs, m::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(merge\<cdot>sb)))))"
    apply(subst(1) emap_def;simp)
    using smapsvalues by (metis (mono_tags, lifting) event.simps(8) snd_eqD)
  then have "Timed (TLive (Event msg))\<in> sValues\<cdot>(smap (Timed \<circ> TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x::'cs, m::msg). x = c)\<cdot>(emap Rep_msgWithChan\<cdot>(merge\<cdot>sb)))))"
    by (metis comp_eq_dest_lhs smapsvalues)
  then have "Timed (TLive (Event msg))\<in> sValues\<cdot>(sb  \<^enum>  c)"
    using bmerge svalues_belowelem by blast
  thus "False"
    using svaluestick by auto
qed

lemma bundlemerge_after:
  fixes spfOld::"'csOld::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'csOld msgWithChan event stream"
  assumes "spfOld \<in> mergeTimed"
      and "chDom (TYPE('csNew::{echan,finite})) \<subseteq> chDom (TYPE('csOld))"
    shows "emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo spfOld
        oo sbFillWithTicks
          \<in> mergeTimed"
  apply(insert assms)
  apply(auto simp add: bundlemerge_alt_eq[symmetric] mergeTimed_alt_def )
    apply(cases "chDomEmpty TYPE('csOld)", auto)
     apply(simp add: efilter_def emap_def)
  sorry (* SSt: Ich weiß nicht, ob das Lemma hilft. eigentlich soll nur das unten bewiesen werden
          "bundlemerge_after_addchan" *)
*)


fixrec tickstream::"lnat \<rightarrow> 'a::countable event stream"where
"tickstream\<cdot>\<bottom> = \<bottom>"|
"tickstream\<cdot>(lnsuc\<cdot>ln) = \<up>Tick \<Zcat> (tickstream\<cdot>ln)"

lemma tickstream_svalues:"sValues\<cdot>(tickstream\<cdot>ln) \<subseteq> {Tick}"
  apply(rule lnat.induct)
  by simp_all

lemma tickstream_svalues_lnsuc:"sValues\<cdot>(tickstream\<cdot>(lnsuc\<cdot>ln)) = {Tick}"
  by (simp add: tickstream_svalues)

lemma tickstream_tlen[simp]:"#\<^sub>\<surd>(tickstream\<cdot>(ln)) = ln"
  apply(rule lnat.induct)
  apply(rule adm_eq,simp add: tlen_stream_def,simp)
  apply simp_all
  apply (simp add: lnzero_def)
  by (simp add: lnat_suc_plus)

lemma smap2m_tlen[simp]:"#\<^sub>\<surd> (smap (Timed \<circ> TLive)\<cdot>s) = #\<^sub>\<surd> s"
  apply(induction s)
  apply(rule adm_eq,simp add: tlen_stream_def,simp)
  by simp_all
  
lemma equalizer_well[simp]:"lsb_well (\<lambda>c::'cs2::{echan}. if chDom TYPE('cs2) = {} then \<bottom> else if Rep c\<in> chDom TYPE('cs1::echan) then sb\<^enum>\<^sub>\<star> c else smap (Timed o TLive)\<cdot>(tickstream\<cdot>(#\<^sub>\<surd> sb)))"
  apply(cases "chDom TYPE('cs2) = {}")
  apply simp_all
  apply(rule lsbwellI)
  apply(case_tac "Rep c\<in> chDom TYPE('cs1)")
  apply simp_all
  apply(simp add: ctype_echan_def)
  by (metis (no_types, lifting) comp_apply empty_iff image_insert image_is_empty insert_iff smap_sValues subsetI subset_singletonD tickstream_svalues)

lift_definition sbEqualizeTimeSlices::"'cs1::{finite,echan}\<^sup>\<Omega> \<rightarrow> 'cs2::{echan}\<^sup>\<Omega>" is
"\<lambda> sb. Abs_lsb(\<lambda>c. if chDom TYPE('cs2) = {} then \<bottom> 
    else (if Rep c\<in> chDom TYPE('cs1) then sb\<^enum>\<^sub>\<star> c else smap (Timed o TLive)\<cdot>(tickstream\<cdot>(#\<^sub>\<surd> sb))))"
  apply(intro cont2cont)
  by simp

lemma repsbeq_insert:"Rep_lsb((sbEqualizeTimeSlices\<cdot>(sb::'cs1\<^sup>\<Omega>))::'cs\<^sup>\<Omega>) = (\<lambda>c. if chDom TYPE('cs::{echan}) = {} then \<bottom> else (if Rep c\<in> chDom TYPE('cs1::{echan,finite}) then sb\<^enum>\<^sub>\<star> c else smap (Timed o TLive)\<cdot>(tickstream\<cdot>(#\<^sub>\<surd> sb))))"
  by(simp add: sbEqualizeTimeSlices.rep_eq)

lemma sbEqid:assumes"chDom TYPE('cs::echan) \<noteq>{}"
  and "Rep c\<in>chDom TYPE('cs1::{echan,finite})"
shows"((sbEqualizeTimeSlices\<cdot>(sb::'cs1\<^sup>\<Omega>))::'cs\<^sup>\<Omega>) \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  apply(simp add: sbgetch_insert2)
  by(simp add: repsbeq_insert assms)
 
lemma sbEqticks:assumes"chDom TYPE('cs::echan) \<noteq>{}"
  and "Rep c\<notin>chDom TYPE('cs1::{echan,finite})"
  shows"((sbEqualizeTimeSlices\<cdot>(sb::'cs1\<^sup>\<Omega>))::'cs\<^sup>\<Omega>) \<^enum> c = smap (Timed o TLive)\<cdot>(tickstream\<cdot>(#\<^sub>\<surd> sb))"
  apply(simp add: sbgetch_insert2)
  by(simp add: repsbeq_insert assms)
 

lemma sbEq_tlen:assumes"chDom TYPE('cs::echan) \<noteq>{}"
  and "chDom TYPE('csOld) \<subseteq> chDom TYPE('cs)"
  shows"#\<^sub>\<surd>((sbEqualizeTimeSlices\<cdot>sb)::'cs\<^sup>\<Omega>) = #\<^sub>\<surd>(sb::'csOld::{echan,finite}\<^sup>\<Omega>)"
  apply(rule sbtlen_rule,simp_all add: assms)
  apply(case_tac "Rep c\<in>chDom TYPE('csOld)")
proof(simp_all add: assms sbEqid sbEqticks)
  fix c::'cs
  assume cdom:"Rep c \<in> chDom TYPE('csOld)"
  then obtain leastc where leastc_def:"#\<^sub>\<surd> sb = #\<^sub>\<surd> (sb\<^enum> leastc)"
    by (metis emptyE sbtlen2stlen)
  have leastcleast:"\<And>c. #\<^sub>\<surd> (sb\<^enum> leastc) \<le> #\<^sub>\<surd> (sb\<^enum> c)"
    apply(simp add: leastc_def[symmetric])
    using sbtlen_min_len cdom by blast
  show"#\<^sub>\<surd> sb \<le> #\<^sub>\<surd> (sb  \<^enum>\<^sub>\<star>  c)"
    apply(simp add: sbgetch_insert cdom)
    apply(subst sbgetch_insert2[symmetric])
    using leastcleast leastc_def by presburger
next
  show "\<exists>c::'cs. #\<^sub>\<surd> (sbEqualizeTimeSlices\<cdot>sb  \<^enum>  c) = #\<^sub>\<surd> sb"
  proof(cases"chDom TYPE('csOld) = {}",simp add: sbgetch_insert repsbeq_insert assms)
    assume nempty:"chDom TYPE('csOld) \<noteq> {}"
    then obtain leastc where leastc_def:"#\<^sub>\<surd> sb = #\<^sub>\<surd> (sb\<^enum> leastc)"
      by (metis sbtlen2stlen)
    show"\<exists>c::'cs. #\<^sub>\<surd> (sbEqualizeTimeSlices\<cdot>sb  \<^enum>  c) = #\<^sub>\<surd> sb"
      apply(rule_tac x="Abs(Rep leastc)" in exI)
      apply(subst sbEqid)
      apply (simp_all add: assms leastc_def)
      apply (metis assms(2) chdom_in nempty rep_reduction subset_eq)
      apply(auto simp add: sbgetch_insert assms sbgetch_insert2)
      apply (metis abs_eqI(1) abs_fail assms(2) in_mono)
      using chdom_in apply blast
      by (metis abs_fail assms(2) in_mono)
  qed
qed


theorem bundlemerge_after_addchan:
  fixes spfOld::"'csOld::{echan,finite}\<^sup>\<Omega> \<rightarrow> 'csOld msgWithChan event stream"
  assumes "spfOld \<in> mergeTimed"
      and "chDom (TYPE('csNew::{echan,finite})) \<subseteq> chDom (TYPE('csOld))"
    shows "emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo spfOld
          \<in> {(sbTypeCast::('csOld\<^sup>\<Omega> \<rightarrow> 'csNew\<^sup>\<Omega>))} \<then> mergeTimed"
  oops
(*  apply (auto simp add: image_iff)
proof - 
  have "emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo spfOld
        oo (sbFillWithTicks::('csNew\<^sup>\<Omega> \<rightarrow> 'csOld\<^sup>\<Omega>)) \<in> mergeTimed" sorry

  have "emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo spfOld
        oo (sbFillWithTicks::('csNew\<^sup>\<Omega> \<rightarrow> 'csOld\<^sup>\<Omega>))
        oo (sbTypeCast::('csOld\<^sup>\<Omega> \<rightarrow> 'csNew\<^sup>\<Omega>))
        =
            emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo  spfOld" sorry (* Stimmt nicht *)

  hence "emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)
        oo (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::'csNew myself)))
        oo spfOld
           \<in> {(sbTypeCast::('csOld\<^sup>\<Omega> \<rightarrow> 'csNew\<^sup>\<Omega>))} \<then> mergeTimed" 
    apply auto
    using sbfill_cast[OF assms(2)] 
    sorry
  show ?thesis sorry
qed
*)


lemma assumes "otherSPF oo spf \<in> sps" 
  shows "otherSPF \<in> {spf} \<then> sps"
  apply (auto simp add: image_iff)
  using assms image_iff 
  oops

lemma   assumes "otherSPF \<in> {spf} \<then> sps"
  shows "otherSPF oo spf \<in> sps" 
  using assms apply auto 
  oops

lemma c1_c3_chandom:"chanDom (DUMMY::cs1 myself) \<subseteq> chanDom (DUMMY::cs3 myself)"
  unfolding ChanDom_cs1_def  ChanDom_cs3_def
  by simp
lemma c1_c3_chdom:"chDom TYPE(cs1) \<subseteq> chDom TYPE(cs3)"
  by (metis c1_c3_chandom chandom_chdom_eq)

(*
lemma bundlemerge_after_addchan:
  fixes spfNew::"bundle_button_mintime.cs3\<^sup>\<Omega> \<rightarrow> cs3 msgWithChan event stream"
  assumes "spfNew \<in> mergeTimed"
  shows "\<exists>spfOld::cs1\<^sup>\<Omega> \<rightarrow> cs1 msgWithChan event stream. 
            spfOld \<in> mergeTimed \<and>
            spfOld\<cdot>(input\<star>) = emap (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan)\<cdot>
                                (efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chanDom (DUMMY::cs1 myself))\<cdot>
                                  (spfNew\<cdot>input))"
  apply(rule exI [where x="emap (Abs_msgWithChan \<circ> apfst (Abs \<circ> Rep) \<circ> Rep_msgWithChan) oo
    efilter (\<lambda>x::cs3 msgWithChan. Rep (fst (Rep_msgWithChan x)) \<in> chanDom DUMMY) oo
    spfNew oo (sbTypeCast::(cs3\<^sup>\<Omega> \<rightarrow> cs1\<^sup>\<Omega>))"])
  apply auto
  using bundlemerge_after_addchan[OF assms(1), OF c1_c3_chandom] apply auto
  apply(rule cfun_arg_cong)+
  
  sledgehammer
  sorry 
    (* TODO: Annahme über die Anzahl Zeitscheiben! 
       TODO: Keine Konkreten Typen!

  ? Vllt besser die spfOld aus spfNew construieren? 
        und zeigen, dass konstruiertes spfOld in mergeTimed liegt*)

*)
















instantiation nat::po
begin

definition below_nat::"nat \<Rightarrow> nat \<Rightarrow> bool" where
"below_nat = (\<le>)"

declare below_nat_def[simp]
instance
  apply(intro_classes)
  by(simp_all)
end

lemma nat2lnat_cont:
    assumes "\<And>n x. f n\<cdot>x \<sqsubseteq> x" 
        and "\<And>n x. f n\<cdot>x \<sqsubseteq> f (Suc n)\<cdot>x"
        and "\<And>Y x. chain Y \<Longrightarrow> \<not>finite_chain Y \<Longrightarrow> x \<sqsubseteq> (\<Squnion>i. f(inv Fin (Y i))\<cdot>x)" 
        shows "cont (\<lambda>ln. case ln of \<infinity>\<Rightarrow>ID | Fin n \<Rightarrow> f n)"
  apply(subgoal_tac "chain f") defer
  apply(rule chainI, intro cfun_belowI, simp add: assms(2))

  apply(rule contI2)
   apply(rule monofunI)
   apply (auto simp add: assms)[1]
   apply(case_tac x, case_tac y; simp add: assms cfun_belowI)
  apply (simp add: po_class.chain_mono)
  apply(subgoal_tac "chain f", simp add: is_ub_thelub)

   apply(rule cfun_belowI)
   apply(subst contlub_cfun_fun)
    apply(rule chainI)
  using po_class.chainE apply blast

  by (auto simp add: assms(3))


lemma infinite_nat_chain: assumes "chain Y" and "\<not>finite_chain Y"
  shows "\<exists>i. (limit::nat) \<le> (Y i)"
  apply(induction limit)
  apply auto
  apply(rule ccontr, simp)
  using assms(2) apply(auto simp add: finite_chain_def assms)
  by (metis LNat.inf_chainl2 assms(1) assms(2) below_nat_def not_less_eq_eq order_antisym_conv)

lemma nat_chain_simple[simp]:
  fixes f::"nat \<Rightarrow> 'a::cpo"
  assumes "chain Y" and "\<not>finite_chain Y" and "monofun f"
  shows "(\<Squnion>i. f (Y i)) = (\<Squnion>i::nat. f i)"
  apply(rule below_antisym)
   apply(rule lub_range_mono)
     apply (simp add: image_subset_iff)
  apply(rule chainI, simp add: assms(3) monofunE)
   apply (simp add: assms(1) assms(3) ch2ch_monofun)

  apply(rule is_lub_thelub)
  apply(rule chainI, simp add: assms(3) monofunE)
  apply(rule is_ubI)
proof - 
  fix x
  assume "x \<in> range f"
  obtain i where i_def: "x= f i"
    using \<open>(x::'a) \<in> range (f::nat \<Rightarrow> 'a)\<close> by auto
  obtain n where n_def: "i \<sqsubseteq> Y n"
    using infinite_nat_chain using assms(1) assms(2) by auto
  thus "x \<sqsubseteq> (\<Squnion>i::nat. f (Y i))" 
    by (metis i_def n_def assms(1) assms(3) ch2ch_monofun image_image is_ub_thelub monofun_def rev_below_trans)
qed    

(* \<open>stakets_nc_mono\<close> (und andere lemma/definitionen) sind im kontext
  von stakeTs in der EventStream.thy Theorie
context
begin
private lemma state_inf_id:
  fixes Y::"nat \<Rightarrow> nat"
      and x::"'a::countable event stream"
    assumes "chain Y" and "\<not>finite_chain Y"
    shows "x \<sqsubseteq> (\<Squnion>i. stakeTs_nc (Y i))  x"
    apply(induction x rule:tslice_alt)
    apply(rule adm_below; simp)
    apply(intro cont2cont)
    apply(rule chainI)
  using stakets_nc_mono assms(1) apply (metis below_nat_def fun_belowI po_class.chain_def po_class.chain_mono)

   apply simp

  apply simp
  apply(subst lub_fun [where S="\<lambda>i. stakeTs_nc (Y (i))"])
    apply(rule chainI)
  using stakets_nc_mono assms(1) apply (metis below_nat_def fun_belowI po_class.chain_def po_class.chain_mono)
  apply(subst stakets_msgs) apply simp+

  apply(subst nat_chain_simple [where Y=Y])
  apply (simp add: assms(1) assms(2))+
  apply(intro monofunI monofun_cfun_arg stakets_nc_mono2, simp)

  apply (subst lub_range_shift [where j="Suc 0", THEN sym])
   apply(intro chainI monofun_cfun_arg stakets_nc_mono2, simp)
  apply auto
  using stakets_nc_mono assms(1) 

  apply(subst lub_const_conc, intro chainI monofun_cfun_arg stakets_nc_mono2 le_SucI, simp)+
  apply(rule monofun_cfun_arg)+ 

  apply(subst(asm) nat_chain_simple [where Y=Y])
  apply(simp add: assms)+
   apply(intro monofunI monofun_cfun_arg stakets_nc_mono2 fun_belowI, simp)

  apply auto
  apply(subst stwbl_f) using Fin_0 lnzero_def one_lnat_def apply auto[1]
  apply(rule monofun_cfun_arg)+ 
proof -
  fix s :: "'a event stream"
  assume a1: "s \<sqsubseteq> (\<Squnion>x. stakeTs_nc x) s"
  obtain ss :: "(nat \<Rightarrow> 'a event stream \<Rightarrow> 'a event stream) \<Rightarrow> 'a event stream" where
    "\<forall>f. \<not> chain (\<lambda>n. f n (ss f)) \<or> (\<lambda>s. \<Squnion>n. f n s) = Lub f"
    by (metis (no_types) contlub_lambda)
  then show "s \<sqsubseteq> (\<Squnion>n. stakeTs_nc n s)"
    using a1 by (metis (no_types) po_class.chain_def stakets_nc_mono)
qed



definition stakeTs_lnat :: "lnat \<rightarrow> 'a::{countable} event stream \<rightarrow> 'a event stream" where
"stakeTs_lnat = (\<Lambda> ln . case ln of \<infinity>\<Rightarrow>(ID) 
                        | Fin n \<Rightarrow> (Abs_cfun (stakeTs_nc n)))" 

lemma inv_fin_chain:
  fixes Y::"nat\<Rightarrow>lnat"
  assumes "chain Y" and "\<not> finite_chain Y"
  shows "chain (\<lambda>i. inv Fin (Y i))"
proof(rule chainI)
  fix i
  obtain n where n_def: "Y i = Fin n" using lnat_chain_fin[OF assms] lnat_well_h2 by blast
  obtain n_next where n_next_def: "Y (Suc i) = Fin n_next" using lnat_chain_fin[OF assms] lnat_well_h2 by blast
  show " inv Fin (Y i) \<sqsubseteq> inv Fin (Y (Suc i))"
    apply(simp add: n_next_def n_def)
    by (metis assms(1) less2nat lnle_def n_def n_next_def po_class.chain_def)
qed

lemma inv_fin_chain_finite:
  fixes Y::"nat\<Rightarrow>lnat"
  assumes "chain Y" and "\<not> finite_chain Y"
  shows "\<not> finite_chain (\<lambda>i. inv Fin (Y i))"
  apply(rule ccontr)
  apply(auto simp add: finite_chain_def)
proof - 
  fix max
  assume as: "max_in_chain max (\<lambda>i::nat. inv Fin (Y i))"
  obtain more where "Y max \<noteq> Y more" and "max \<le> more"
    by (meson assms(1) assms(2) finite_chainl1 max_in_chain_def)
  thus False using as lnat_chain_fin[OF assms]
    apply(auto simp add: max_in_chain_def)
    by (metis f_inv_into_f lnat_well_h2 range_eqI)
qed
  

private lemma "stakeTs_lnat\<cdot>ln\<cdot>s = (case ln of \<infinity>\<Rightarrow>s 
                        | Fin n \<Rightarrow> ((stakeTs_nc n s)))"
  apply(subst stakeTs_lnat_def)
  apply(subst beta_cfun, intro nat2lnat_cont)
     apply(subst beta_cfun, intro cont2cont)
     apply(rule stakets_nc_prefix)
    apply(subst beta_cfun, intro cont2cont)+
    apply(rule stakets_nc_mono)

   apply simp
  using state_inf_id defer

   apply(cases ln; simp)
  apply(rule_tac x=x in fun_belowD, subst lub_fun[symmetric])
  apply (metis below_nat_def fun_belowI inv_fin_chain po_class.chain_def stakets_nc_mono2)
  apply(rule fun_belowI)

  apply(rule_tac Y="(\<lambda>i. (inv Fin) (Y i))" in state_inf_id )
  by (simp add: inv_fin_chain inv_fin_chain_finite)+
end 

*)











definition sbToEqTlen::"'cs::{finite, chan}\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" where
"sbToEqTlen = undefined"

hide_fact sbToEqTlen_def

lemma sbtoeqtlen_leneq: "#\<^sub>\<surd>((sbToEqTlen\<cdot>sb) \<^enum> c1) = #\<^sub>\<surd>((sbToEqTlen\<cdot>sb) \<^enum> c2)"
  sorry
lemma sbtoeqtlen_below: "sbToEqTlen\<cdot>sb \<sqsubseteq> sb"
  sorry
lemma sbtoeqtlen_tlen: "#\<^sub>\<surd>(sbToEqTlen\<cdot>sb) = #\<^sub>\<surd>sb"
  sorry
lemma assumes "\<And>c1 c2. #\<^sub>\<surd>(sb \<^enum> c1) = #\<^sub>\<surd>(sb \<^enum> c2)"
  shows "sbToEqTlen\<cdot>sb = sb"
  sorry


lemma spscomp_seqin:
  assumes "spf1 \<in> spsComplete sps1"
          and "spf2 \<in> spsComplete sps2"
        shows "spf2 oo spf1 \<in> spsComplete (sps1 \<then> sps2)"
  using assms apply(auto simp add: spsComplete_def seqcomp_insert)
  by (metis cfcomp2)

theorem
  fixes ndaGreat::"('stateGreat::type, 'csGreat::{echan,finite} msgWithChan event, 'out::conc) automaton"
     and ndaSmall::"('stateSmall::type, 'csSmall::{echan,finite} msgWithChan event, 'out::conc) automaton"
     and f::"'stateGreat \<Rightarrow> 'stateSmall"

  assumes  
          ch_ref:  "chDom (TYPE ('csSmall)) \<subseteq> chDom (TYPE ('csGreat))"

      and init_ref: "apfst f ` autInitConfig\<cdot>ndaGreat \<subseteq> autInitConfig\<cdot>ndaSmall"
      and trans_tick_ref: "\<And>state. apfst f ` (autTransition\<cdot>ndaGreat)    state  Tick 
                                           \<subseteq> (autTransition\<cdot>ndaSmall) (f state) Tick"
      and trans_msg_ref: "\<And>state msg. Rep (fst (Rep_msgWithChan msg)) \<in> chDom (TYPE ('csSmall)) 
          \<Longrightarrow> apfst f ` (autTransition\<cdot>ndaGreat)    state  (Event msg) 
                     \<subseteq> (autTransition\<cdot>ndaSmall) (f state) (Event (ewcTypeCast msg))"

      and trans_msg_new: "\<And>msg state nextState output. Rep (fst (Rep_msgWithChan msg)) \<notin> chDom (TYPE ('csSmall)) 
          \<Longrightarrow> (nextState,output) \<in> (autTransition\<cdot>ndaGreat) state (Event msg)
          \<Longrightarrow> output = \<bottom> \<and> f state = f nextState"

  shows "mergeTimed \<then> eSem ndaGreat 
    \<subseteq> spsComplete ({sbToEqTlen} \<then> {sbTypeCast::'csGreat\<^sup>\<Omega> \<rightarrow> 'csSmall\<^sup>\<Omega>} \<then> mergeTimed \<then> eSem ndaSmall)"
proof (rule spscomplete_belowI)
  fix spf3 sb
  assume as:"spf3 \<in> mergeTimed \<then> eSem ndaGreat"
  obtain spf3Merge spf3Sem where spf3_def: "spf3 = spf3Sem oo spf3Merge"
      and spf3merge_in: "spf3Merge \<in> mergeTimed" and spf3sem_in: "spf3Sem \<in> eSem ndaGreat"
    using as seqcomp_insert by (smt mem_Collect_eq)
  let ?map = "(emap ewcTypeCast)"
  let ?filter = "(efilter (\<lambda>x. Rep (fst (Rep_msgWithChan x)) \<in> chDom (TYPE ('csSmall))))"

  let ?spf1Merge = "?map oo ?filter oo spf3Merge"
(*  have spf1merge_in: "?spf1Merge \<in> {sbToEqTlen} \<then> {sbTypeCast::'csGreat\<^sup>\<Omega>\<rightarrow>'csSmall\<^sup>\<Omega>} \<then> mergeTimed"
    apply(cases "chDomEmpty TYPE('csSmall)")
    defer
    apply (simp add: image_comp )
    apply(auto simp add: mergeTimed_def mergeGen_def image_iff)
    sorry 
    (* by(rule bundlemerge_after_addchan[OF spf3merge_in, OF c1_c3_chdom]) *) 
*)
  have spf1merge_in: "{?spf1Merge} \<subseteq> spsComplete( {sbToEqTlen} \<then> {sbTypeCast::'csGreat\<^sup>\<Omega>\<rightarrow>'csSmall\<^sup>\<Omega>} \<then> mergeTimed)"
    apply(rule spscomplete_belowI, auto)
    apply(rule_tac x="(\<Lambda> input. ?map\<cdot>(?filter\<cdot>(spf3Merge\<cdot>(input \<uplus>\<^sub>\<star> sb))))" in bexI)

     apply(subst beta_cfun, intro cont2cont)
     apply (rule cfun_arg_cong, rule cfun_arg_cong)
     defer

    apply(cases "chDomEmpty TYPE('csSmall)")
    defer
      apply(rule mergetimed_in)
        apply simp
    apply(rule sb_belowI)
       apply(simp add: sbgetch_insert2 uSplit.rep_eq)

    apply(subst eventfilter_typecast)
    using ch_ref apply blast
        apply(rule evalues_filter)

    apply(subst eventfilter_efilter)
        apply (metis ch_ref chdom_in rep_reduction subsetD)

    
    sorry

  have h1: "eSem ndaGreat \<subseteq> spsComplete ({?filter} \<then> {?map} \<then> eSem ndaSmall)"
    unfolding emap_def efilter_def
    apply(intro eventaut_refine_add_channel [where f=f]; simp add: assms)
     apply(rename_tac msg state)
     apply(case_tac msg; simp add: trans_tick_ref trans_msg_ref)
    using trans_msg_new by blast
  obtain spf1Sem where spfsem1_in: "spf1Sem \<in> eSem ndaSmall"
    and conv2:"spf3Sem\<cdot>(spf3Merge\<cdot>sb) =  (spf1Sem oo ?map oo ?filter)\<cdot>(spf3Merge\<cdot>sb)"
    apply(insert h1, simp add: spsComplete_def)
    using spf3sem_in by force
  show "\<exists>spf1\<in>{sbToEqTlen}\<then>{sbTypeCast} \<then> mergeTimed \<then> eSem ndaSmall. spf3\<cdot>sb = spf1\<cdot>sb"
    apply(rule bexI [where x="spf1Sem oo ?spf1Merge"])
     apply(simp add: spf3_def conv2)
    apply(simp add: image_comp)
    using  spfsem1_in spf1merge_in seqcomp_insert 
    apply(auto simp add: seqcomp_insert )
    using spfsem1_in spf1merge_in assoc_oo  
    
    oops


end