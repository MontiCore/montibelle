theory hwl_tsynSBBoolFilter
  imports
    hwl_tsynSBRemDups
    TsynStreamExtension
    TsynSBFunctionExtension

begin

default_sort countable


lemma tsynchan_svalues: "sValues\<cdot>((sb :: 'cs::{tsynchan}\<^sup>\<Omega>)  \<^enum>  c) \<subseteq> Timed ` Tsyn ` UNIV"
  apply(insert sbgetch_ctypewell[of c sb])
  apply(simp add: ctype_def)
  apply(case_tac "chDomEmpty TYPE('cs)", simp_all add: cMsg_nonempty_tsynchan)
  by blast

lemma tsynfilterelem_image_seq: "tsynFilterElem A ` B \<subseteq> B \<union> {\<sim>}"
  apply(auto simp add: image_def)
  apply(case_tac xa, simp_all)
  by(case_tac "a \<in> A", simp_all)


lemma tsynboolfilter_subset: "sValues\<cdot>(tsynBoolFilter\<cdot>s\<cdot>ora) \<subseteq> sValues\<cdot>s \<union> {\<sim>}"
  apply(simp add: tsynBoolFilter_def)
  apply(simp add: tsynprojfst_sValues tsynfilter_insert smap_sValues)
proof-
  have "sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s \<times> sValues\<cdot>ora) \<union> {\<sim>}"
    by (rule tsynzip_sValues)
  then have "tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s \<times> sValues\<cdot>ora) \<union> {\<sim>}"
    by (meson Un_least order_trans sup_ge2 tsynfilterelem_image_seq)
  then have lhs: "tsynFst ` tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> TSynMsg ` (tsynValues\<cdot>s) \<union> {\<sim>}"
    by auto

  have rhs: "TSynMsg ` (tsynValues\<cdot>s) \<union> {\<sim>} \<subseteq> insert \<sim> (sValues\<cdot>s)"
    by(auto simp add: image_def tsyndom_insert)

  show "tsynFst ` tsynFilterElem (Collect snd) ` sValues\<cdot>(tsynZip\<cdot>s\<cdot>ora) \<subseteq> insert \<sim> (sValues\<cdot>s)"
    using lhs rhs by order
qed

lemma tsynmsgtomstream_svalues: "sValues\<cdot>(tsynMsgToMStream\<cdot>s) \<subseteq> Timed ` Tsyn ` sValues\<cdot>s"
  apply(simp add: tsynMsgToMStream_def smap_sValues)
  by blast

lemma totsynmsgstream_svalues: "sValues\<cdot>(toTsynMsgStream\<cdot>s) \<subseteq> (inv Tsyn) ` (inv Timed) ` sValues\<cdot>s"
  apply(simp add: toTsynMsgStream_def  smap_sValues)
  by blast



definition tsynSBBoolFilter_raw :: "'cs::{tsynchan}\<^sup>\<Omega> \<Rightarrow> ('cs \<Rightarrow> bool stream) \<rightarrow> 'cs\<^sup>\<Omega>" where
  "tsynSBBoolFilter_raw \<equiv> \<lambda>sb. \<Lambda> f. Abs_lsb (\<lambda>c. (tsynMsgToMStream oo (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>(f c)) oo toTsynMsgStream)\<cdot>(sb\<^enum>c))"

lemma
  tsynsbboolfilter_well_pre:
  assumes "sValues\<cdot>s \<subseteq> Timed ` Tsyn ` UNIV"
  shows "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> sValues\<cdot>(s) \<union> {Timed (Tsyn \<sim>)}"
proof-
  have "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> Timed ` Tsyn ` (sValues\<cdot>(toTsynMsgStream\<cdot>(s)) \<union> {\<sim>})"
    by (meson dual_order.trans subset_image_iff tsynboolfilter_subset tsynmsgtomstream_svalues)
  then have 1: "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> (Timed ` Tsyn ` sValues\<cdot>(toTsynMsgStream\<cdot>(s))) \<union> {Timed (Tsyn \<sim>)}"
    by blast

  have 2: "Timed ` Tsyn ` sValues\<cdot>(toTsynMsgStream\<cdot>s) \<subseteq> sValues\<cdot>s"
    using assms by(auto simp add: toTsynMsgStream_def  smap_sValues image_def)

  show ?thesis
    using "1" "2" by blast
qed


lemma tsynsbboolfilter_well:
  "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>((x :: 'cs::{tsynchan}\<^sup>\<Omega>)  \<^enum>  c))\<cdot>y)) \<subseteq> ctype (Rep c)"
proof (cases "chDomEmpty TYPE('cs)")
  case c: True
  then have "x  \<^enum>  c = \<epsilon>"
    by simp
  then have "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(x  \<^enum>  c))\<cdot>y)) = {}"
    by (metis strict_smap toTsynMsgStream_def tsynMsgToMStream_def tsynboolfilter_strict(3) svalues_eps)
  then show ?thesis
    by blast
next
  case c: False
  then have "ctype (Rep c) = (Timed o Tsyn) ` ({Eps} \<union> (TSynMsg ` (cMsg (Rep c))))"
    by (simp add: cMsg_nonempty_tsynchan ctype_def)
  then show ?thesis
    by (meson Eps_ctype_Rep_c c Un_least order.trans sbgetch_ctypewell tsynchan_svalues tsynsbboolfilter_well_pre)
qed

lift_definition tsynSBBoolFilter :: "'cs::{tsynchan}\<^sup>\<Omega> \<rightarrow> ('cs \<Rightarrow> bool stream) \<rightarrow> 'cs\<^sup>\<Omega>" is
  "tsynSBBoolFilter_raw"
  apply(simp add: tsynSBBoolFilter_raw_def)
  apply(intro cont2cont)
  apply(simp add: lsb_well_def)
  by(simp add: tsynsbboolfilter_well)

lemma tsynsbboolfilter_getch:
  "tsynSBBoolFilter\<cdot>sb\<cdot>oraf \<^enum> c = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))\<cdot>(oraf c))"
  apply(simp add: tsynSBBoolFilter_def tsynSBBoolFilter_raw_def)
  apply(subst beta_cfun, intro cont2cont, simp add: lsb_well_def tsynsbboolfilter_well)+
  apply(subst sbgetch_insert2, subst sb_rep_abs, rule lsbwellI, rule tsynsbboolfilter_well)
  ..

lemma
  tsynsbboolfilter_insert:
  assumes "\<And>c. sbo \<^enum> c = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> (cf c)))\<cdot>(oraf (cf c)))"
    and "\<And>c. ctype (Rep (cf c)) \<subseteq> ctype (Rep c)"  
  shows "sbo = sbRenameCh cf\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)"
  by (metis assms(1,2) sb_eqI sbrenamech_getch tsynsbboolfilter_getch)


lemma tsynsblen_tsynlenm_leq: "tsynLenM\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>s)\<cdot>ora)) \<le> tsynLenM\<cdot>s"
  apply(simp add: tsynLenM_def)
  apply(insert tsynlen_boolfilter[of "toTsynMsgStream\<cdot>s" ora])
  by (metis toTsynMsgStream_smap_Timed_Tsyn tsynMsgToMStream_def)


lemma tsynsbboolfilter_live:
  assumes "tsynSBlen (sb :: 'cs::{tsynchan}\<^sup>\<Omega>) = \<infinity>"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>oraf) = (LEAST n . n\<in>{(#({True} \<ominus> oraf c)) | c . True})"
  apply(insert tsynSBlen_infty[of sb], simp add: assms)
  apply(subst tsynSBlen_rule)
     apply (auto simp add: tsynsbboolfilter_getch)
    apply(simp_all add: tsynLenM_def tsynMsgToMStream_def toTsynMsgStream_smap_Timed_Tsyn)
  apply (smt Least_le)
  by (smt LeastI_ex)


lemma tsynsbboolfilter_live_single:
  assumes "tsynSBlen (sb :: 'cs::{tsynchan}\<^sup>\<Omega>) = \<infinity>"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>_.ora)) = #({True} \<ominus> ora)"
  by (smt LeastI_ex assms mem_Collect_eq tsynsbboolfilter_live)


lemma tsynsbboolfilter_live_single_rename:
  fixes sb :: "'ca::{tsynchan}\<^sup>\<Omega>"
    and cf :: "'cb::{tsynchan} \<Rightarrow> 'ca"
  assumes "tsynSBlen sb = \<infinity>"
    and "\<not>chDomEmpty TYPE('ca)"
    and "\<not>chDomEmpty TYPE('cb::{tsynchan})"
    and "\<And>c. ctype (Rep (cf c)) \<subseteq> ctype (Rep c)"
  shows "tsynSBlen (sbRenameCh cf\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>_.ora))) = #({True} \<ominus> ora)"
  apply(subst tsynsbboolfilter_live_single[OF assms(1,2), symmetric])
  apply(rule tsynSBlen_rule)
    apply(simp add: assms(3))
   apply (metis assms(2,4) sbrenamech_getch tsynSBlen_le)
proof -
  have "\<forall>c. tsynLenM\<cdot> (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora) \<^enum> c) = #({True} \<ominus> ora)"
    by (metis (lifting) assms(1,2) cfcomp2 toTsynMsgStream_smap_Timed_Tsyn tsynLenM_def tsynMsgToMStream_def tsynSBlen_infty tsynboolfilter_live tsynsbboolfilter_getch)
  then show "\<exists>c. tsynLenM\<cdot> (sbRenameCh cf\<cdot> (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora)) \<^enum> c) = tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora))"
    by (metis (no_types) assms(2,4) dual_order.eq_iff sbrenamech_getch tsynSBlen_rule)
qed


lemma
  tsynsblen_tsynsbremdups_tsynsbboolfilter_leq:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>(sb)\<cdot>(oraf))) \<le> tsynSBlen (tsynSBRemDups\<cdot>sb)"
proof-

  obtain ca where ca: "\<And>c. tsynLenM\<cdot>(tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)  \<^enum>  ca) \<le> tsynLenM\<cdot>(tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)  \<^enum>  c)"
    by (metis assms tsynSBlen_le tsynSBlen_ruleD(2))

  obtain cb where cb: "\<And>c. tsynLenM\<cdot>(tsynSBRemDups\<cdot>sb  \<^enum>  cb) \<le> tsynLenM\<cdot>(tsynSBRemDups\<cdot>sb  \<^enum>  c)"
    by (metis assms tsynSBlen_ruleD(1,2))

  show ?thesis
    apply(rule tsynSBlen_le_rule[of ca _ cb])
        apply(auto simp add: assms ca cb)
    apply(auto simp add: tsynSBRemDups_getCh tsynsbboolfilter_getch tsynLenM_def)
    apply (cases "#\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  ca))\<cdot>(oraf ca))) \<le> #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  cb))\<cdot>(oraf cb)))")
    using trans_lnle tsynlen_remdups_boolfilter_leq apply blast
    by (metis (no_types, lifting) ca cfcomp2 toTsynMsgStream_tsynMsgToMStream_id tsynLenM_def tsynSBRemDups_getCh tsynsbboolfilter_getch)
qed

end