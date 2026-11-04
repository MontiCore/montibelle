theory Causality

imports Classes SetPcpo Prelude

begin
default_sort type

definition weak::"('I::{cpo,tlen} \<rightarrow> 'O::{cpo,tlen}) \<Rightarrow> bool" where
"weak spf \<equiv> \<forall>i. #\<^sub>\<surd>i \<le> #\<^sub>\<surd>(spf\<cdot>i)" 

definition weakpred::"'in::tlen \<Rightarrow> 'out::tlen \<Rightarrow> bool"where
"weakpred i out \<equiv>#\<^sub>\<surd>i \<le> #\<^sub>\<surd>out"



definition strong::"('I::{cpo,tlen} \<rightarrow> 'O::{cpo,tlen}) \<Rightarrow> bool" where
"strong spf \<equiv> \<forall>i. lnsuc\<cdot>(#\<^sub>\<surd>i) \<le> #\<^sub>\<surd>(spf\<cdot>i)"

definition strongpred::"'in::tlen \<Rightarrow> 'out::tlen \<Rightarrow> bool"where
"strongpred i out \<equiv> lnsuc\<cdot>(#\<^sub>\<surd>i) \<le> #\<^sub>\<surd>out"


lemma strong2weak [simp]:
  assumes"strong spf"
  shows"weak spf"
  by (meson assms less_lnsuc strong_def trans_lnle weak_def)

lemma strong2weakpred:
  assumes"strongpred i out"
  shows"weakpred i out"
  by (meson assms dual_order.trans less_lnsuc strongpred_def weakpred_def)

lemma weakI:
  assumes"\<And>i. #\<^sub>\<surd> i \<le> #\<^sub>\<surd>(spf\<cdot>i)"
  shows "weak spf"
  by(simp add: weak_def assms)

lemma strongI:
  assumes"\<And>i. lnsuc\<cdot>(#\<^sub>\<surd> i) \<le> #\<^sub>\<surd>(spf\<cdot>i)"
  shows "strong spf"
  by(simp add: strong_def assms)

lemma weak2pred: 
  assumes "weak spf" 
  shows "weakpred i (spf\<cdot>i)"
  using assms by (simp add: weak_def weakpred_def)

lemma strong2pred: 
  assumes "strong spf"
  shows "strongpred i (spf\<cdot>i)"
  using assms by (simp add: strong_def strongpred_def)

lemma cfcomp_weak_well: 
  assumes "weak f" and "weak g"
  shows "weak (f oo g)"
  by (metis (no_types, opaque_lifting) assms(1) assms(2) cfcomp2 dual_order.trans weak_def)

lemma cfcomp_strong_well1:
  assumes "weak f" 
  and "strong g"
  shows "strong (f oo g)"
  by (metis (no_types, opaque_lifting) assms cfcomp2 dual_order.trans weak_def strong_def)

lemma cfcomp_strong_well2: 
  assumes "strong f" 
  and "weak g"
  shows "strong (f oo g)"
  apply (subst strong_def, rule allI, simp)
  apply(rename_tac sb)
  apply (subgoal_tac "#\<^sub>\<surd>(g\<cdot>sb) <\<^sup>l #\<^sub>\<surd>(f\<cdot>(g\<cdot>sb))")
  apply (meson assms(2) dual_order.trans lnsuc_lnle_emb weak_def)
  using assms(1) strong_def by blast



lemma weak_well_adm:"adm weak"
  unfolding weak_def
  apply (rule adm_all)
  apply(rule admI)
  apply(subst lnle_def)
  by (meson cfun_below_iff dual_order.trans is_ub_thelub lnle_conv mono_tlen)

lemma strong_well_adm:"adm strong"
  unfolding strong_def
  apply (rule adm_all)
  apply(rule admI)
  apply(subst lnle_def)
  by (meson cfun_below_iff dual_order.trans is_ub_thelub lnle_conv mono_tlen)


lemma weakD: assumes "weak spf" and "wellformed i" 
  shows "#\<^sub>\<surd> i \<le> #\<^sub>\<surd> (spf\<cdot>i)"
  using assms(1) assms(2) weak_def by auto

lemma strong_tleninf: "strong (\<Lambda> _ . tlen_inf)"
  by(rule strongI, simp)

lemma wellformed_weakI:
  fixes spf::"'csIn::wellformed \<rightarrow> 'csOut::wellformed" 
  assumes "weak spf" and "wellformed sb"
  shows "wellformed (spf\<cdot>sb)"
proof - 
  obtain sbSuper where super: "sb \<sqsubseteq> sbSuper" 
            and super_tlen: "#\<^sub>\<surd>sbSuper = \<infinity>" 
    using well_superEx2[OF assms(2)] by blast
  have "wellformed sbSuper"
    by (metis super_tlen well_infI)
  show ?thesis
  apply(rule well_belowI[where super="spf\<cdot>sbSuper"])
    apply (simp add: super cont_pref_eq1I; fail)
    by (metis assms(1) super_tlen inf_less_eq weakD well_infI)
qed

end