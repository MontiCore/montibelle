theory StreamFoot
imports stream.Stream
begin

text\<open>@{term sfoot}: Get the last element of a not empty, finite stream\<close>
definition sfoot      :: "'a stream \<Rightarrow> 'a" where
"sfoot s = snth (THE a. lnsuc\<cdot>(Fin a) = #s) s"


section \<open>@{term sfoot}\<close>

lemma sfoot1[simp]: assumes "xs = s\<Zcat>(\<up>a)" and "#xs < \<infinity>"
   shows "sfoot xs = a"
proof -
  have "xs \<noteq> \<epsilon>" using assms(1) strictI by force
  obtain n where n_def: "Fin n = #xs" by (metis assms(2) lncases lnless_def) 
  hence "n>0" using assms(2) gr0I using Fin_02bot \<open>xs \<noteq> \<epsilon>\<close> lnzero_def slen_empty_eq by fastforce 
  hence "(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n-1" by (metis (mono_tags, lifting) Fin_Suc Suc_diff_1 n_def inject_Fin inject_lnsuc the_equality)
  have "snth (n-1) xs = a" by (metis Fin_0 Fin_Suc Suc_diff_1 assms(1) n_def bot_is_0 inject_lnsuc lnat.con_rews lscons_conv neq0_conv sdropl6 shd1 slen_lnsuc snth_def sup'_def)
  thus ?thesis by (metis \<open>(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n - 1\<close> sfoot_def)
qed

lemma sfoot12 [simp]: assumes "#s<\<infinity>"
  shows "sfoot (s\<Zcat>\<up>a) = a"
by (metis assms fold_inf inject_lnsuc lnless_def monofun_cfun_arg sfoot1 slen_lnsuc)

lemma sfoot_one [simp]: "sfoot (\<up>a) = a"
by (metis Inf'_neq_0 inf_ub lnle_def lnless_def sconc_fst_empty sfoot12 slen_zero)


lemma sfoot2 [simp]: assumes "sfoot xs = a" and "xs\<noteq>\<epsilon>"
  shows "\<exists>s. xs = s \<Zcat> \<up>a"
proof (cases "#xs = \<infinity>")
  case True thus ?thesis by (metis sconc_fst_inf) 
next
  case False 
  obtain n where n_def:"#xs = Fin (Suc n)" using False lncases assms(2) slen_empty_eq
    by (metis Fin_0 old.nat.exhaust)
  hence h1:"stake (n)\<cdot>xs \<Zcat> \<up>(snth (n) xs) = xs"
    apply(induction n arbitrary: xs)
    by(rule_tac x="xs" in scases;simp)+
  show ?thesis 
    apply(rule exI[of _ "stake n\<cdot>xs"])
    apply(subst h1[symmetric])
    apply(rule reduce_seq)
    by (simp add: assms(1)[symmetric] sfoot_def n_def)
qed

lemma sfoot_conc [simp]: assumes "#s<\<infinity>" and "#xs<\<infinity>" and "xs\<noteq>\<epsilon>"
  shows "sfoot (s\<Zcat>xs) = sfoot xs"
by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) assoc_sconc sconc_slen sfoot1 sfoot2)

lemma sfoot_sdrop: assumes "Fin 1<#s" and "#s<\<infinity>"
  shows "sfoot (srt\<cdot>s) = sfoot s"
proof -
  obtain s' where "s = s' \<Zcat> \<up>(sfoot s)" by (metis assms(1) below_antisym bot_is_0 lnless_def minimal sfoot2 slen_zero)
  hence "s' \<noteq> \<epsilon>"
    by (metis Fin_02bot Fin_Suc One_nat_def assms(1) lnless_def lnzero_def slen_lnsuc slen_zero)
  hence "s' \<Zcat> \<up>(sfoot s) \<noteq> \<epsilon>"
    by (metis (full_types) sconc_snd_empty strictI)
  hence "srt\<cdot>s = srt\<cdot>s' \<Zcat> \<up>(sfoot s)"
    by (metis (no_types) \<open>s = s' \<Zcat> \<up>(sfoot s)\<close> \<open>s' \<noteq> \<epsilon>\<close> assoc_sconc inject_scons surj_scons)
  thus ?thesis
    by (metis \<open>s = s' \<Zcat> \<up>(sfoot s)\<close> \<open>s' \<noteq> \<epsilon>\<close> assms(2) inf_ub lnle_conv lnless_def sconc_snd_empty sfoot1 slen_sconc_snd_inf strictI surj_scons) 
qed

lemma sfoot_nshd [simp]: assumes "#xs < \<infinity>"
  shows "sfoot (\<up>a \<Zcat> \<up>b \<Zcat> xs) = sfoot (\<up>b \<Zcat> xs)"
using assms lnless_def by auto 

lemma sfoot_exists [simp]:"\<exists>n. snth n s = sfoot s"
by (metis sfoot_def)

lemma  sfoot_exists2: 
  shows "Fin (Suc n) = #s \<Longrightarrow> snth n s = sfoot s"
  apply(induction n arbitrary: s)
  apply (metis (mono_tags, lifting) Fin_02bot Fin_Suc Zero_lnless_infty inject_lnsuc lnzero_def sconc_fst_empty sconc_snd_empty sfoot12 slen_empty_eq slen_scons snth_shd surj_scons)
  apply(case_tac s rule: scases;simp)
  apply(subst sfoot_sdrop[symmetric];simp)
  apply(subgoal_tac "#sa = Fin (Suc n)",simp)
  apply (metis Fin_Suc lnat.sel_rews(2))
  apply (metis leI notinfI3)
  by (metis Fin_Suc inject_lnsuc)


lemma sfood_id: assumes"#s = Fin (Suc n)"
  shows "(stake n\<cdot>s) \<Zcat> \<up>(sfoot s) = s"
  using assms
proof(induction n arbitrary: s)
  case 0
  then show ?case 
  apply simp
  by (metis Fin_02bot Fin_Suc lnat.sel_rews(2) lnsuc_neq_0_rev lnzero_def lscons_conv sfoot_exists2 slen_scons snth_shd slen_zero sup'_def surj_scons)
next
  case (Suc n)
  then show ?case
    apply (subst stake_suc)
    apply simp
    apply(rule scases[of s],simp_all)
    apply(subst stake2shd2)
    apply auto[1]
    apply(subst sfoot_conc,simp_all)
    by force
qed


lemma footind: "#s = Fin k \<Longrightarrow> P \<epsilon> \<Longrightarrow> (\<And>t a. #t < \<infinity> \<Longrightarrow> P t \<Longrightarrow> P (t \<Zcat> \<up>a)) \<Longrightarrow> P s"
proof -
  assume "#s = Fin k" and "P \<epsilon>" and "\<And>t a. #t < \<infinity> \<Longrightarrow> P t \<Longrightarrow> P (t \<Zcat> \<up>a)"
  then show "P s"
  proof (induction k arbitrary: s rule: less_induct)
    case (less k)
    then have IH: "\<And>t. #t < Fin k \<Longrightarrow> P \<epsilon> \<Longrightarrow> (\<And>u b. #u < \<infinity> \<Longrightarrow> P u \<Longrightarrow> P (u \<Zcat> \<up>b)) \<Longrightarrow> P t"
      by (meson lnat_well_h1)
    then show ?case
    proof (cases "k = 0")
      case True
      then show ?thesis
        using less.prems(1) less.prems(2) by force
    next
      case False
      then obtain u b where "s = u \<Zcat> \<up>b"
        using less.prems(1) sfoot2 by force
      then have "#u < Fin k"
        by (metis fold_inf leI less.prems(1) ln_less lnsuc_lnle_emb notinfI3 slen_lnsuc)
      then show ?thesis
        by (metis IH \<open>s = u \<Zcat> \<up>b\<close> inf_ub less.prems(2) less.prems(3) less_le not_less)
    qed
  qed
qed

lemma footind2: "#s < \<infinity> \<Longrightarrow> P \<epsilon> \<Longrightarrow> (\<And>t a. #t < \<infinity> \<Longrightarrow> P t \<Longrightarrow> P (t \<Zcat> \<up>a)) \<Longrightarrow> P s"
  by (metis footind infI less_le)

lemma sfoot_end:
  fixes s and a
  assumes "#s < \<infinity>" and "s \<noteq> \<epsilon>"
  shows "\<exists>t n. s = t \<Zcat> (sntimes n (\<up>(sfoot s))) \<and> (t = \<epsilon> \<or> sfoot s \<noteq> sfoot t)"
  apply (rule footind2)
  apply (simp add: assms(1); fail)
   apply (metis sconc_fst_empty sntimes.simps(1))
proof -
  fix t :: "'a stream" and a :: 'a
  assume "#t < \<infinity>" and "\<exists>ta n. t = ta \<Zcat> (sntimes n (\<up>(sfoot t))) \<and> (ta = \<epsilon> \<or> sfoot t \<noteq> sfoot ta)"
  then obtain u n where "t = u \<Zcat> (sntimes n (\<up>(sfoot t)))" and "u = \<epsilon> \<or> sfoot t \<noteq> sfoot u"
    by blast
  then have expr: "t \<Zcat> \<up>a = u \<Zcat> (sntimes n (\<up>(sfoot t))) \<Zcat> \<up>a"
    by (metis assoc_sconc)
  then show "\<exists>ta n. ((t \<Zcat> \<up>a) =(ta \<Zcat> (n\<star>(\<up>(sfoot (t \<Zcat> \<up>a)))))) \<and> ((ta = \<epsilon>) \<or> (sfoot (t \<Zcat> \<up>a) \<noteq> sfoot ta))"
  proof (cases "a = sfoot t")
    case True
    then have "t \<Zcat> \<up>a = u \<Zcat> (sntimes (Suc n) (\<up>(sfoot t)))"
      by (metis expr sntimes_Suc2)
    then show ?thesis
      by (metis True \<open>#t < \<infinity>\<close> \<open>u = \<epsilon> \<or> sfoot t \<noteq> sfoot u\<close> sfoot12)
  next
    case False
    then have "t \<Zcat> \<up>a = (u \<Zcat> (sntimes n (\<up>(sfoot t)))) \<Zcat> (sntimes (Suc 0) (\<up>(sfoot (t \<Zcat> \<up>a))))"
      using \<open>#t < \<infinity>\<close> \<open>t = u \<Zcat> (n\<star>\<up>(sfoot t))\<close> by auto
    then show ?thesis
      by (metis False \<open>#t < \<infinity>\<close> \<open>t = u \<Zcat> (n\<star>\<up>(sfoot t))\<close> sfoot12)
  qed
qed

lemma sfoot_dom: assumes "#s = Fin (Suc n)" and "sValues\<cdot>s\<subseteq>A"
  shows "sfoot s\<in>A"
by (metis Suc_n_not_le_n assms(1) assms(2) contra_subsetD leI less2nat_lemma sfoot_exists2 snth2sValues)

end