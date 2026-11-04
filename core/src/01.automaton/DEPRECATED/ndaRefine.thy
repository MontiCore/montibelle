theory ndaRefine

imports ndAutomaton

begin




lemma ndatransrefines_h:
  assumes "ndaTransition\<cdot>nda1 \<sqsubseteq> ndaTransition\<cdot>nda2"
  and "ndaInitConfig\<cdot>nda1 \<subseteq> ndaInitConfig\<cdot>nda2"
  shows "nda1 \<sqsubseteq> nda2"
  by (metis (full_types) SetPcpo.less_set_def assms(1) assms(2) fun_belowD nda_belowI)

lemma ndatransrefines:
  assumes "ndaTransition\<cdot>nda1 \<sqsubseteq> ndaTransition\<cdot>nda2"
  and "ndaInitConfig\<cdot>nda1 \<subseteq> ndaInitConfig\<cdot>nda2"
  shows "\<lbrakk>nda1\<rbrakk>\<^sup>c \<subseteq> \<lbrakk>nda2\<rbrakk>\<^sup>c"
  by (metis (full_types) assms(1) assms(2) le_fun_def nda_trans_mono ndasem_mono_h ndastatesem_mono_h ndatransrefines_h)

lemma assumes "mono f" and "mono g"
  and "\<And>x. g (h x) \<le> h (f x)"
  and "\<And>M. (\<forall>m\<in>M. (gfp g) \<le> h m) \<Longrightarrow> gfp g \<le> h (Inf M)"
shows "(gfp g) \<le> h (gfp f)"
  apply(rule gfp_ordinal_induct)
  apply (simp add: assms(1))
  apply (metis assms(2) assms(3) def_gfp_unfold dual_order.trans mono_def)
  by (simp add: assms(4))


lemma assumes "monofun f" and "monofun g"
  and "\<And>x. g (h x) \<sqsubseteq> h (f x)"
  and "\<And>M. (\<forall>m\<in>M. (gfp g) \<sqsubseteq> h m) \<Longrightarrow> gfp g \<sqsubseteq> h (Inf M)"
  and "(\<sqsubseteq>) = (\<le>)"
shows "(gfp g) \<sqsubseteq> h (gfp f)"
  oops





default_sort complete_lattice

lemma parallel_fix_ind:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P \<bottom> \<bottom>"
  assumes step: "\<And>x y. P x y \<Longrightarrow> P (F\<cdot>x) (G\<cdot>y)"
  shows "P (fix\<cdot>F) (fix\<cdot>G)"
  oops



lemma gfp_ordinal_induct[case_names mono step union]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes mono: "mono f"
    and P_f: "\<And>S. P S \<Longrightarrow> gfp f \<le> S \<Longrightarrow> P (f S)"
    and P_Union: "\<And>M. \<forall>S\<in>M. P S \<Longrightarrow> P (Inf M)"
  shows "P (gfp f)"
  oops

instantiation prod:: (order, order) order
begin

definition less_eq_prod:: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
"less_eq_prod a b \<equiv> (fst a \<le> fst b) \<and> (snd a \<le> snd b) "

definition less_prod:: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
"less_prod a b \<equiv> ((fst a < fst b) \<and> (snd a \<le> snd b)) 
               \<or> ((fst a \<le> fst b) \<and> (snd a < snd b))"

instance 
  apply(standard)
  unfolding less_eq_prod_def less_prod_def
  by (auto simp add: le_less)
end

instantiation prod:: (semilattice_inf, semilattice_inf) semilattice_inf
begin
definition inf_prod:: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
"inf_prod a b = ((inf (fst a) (fst b)), (inf (snd a) (snd b)))"

instance 
  apply(standard)
  unfolding inf_prod_def
  by (auto simp add: less_eq_prod_def)
end


instantiation prod:: (semilattice_sup, semilattice_sup) semilattice_sup
begin
definition sup_prod:: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
"sup_prod a b = ((sup (fst a) (fst b)), (sup (snd a) (snd b)))"

instance 
  apply(standard)
  unfolding sup_prod_def
  by (auto simp add: less_eq_prod_def)
end

instantiation prod:: (lattice, lattice) lattice
begin
instance 
  by(standard)
end


instantiation prod:: (complete_lattice, complete_lattice) complete_lattice
begin
definition Inf_prod:: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b" where
"Inf_prod M  = (Inf (fst`M), Inf (snd `M))"

definition Sup_prod:: "('a \<times> 'b) set \<Rightarrow> 'a \<times> 'b" where
"Sup_prod M  = (Sup (fst`M), Sup (snd `M))"

definition top_prod:: "'a \<times> 'b" where
"top_prod = (top, top)"

definition bot_prod:: "'a \<times> 'b" where
"bot_prod = (bot, bot)"

instance 
  apply(standard)
  unfolding Inf_prod_def Sup_prod_def top_prod_def bot_prod_def
  apply auto
  apply (metis INF_lower fst_conv less_eq_prod_def snd_conv)
  apply (metis le_INF_iff less_eq_prod_def old.prod.inject prod.collapse)
  apply (metis SUP_upper fst_conv less_eq_prod_def snd_conv)
  apply (metis SUP_least less_eq_prod_def old.prod.inject prod.collapse)
  done
end

lemma prod_inf_fst[simp]: "fst (Inf M) = Inf (fst`M)"
  by (simp add: Inf_prod_def)

lemma prod_inf_snd[simp]: "snd (Inf M) = Inf (snd`M)"
  by (simp add: Inf_prod_def)


lemma gfp_ordinal_induct[case_names mono step union]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes mono: "mono f"
    and P_init: "P (Inf {})"
    and P_step: "\<And>S. P S \<Longrightarrow> gfp f \<le> S \<Longrightarrow> P (f S)"
    and P_adm: "\<And>M. \<forall>m\<in>M. (P m \<and> gfp f \<le> m) \<Longrightarrow> M \<noteq> {} \<Longrightarrow>  P (Inf M)"
  shows "P (gfp f)"
proof -
  let ?M = "{S. P S \<and> gfp f \<le> S}"
  have "P (Inf ?M)"
    by (metis (no_types, lifting) P_adm P_init mem_Collect_eq)
  also have "Inf ?M = gfp f"
  proof (rule antisym)
    show g1: "gfp f \<le> Inf ?M"
      by (blast intro: Inf_greatest)
    then have "f (gfp f) \<le> f (Inf ?M)"
      by (rule mono [THEN monoD])
    then have "gfp f \<le> f (Inf ?M)"
      using mono [THEN gfp_unfold] by simp
    hence "f (Inf ?M) \<in> ?M"
      by (simp add: P_step calculation g1)
    then have "Inf ?M \<le> f (Inf ?M)"
      by (rule Inf_lower)
    then show "Inf ?M \<le> gfp f"
      by (rule gfp_upperbound)
  qed
  finally show ?thesis .
qed

lemma prod_fst_mono[simp]:  "mono fst"
  using less_eq_prod_def monoI by blast

lemma prod_snd_mono[simp]:  "mono snd"
  using less_eq_prod_def monoI by blast


lemma gfp_prod_single[simp]:
  assumes "mono f"
      and "mono g"
    shows "gfp (\<lambda>m. (f (fst m), g (snd m))) = (gfp f, gfp g)"
  apply(rule antisym)
   apply(rule gfp_least)
  apply(simp add: less_eq_prod_def gfp_upperbound)
  apply(rule gfp_upperbound)
  apply(auto simp add: less_eq_prod_def)
  by(subst gfp_unfold, auto simp add: assms)+

lemma gfp_parallel_induct_h: assumes f_mono: "mono f" and g_mono: "mono g"
  and P_step: "\<And>x y. P(x,y) \<Longrightarrow> (gfp f) \<le> x \<Longrightarrow> (gfp g) \<le> y \<Longrightarrow>  P ((f x),(g y))"
  and P_adm: "\<And>M. (\<forall>m\<in>M. P m \<and> (gfp f) \<le> (fst m) \<and> (gfp g) \<le> snd m) \<Longrightarrow> P (Inf M)"
shows "P (gfp (\<lambda>m. (f (fst m), g (snd m))))" (is "P (gfp ?h)")
proof(rule gfp_ordinal_induct)
  have gfp_fst: "(gfp ?h) = (gfp f, gfp g)"
    by (simp add: f_mono g_mono) 
  show monoProd: "mono (\<lambda>m::'a \<times> 'b. (f (fst m), g (snd m)))" 
    apply(rule monoI, auto)
    by (metis f_mono fst_conv g_mono less_eq_prod_def monoE snd_conv)

  have "(\<forall>m\<in>{}. P m \<and> (gfp f) \<le> (fst m) \<and> (gfp g) \<le> snd m)"
    by simp
  thus "P (Inf {})" using P_adm by blast

  show "\<And>S::'a \<times> 'b. P S \<Longrightarrow> gfp (\<lambda>m::'a \<times> 'b. (f (fst m), g (snd m))) \<le> S \<Longrightarrow> P (f (fst S), g (snd S))"
    apply(subst (asm) gfp_unfold)
     apply (auto simp add: monoProd less_eq_prod_def)
    by (simp add: P_step f_mono g_mono gfp_fixpoint)

  show "\<And>M::('a \<times> 'b) set. \<forall>m::'a \<times> 'b\<in>M. P m \<and> gfp (\<lambda>m::'a \<times> 'b. (f (fst m), g (snd m))) \<le> m \<Longrightarrow> M \<noteq> {} \<Longrightarrow> P (Inf M)"
    by (simp add: P_adm gfp_fst less_eq_prod_def)
qed


lemma gfp_parallel_induct: 
  assumes f_mono: "mono f" and g_mono: "mono g"
      and P_step: "\<And>x y. P x y \<Longrightarrow> (gfp f) \<le> x \<Longrightarrow> (gfp g) \<le> y \<Longrightarrow>  P (f x) (g y)"
      and P_adm: "\<And>M. (\<forall>m\<in>M. P (fst m) (snd m) \<and> (gfp f) \<le> (fst m) \<and> (gfp g) \<le> snd m) 
             \<Longrightarrow> P (Inf (fst`M)) (Inf (snd`M))"
    shows "P (gfp f) (gfp g)"
proof -
  let ?H = "gfp (\<lambda>m. (f (fst m), g (snd m)))"
  let ?P = "\<lambda>m. P (fst m) (snd m)"
  have "?P ?H"
    by(rule gfp_parallel_induct_h, auto simp add: assms)

  thus ?thesis
    by (simp add: f_mono g_mono) 
qed


lemma ndastaterefine_adm: assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
    shows "\<And>(x::'s::type \<Rightarrow> ('in::{chan, finite}\<^sup>\<Omega> \<rightarrow> 'out::chan\<^sup>\<Omega>) set) (y::'a::type \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set) (s::'s) trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 's \<times> 'out\<^sup>\<Omega>.
       \<forall>s::'s. x s \<subseteq> y (f s) \<Longrightarrow>
       trans \<in> ndaStateSem_helper nda1 x s \<Longrightarrow>
       sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
       \<in> (\<lambda>trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 'a \<times> 'out\<^sup>\<Omega>.
              sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
          ndaStateSem_helper nda2 y (f s)"
proof - 
  fix x::"'s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"
  and y::"'a \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" 
  and s::"'s" 
  and trans::"'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 's \<times> 'out\<^sup>\<Omega>"
  assume a1: "\<forall>s::'s. x s \<subseteq> y (f s)"
  and a4: "trans \<in> ndaStateSem_helper nda1 x s"
  have h1: "\<forall>sbe . snd (trans sbe) \<in> ((ndaTransition\<cdot>nda1) s sbe)"
    using a4 by(simp add: ndaStateSem_helper_def) 
  moreover have h2: "\<forall>sbe .  fst (trans sbe) \<in> x (fst (snd (trans sbe)))"
    using a4 by(simp add: ndaStateSem_helper_def) 
  ultimately have h3: "\<forall>sbe . (f (fst (snd(trans sbe))), snd (snd(trans sbe))) \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
    using assms(1) by simp
  obtain trans2 where trans_def: "trans2 = (\<lambda> sbe. (fst (trans sbe), f (fst (snd(trans sbe))), snd (snd(trans sbe))))"
    by(simp)
  then have transF_def2: "\<forall>sbe. (trans2 sbe) = (fst (trans sbe), f (fst (snd(trans sbe))), snd (snd(trans sbe)))"
    by simp
  have "\<forall>sbe. snd (trans2 sbe) \<in> (ndaTransition\<cdot>nda2) (f s) sbe"
    using assms(1) transF_def2
    by (simp add: h3)
  moreover have "\<forall>sbe. fst (trans2 sbe) \<in> y (fst (snd (trans2 sbe)))"
    using a1 h2 transF_def2 by fastforce
  ultimately have h4: "trans2 \<in> ndaStateSem_helper nda2 y (f s)"
    by(simp add: ndaStateSem_helper_def)
  have "sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
        = sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans2 sbe)) \<Zcat>\<^sup>\<Omega> fst (trans2 sbe)\<cdot>sb)"
    using transF_def2
    by auto
  then show "sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
       \<in> (\<lambda>trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 'a \<times> 'out\<^sup>\<Omega>.
              sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
          ndaStateSem_helper nda2 y (f s)"
    using h4 by simp
qed

lemma ndastaterefine:
   assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
  and P_def: "P = (\<lambda>A B. \<forall>s. A s \<subseteq> B (f s))"
shows "P (ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) 
         (ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton))"
  unfolding ndastatesem_eq ndaStateSem2_def 
  apply(rule gfp_parallel_induct [where P = "P"])
  using ndastatesem2_mono apply blast+
   apply (auto simp add: P_def) 
  apply(subst ndastaterefine_adm)
  by(simp_all add: assms(1))

lemma ndarefine_s:
  assumes "\<And>s.      s \<in> fst `ndaInitConfig\<cdot>nda1 \<Longrightarrow> ndaStateSem nda1 s \<subseteq> ndaStateSem nda2 (f s)"
      and "\<And>s out. (s,out)\<in>ndaInitConfig\<cdot>nda1 \<Longrightarrow> (f s, out) \<in> ndaInitConfig\<cdot>nda2"
    shows "(ndaSem nda1) \<subseteq> (ndaSem nda2)"
  apply(simp add: ndaSem_def)
  by (smt Collect_mono_iff fst_conv assms image_eqI subset_iff)

lemma ndarefine:
  assumes "\<And>s. ndaStateSem nda1 s \<subseteq> ndaStateSem nda2 (f s)"
  and "\<And>s out. (s,out)\<in>ndaInitConfig\<cdot>nda1 \<Longrightarrow> (f s, out)\<in>ndaInitConfig\<cdot>nda2"
shows "(ndaSem nda1) \<subseteq> (ndaSem nda2)"
  using assms ndarefine_s by metis

lemma ndastateref_h:
  assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
  shows "(\<lbrakk>nda1\<rbrakk>\<^sup>p) \<sqsubseteq> (\<lambda>s. (\<lbrakk>nda2\<rbrakk>\<^sup>p) (f s))"
  apply(rule ndastaterefine[where f="f"])
  using assms apply auto
  by (simp add: SetPcpo.less_set_def fun_below_iff)


theorem ndastatesemref:
  assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
  shows "(ndaStateSem nda1) state \<subseteq> (ndaStateSem nda2) (f state)"
  apply(insert ndastateref_h[of nda1 f nda2])
  by (simp add: SetPcpo.less_set_def fun_below_iff assms)
  

lemma ndastateref:
  assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
  and "\<And>s out. (s,out)\<in>ndaInitConfig\<cdot>nda1 \<Longrightarrow> (f s, out)\<in>ndaInitConfig\<cdot>nda2"
  shows "\<lbrakk>nda1\<rbrakk>\<^sup>c \<subseteq> \<lbrakk>nda2\<rbrakk>\<^sup>c"
  apply(rule ndarefine[where f="f"])
  apply(simp add: less_set_def[symmetric])
  apply(metis ndastateref_h fun_belowD assms(1))
  using assms(2) by simp



lemma statesem_inv_h: assumes invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda) currentState input
                 \<Longrightarrow> Inv nextState"
          and trans_eq: "\<And>s. (Inv s \<Longrightarrow> (ndaTransition\<cdot>nda) s = (ndaTransition\<cdot>nda') s)"
          and P_def: "P = (\<lambda>A B. \<forall>s. (Inv s \<longrightarrow> A s = B s))"
  shows "P (ndaStateSem nda) (ndaStateSem nda')"
  apply(simp add: ndaStateSem_def)
  apply(rule gfp_parallel_induct [where P = "P"])
  using ndastatesem_mono apply auto[2]
   apply (auto simp add: P_def) 
  proof -
    fix x :: "'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set" and y :: "'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set" and s :: 'a and f :: "'b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>"
    assume a1: "\<forall>sbe. snd (f sbe) \<in> (ndaTransition\<cdot>nda) s sbe \<and> fst (f sbe) \<in> x (fst (snd (f sbe)))"
    assume a2: "\<forall>s. Inv s \<longrightarrow> x s = y s"
    assume a3: "Inv s"
    { fix ss :: "('b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>) \<Rightarrow> 'b\<^sup>\<surd>" and ssa :: "('b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>) \<Rightarrow> 'b\<^sup>\<surd>"
      have "Inv (fst (snd (f (ssa f))))"
        using a3 a1 by (metis image_eqI invariant)
      then have "\<exists>fa. sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case f s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) = sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case fa s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) \<and> snd (fa (ss fa)) \<in> (ndaTransition\<cdot>nda') s (ss fa) \<and> fst (fa (ssa fa)) \<in> y (fst (snd (fa (ssa fa))))"
        using a3 a2 a1 trans_eq by auto }
    then show "\<exists>fa. sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case f s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) = sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case fa s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) \<and> (\<forall>sa. snd (fa sa) \<in> (ndaTransition\<cdot>nda') s sa \<and> fst (fa sa) \<in> y (fst (snd (fa sa))))"
      by (metis (no_types))
  next
    fix x :: "'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set" and y :: "'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set" and s :: 'a and f :: "'b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>"
    assume a1: "\<forall>sbe. snd (f sbe) \<in> (ndaTransition\<cdot>nda') s sbe \<and> fst (f sbe) \<in> y (fst (snd (f sbe)))"
    assume a2: "\<forall>s. Inv s \<longrightarrow> x s = y s"
    assume a3: "Inv s"
    { fix ss :: "('b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>) \<Rightarrow> 'b\<^sup>\<surd>" and ssa :: "('b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>) \<Rightarrow> 'b\<^sup>\<surd>"
      have "Inv (fst (snd (f (ssa f))))"
        using a3 a1 by (metis (no_types) image_eqI invariant trans_eq)
      then have "\<exists>fa. sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case f s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) = sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case fa s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) \<and> snd (fa (ss fa)) \<in> (ndaTransition\<cdot>nda) s (ss fa) \<and> fst (fa (ssa fa)) \<in> x (fst (snd (fa (ssa fa))))"
        using a3 a2 a1 trans_eq by auto }
    then show "\<exists>fa. sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case f s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) = sb_step\<cdot> (\<lambda>s. \<Lambda> sa. case fa s of (c, a, s) \<Rightarrow> s \<Zcat>\<^sup>\<Omega> c\<cdot>sa) \<and> (\<forall>sa. snd (fa sa) \<in> (ndaTransition\<cdot>nda) s sa \<and> fst (fa sa) \<in> x (fst (snd (fa sa))))"
      by (metis (no_types))
  qed

theorem statesem_inv: assumes invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda) currentState input
                 \<Longrightarrow> Inv nextState"
          and trans_eq: "\<And>s. (Inv s \<Longrightarrow> (ndaTransition\<cdot>nda) s = (ndaTransition\<cdot>nda') s)"
          and "Inv s"
        shows "(ndaStateSem nda) s =  (ndaStateSem nda') s"
proof -
  have "\<forall>s. Inv s \<longrightarrow> (ndaStateSem nda) s =  (ndaStateSem nda') s"
    apply(rule statesem_inv_h [where Inv = "Inv"])
    by(auto simp add: assms)
  thus ?thesis
    by (simp add: assms(3)) 
qed

lemma sem_inv_h: assumes "ndaInitConfig\<cdot>nda = ndaInitConfig\<cdot>nda'"
      and "\<And>s. s\<in> fst ` ndaInitConfig\<cdot>nda \<Longrightarrow> ndaStateSem nda s = ndaStateSem nda' s"
    shows "ndaSem nda = ndaSem nda'"
  apply(rule)
  by(rule ndarefine_s[where f="id"],simp_all add: assms)+
  

theorem sem_inv: 
  assumes invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda) currentState input
                 \<Longrightarrow> Inv nextState"
      and "\<And>s. s\<in> fst ` ndaInitConfig\<cdot>nda \<Longrightarrow> Inv s"
      and "\<And>s. Inv s \<Longrightarrow> (ndaTransition\<cdot>nda) s = (ndaTransition\<cdot>nda') s"
      and "ndaInitConfig\<cdot>nda = ndaInitConfig\<cdot>nda'"
    shows "ndaSem nda = ndaSem nda'"
  apply(rule sem_inv_h,simp add: assms)
  by(rule statesem_inv[where Inv="Inv"],simp_all add: assms)

lemma ndastaterefine_inv_adm: assumes "\<And>s sbe t out. Inv s \<Longrightarrow> (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
and invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda1) currentState input
                 \<Longrightarrow> Inv nextState"
    shows "\<And>(x::'s::type \<Rightarrow> ('in::{chan, finite}\<^sup>\<Omega> \<rightarrow> 'out::chan\<^sup>\<Omega>) set) (y::'a::type \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set) (s::'s) trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 's \<times> 'out\<^sup>\<Omega>.
       (\<forall>s::'s. (Inv s \<longrightarrow> x s \<subseteq> y (f s))) \<Longrightarrow>
       Inv s \<Longrightarrow>
       trans \<in> ndaStateSem_helper nda1 x s \<Longrightarrow>
       sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
       \<in> (\<lambda>trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 'a \<times> 'out\<^sup>\<Omega>.
              sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
          ndaStateSem_helper nda2 y (f s)" 
proof - 
  fix x::"'s \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set"
  and y::"'a \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" 
  and s::"'s" 
  and trans::"'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 's \<times> 'out\<^sup>\<Omega>"
  assume a1: "\<forall>s::'s. Inv s \<longrightarrow> x s \<subseteq> y (f s)" and inv: "Inv s"
  and a4: "trans \<in> ndaStateSem_helper nda1 x s"
  have h1: "\<forall>sbe . snd (trans sbe) \<in> ((ndaTransition\<cdot>nda1) s sbe)"
    using a4 by(simp add: ndaStateSem_helper_def) 
  moreover have h2: "\<forall>sbe .  fst (trans sbe) \<in> x (fst (snd (trans sbe)))"
    using a4 by(simp add: ndaStateSem_helper_def) 
  ultimately have h3: "\<forall>sbe . (f (fst (snd(trans sbe))), snd (snd(trans sbe))) \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
    by (simp add: assms(1) inv)
  obtain trans2 where trans_def: "trans2 = (\<lambda> sbe. (fst (trans sbe), f (fst (snd(trans sbe))), snd (snd(trans sbe))))"
    by(simp)
  then have transF_def2: "\<forall>sbe. (trans2 sbe) = (fst (trans sbe), f (fst (snd(trans sbe))), snd (snd(trans sbe)))"
    by simp
  have "\<forall>sbe. snd (trans2 sbe) \<in> (ndaTransition\<cdot>nda2) (f s) sbe"
    using assms(1) transF_def2
    by (simp add: h3 inv)
  have h4: "trans2 \<in> ndaStateSem_helper nda2 y (f s)"
    apply(simp add: ndaStateSem_helper_def trans_def)
    using h3 apply auto
    using a1 h2 transF_def2 inv by (metis (no_types, opaque_lifting) h1 image_eqI invariant subset_iff) 
  have "sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
        = sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans2 sbe)) \<Zcat>\<^sup>\<Omega> fst (trans2 sbe)\<cdot>sb)"
    using transF_def2
    by auto
  then show "sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)
       \<in> (\<lambda>trans::'in\<^sup>\<surd> \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 'a \<times> 'out\<^sup>\<Omega>.
              sb_step\<cdot>(\<lambda>sbe::'in\<^sup>\<surd>. \<Lambda> (sb::'in\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
          ndaStateSem_helper nda2 y (f s)"
    using h4 inv by simp
qed

lemma ndastaterefine_inv_h:
   assumes "\<And>s sbe t out. Inv s \<Longrightarrow> (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
and invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda1) currentState input
                 \<Longrightarrow> Inv nextState"
  and P_def: "P = (\<lambda>A B. \<forall>s. Inv s \<longrightarrow> A s \<subseteq> B (f s))"
shows "P (ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) 
         (ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton))"
  unfolding ndastatesem_eq ndaStateSem2_def 
  apply(rule gfp_parallel_induct [where P = "P"])
  using ndastatesem2_mono apply blast+
   apply (auto simp add: P_def) 
  apply(subst ndastaterefine_inv_adm [where Inv="Inv"])
       apply(simp_all add: assms)
  done

lemma ndastaterefine_inv:
  assumes "\<And>s sbe t out. Inv s \<Longrightarrow> (t, out) \<in> (ndaTransition\<cdot>nda1) s sbe
              \<Longrightarrow> (f t, out)  \<in> (ndaTransition\<cdot>nda2) (f s) sbe"
      and invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda1) currentState input
                 \<Longrightarrow> Inv nextState"
      and "Inv s" 
    shows "ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton) s
        \<subseteq> ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton) (f s)"
proof -
  have "\<forall>s. Inv s \<longrightarrow> ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton) s \<subseteq> 
         (ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) (f s)"
    apply(rule ndastaterefine_inv_h[where f="f"])
    by(simp_all add: assms)
  then show ?thesis
    by (simp add: assms(3))
qed


lemma ndarefine_inv:
   assumes "\<And>s sbe t out. Inv s \<Longrightarrow> (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
and invariant: "\<And>currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` (ndaTransition\<cdot>nda1) currentState input
                 \<Longrightarrow> Inv nextState"
  and "\<And>s. s\<in> (fst `(ndaInitConfig\<cdot>nda1)) \<Longrightarrow> Inv s" 
  and "\<And>(s::'s) out::'out\<^sup>\<Omega>. (s, out) \<in> ndaInitConfig\<cdot>nda1 \<Longrightarrow> (f s, out) \<in> ndaInitConfig\<cdot>nda2"
shows "ndaSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton) \<subseteq> 
         (ndaSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton))"
  apply(rule ndarefine_s[where f="f"],simp add: assms)
  by(rule ndastaterefine_inv[where Inv="Inv"],simp_all add: assms)


end
