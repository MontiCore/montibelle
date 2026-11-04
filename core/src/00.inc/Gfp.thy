theory Gfp

imports Main


begin
default_sort type

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
  apply auto[6]
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
  apply(simp add: less_eq_prod_def gfp_upperbound; fail)
  apply(rule gfp_upperbound)
  apply(auto simp add: less_eq_prod_def)[1]
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
     apply (auto simp add: monoProd less_eq_prod_def)[2]
    by (simp add: P_step f_mono g_mono gfp_fixpoint)

  show "\<And>M::('a \<times> 'b) set. \<forall>m::'a \<times> 'b\<in>M. P m \<and> gfp (\<lambda>m::'a \<times> 'b. (f (fst m), g (snd m))) \<le> m \<Longrightarrow> M \<noteq> {} \<Longrightarrow> P (Inf M)"
    by (simp add: P_adm gfp_fst less_eq_prod_def)
qed


theorem gfp_parallel_induct: 
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

end