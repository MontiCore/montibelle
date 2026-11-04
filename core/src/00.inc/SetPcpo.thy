
theory SetPcpo
imports HOLCF
begin
default_sort type



instantiation set :: (type) po
begin
  definition less_set_def: "(\<sqsubseteq>) = (\<subseteq>)"
instance
apply intro_classes
apply (simp add: less_set_def)
apply (simp add: less_set_def)
apply (simp add: less_set_def)
done
end

lemma Union_is_lub: "A <<| \<Union>A"
apply (simp add: is_lub_def)
apply (simp add: is_ub_def)
apply (simp add: less_set_def Union_upper)
apply (simp add: Sup_least)
done

lemma lub_eq_Union: "lub = Union"
apply (rule ext)
apply (rule lub_eqI [OF Union_is_lub])
done

instance set :: (type) cpo
apply intro_classes
using Union_is_lub
apply auto
done

instance set :: (type) pcpo
apply intro_classes
apply (rule_tac x= "{}" in exI)
apply (simp add: less_set_def)
done

lemma UU_eq_empty: "\<bottom> = {}"
apply (simp add: less_set_def bottomI)
done

lemmas set_cpo_simps = less_set_def lub_eq_Union UU_eq_empty


instantiation bool :: po
begin
  definition less_bool_def: "(\<sqsubseteq>) = (\<longrightarrow>)"
instance
apply intro_classes
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply (simp add: less_bool_def)
apply auto
done
end

instance bool :: chfin
proof
  fix S:: "nat \<Rightarrow> bool"
  assume S: "chain S"
  then have "finite (range S)"
  apply simp
  done
  from S and this
  have "finite_chain S"
  apply (rule finite_range_imp_finch)
  done
  thus "\<exists> n. max_in_chain n S"
  apply (unfold finite_chain_def, simp)
  done
qed

instance bool :: cpo ..

instance bool :: pcpo
proof
  have "\<forall>y::bool. False \<sqsubseteq> y"
  unfolding less_bool_def
  apply simp
  done
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed



lemma adm_nonempty: "adm (\<lambda>A. \<exists>x. x \<in> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply force
done

lemma adm_in: "adm (\<lambda>A. x \<in> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
done

lemma adm_not_in: "adm (\<lambda>A. x \<notin> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
  done

lemma adm_Ball: "(\<And>x. adm (\<lambda>A. P A x)) \<Longrightarrow> adm (\<lambda>A. \<forall>x\<in>A. P A x)"
apply (simp add: Ball_def)
apply (simp add: adm_not_in)
done

lemma adm_Bex: "adm (\<lambda>A. Bex A P)"
apply (rule admI)
apply (simp add: lub_eq_Union)
done

lemma adm_subset: "adm (\<lambda>A. A \<subseteq> B)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply auto
done

lemma adm_superset: "adm (\<lambda>A. B \<subseteq> A)"
apply (rule admI)
apply (simp add: lub_eq_Union)
apply auto
done

lemma adm_subset_cont[simp]: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. f x \<subseteq> g x)"
  by (metis (full_types) SetPcpo.less_set_def adm_below)

lemmas adm_set_lemmas[simp] = adm_nonempty adm_in adm_not_in adm_Bex adm_Ball adm_subset adm_superset

lemma adm_in2: "adm (\<lambda>s. x \<in> f\<cdot>s)"
  by (simp add: adm_subst)

lemma adm_in3[simp]:"adm (\<lambda>x. z \<in> f\<cdot>x \<or> y \<in> f\<cdot>x)"
  by (simp add: adm_in2)

lemma adm_cmp: "adm P \<Longrightarrow> adm (\<lambda>x. P(g\<cdot>x))"
  by (simp add: adm_subst)

lemma adm_not_in_f [simp]: "adm (\<lambda>A. x \<notin> f\<cdot>A)"
  apply (rule admI)
  by (simp add: contlub_cfun_arg lub_eq_Union)

lemma adm_not_mem: "adm (\<lambda>s. x \<notin> f\<cdot>s)"
  using adm_cmp by force

lemma adm_not_mem2: "cont f \<Longrightarrow> adm (\<lambda>s. x \<notin> f s)"
  using adm_subst by force



lemma compact_empty: "compact {}"
apply (fold UU_eq_empty)
apply simp
done

lemma compact_insert: "compact A \<Longrightarrow> compact (insert x A)"
apply (simp add: compact_def)
apply (simp add: set_cpo_simps)
done

lemma finite_imp_compact: "finite A \<Longrightarrow> compact A"
apply (induct A set: finite)
apply (rule compact_empty)
apply (erule compact_insert)
done

lemma union_cont[simp, cont2cont]:"cont (\<lambda>S2. union S1 S2)"
  apply(rule contI)
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by (metis (no_types, lifting) UN_simps(3) Union_is_lub empty_not_UNIV lub_eq lub_eqI)

lemma image_cont[simp,cont2cont]:"cont (image f)"
  apply(rule Cpo.contI2)
  apply(rule monofunI)
  apply (simp add: image_mono SetPcpo.less_set_def)
  by(simp add: image_def lub_eq_Union SetPcpo.less_set_def,auto)

lemma adm_in_img2:"adm (\<lambda>s. x \<in> f`s)"
  by (simp add: adm_subst)

lemma image_cfun_cont[simp, cont2cont]:
  shows "cont (\<lambda> sps. {y . (\<exists> x \<in> sps . y = f\<cdot>x)})"
  using image_cont[of "Rep_cfun f"]
  unfolding image_def
  by simp

lemma Union_cont [cont2cont]: "cont \<Union>"
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: less_set_def Union_mono)
  apply (simp add: set_cpo_simps)
  by fastforce

lemma Union_set_image_cont[cont2cont]: "cont (\<lambda>a. \<Union> (set ` a))"
  apply (rule cont_compose [where f="\<lambda>a. set ` a"])
  by (intro cont2cont)+

lemma lub_unionL:"chain Y \<Longrightarrow> (\<Squnion>i. (union x (Y i))) = ((union x (\<Squnion>i. Y i)))"
  by (metis cont2contlubE union_cont)

lemma lub_unionR:"chain Y \<Longrightarrow> (\<Squnion>i. (union (Y i) x)) = ((union (\<Squnion>i. Y i) x))"
  using cont2contlubE union_cont
  by (metis (mono_tags, lifting) image_cong sup_commute)

lemma lub_union_pairwise:"chain Y \<Longrightarrow> chain Z \<Longrightarrow> (\<Squnion>i. (union (Y i) (Z i))) = ((union (\<Squnion>i. Y i) (\<Squnion>i. Z i)))"
  apply(simp add: lub_eq_Union)
  by (simp add: complete_lattice_class.SUP_sup_distrib)

lemma subset_neg_implies_total:"{x\<in>{y. \<not> P y}. R x } \<subseteq> {x\<in>{y. P y}.R x } \<Longrightarrow> {x\<in>{y. P y}.R x } = {x . R x }"
  by blast

lemma lub_partition:"(\<Squnion>x\<in>{i. Y i = \<bottom>}. S ) \<subseteq> (\<Squnion>x\<in>{i. \<not>(Y i = \<bottom>)}. S )
 \<Longrightarrow> (\<Squnion>x\<in>{i. \<not>(Y i = \<bottom>)}. S ) = (\<Squnion>x. S )"
  apply auto
  apply (metis UN_iff lub_eq_Union)
  by (metis (mono_tags, lifting) UN_iff lub_eq_Union mem_Collect_eq subset_iff)

lemma set_monofun_cfun:"x \<sqsubseteq> y \<Longrightarrow> f \<sqsubseteq> g \<Longrightarrow> f\<cdot>x\<subseteq> g\<cdot>y"
  using SetPcpo.less_set_def
  by (metis monofun_cfun)

definition setify_on::"'m set \<Rightarrow> ('m::type \<Rightarrow> ('n::type set)) \<Rightarrow> ('m \<Rightarrow> 'n) set" where
"setify_on Dom \<equiv> \<lambda> f. {g. \<forall>m\<in>Dom. g m \<in> (f m)}"

definition setify::"('m::type \<Rightarrow> ('n::type set)) \<Rightarrow> ('m \<Rightarrow> 'n) set" where
"setify \<equiv> \<lambda> f. {g. \<forall>m. g m \<in> (f m)}"




thm setify_def
lemma setify_on_mono[simp]: "\<And> Dom. monofun (\<lambda> f. {g. \<forall>m\<in>Dom. g m \<in> (f m)})"
proof (rule monofunI, simp add: less_set_def, rule subsetI)
  fix x y::"'m::type \<Rightarrow> ('n::type set)"
  fix Dom::"'m set"
  fix xa:: "'m \<Rightarrow> 'n"
  assume a1:"x \<sqsubseteq> y"
  assume a2: "xa \<in> {g. \<forall>m\<in>Dom. g m \<in> x m}"
  have f0: "\<And>m. x m \<sqsubseteq> y m"
    by (simp add: a1 fun_belowD)
  have f1: "\<And>m. m \<in> Dom \<Longrightarrow> xa m \<in> x m"
    using a2 by blast
  have f2: "\<And>m. m \<in> Dom \<Longrightarrow> xa m \<in> y m"
    by (metis SetPcpo.less_set_def f0 f1 subsetCE)
  show "xa \<in> {g. \<forall>m\<in>Dom. g m \<in> y m}"
    using f2 by blast
qed

lemma setify_on_empty:"\<And> Dom. sbe \<in> Dom \<Longrightarrow> f sbe = {} \<Longrightarrow> setify_on Dom f = {}"
  apply(simp add: setify_on_def)
  by (metis empty_iff)

lemma setify_on_notempty_ex:"setify_on Dom f \<noteq> {} \<Longrightarrow> \<exists>g.(\<forall>m \<in> Dom. g m \<in> (f m))"
  by (metis (no_types, lifting) Collect_empty_eq setify_on_def)

lemma setify_on_notempty:assumes "\<forall>m \<in> Dom. f m \<noteq> {}" shows" setify_on Dom f \<noteq> {}"
proof -
  have "\<forall>m \<in> Dom. (\<exists>x. x\<in>((f m)))"
    by (metis all_not_in_conv assms)
  have "\<forall>m \<in> Dom. (\<lambda>e. SOME x. x\<in> (f e)) m \<in> (f m)"
    by (metis assms some_in_eq)
  then have "\<exists>x::'a \<Rightarrow> 'b. \<forall>m::'a \<in> Dom. x m \<in> (f m)"
    by(rule_tac x="(\<lambda>e. SOME x. x\<in> (f e))" in exI, auto)
  thus ?thesis by(simp add: setify_on_def)
qed

lemma setify_on_final:assumes "\<forall>m \<in> Dom. f m \<noteq> {}" and "x \<in> (f m)"
  shows"\<exists>g\<in>((setify_on Dom f)). g m = x"
proof -
  have "\<exists>g.(\<forall>m \<in> Dom. g m \<in> (f m))"
    by(simp add: setify_on_notempty setify_on_notempty_ex assms(1))
  then obtain g where g_def:"(\<forall>m \<in> Dom. g m \<in> (f m))"
    by auto
  have g2_def:"\<forall>n \<in> Dom. (\<lambda>e. if e = m then x else g e) n \<in> (f n)"
    by (simp add: assms(2) g_def)
  then have "\<exists>g::'a \<Rightarrow> 'b. (\<forall>m::'a \<in> Dom. g m \<in> (f m)) \<and> g m = x"
    by(rule_tac x="(\<lambda>e. if e = m then x else g e)" in exI, auto)
  thus ?thesis by(simp add: setify_on_def)
qed



lemma setify_mono[simp]:"monofun (\<lambda>f. {g. \<forall>m. g m \<in> (f m)})"
  apply(rule monofunI)
  by (simp add: SetPcpo.less_set_def fun_below_iff subset_iff)

lemma setify_empty:"f m = {} \<Longrightarrow> setify f = {}"
  apply(simp add: setify_def)
  by (metis empty_iff)

lemma setify_notempty:assumes "\<forall>m. f m \<noteq> {}" shows" setify f \<noteq> {}"
proof(simp add: setify_def)
  have "\<forall>m. \<exists>x. x\<in>((f m))"
    by (metis all_not_in_conv assms)
  have "\<forall>m. (\<lambda>e. SOME x. x\<in> (f e)) m \<in> (f m)"
    by (metis assms some_in_eq)
  then show "\<exists>x::'a \<Rightarrow> 'b. \<forall>m::'a. x m \<in> (f m)"
    by(rule_tac x="(\<lambda>e. SOME x. x\<in> (f e))" in exI, auto)
qed

lemma setify_notempty_ex:"setify f \<noteq> {} \<Longrightarrow> \<exists>g.(\<forall>m. g m \<in> (f m))"
  by(simp add: setify_def)

lemma setify_final:assumes "\<forall>m. f m \<noteq> {}" and "x \<in> (f m)" shows"\<exists>g\<in>((setify f)). g m = x"
proof(simp add: setify_def)
  have "\<exists>g.(\<forall>m. g m \<in> (f m))"
    by(simp add: setify_notempty setify_notempty_ex assms(1))
  then obtain g where g_def:"(\<forall>m. g m \<in> (f m))"
    by auto
  have g2_def:"\<forall>n. (\<lambda>e. if e = m then x else g e) n \<in> (f n)"
    by (simp add: assms(2) g_def)
  then show "\<exists>g::'a \<Rightarrow> 'b. (\<forall>m::'a. g m \<in> (f m)) \<and> g m = x"
    by(rule_tac x="(\<lambda>e. if e = m then x else g e)" in exI, auto)
qed


(*
inductive setSize_helper :: "'a set \<Rightarrow> nat \<Rightarrow> bool"
  where
    "setSize_helper {} 0"
  |  "setSize_helper A X \<and> a \<notin> A \<Longrightarrow> setSize_helper (insert a A) (Suc X)"

definition setSize :: "'a set \<Rightarrow> lnat"
  where
  "setSize X \<equiv> if (finite X) then Fin (THE Y. setSize_helper X Y) else \<infinity>"


lemma setSizeEx: assumes "finite X" shows "\<exists> Y. setSize_helper X Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  using setSize_helper.intros(1) apply auto[1]
  by (metis setSize_helper.simps)

lemma setSize_remove: "y \<in> F \<and> setSize_helper (F - {y}) A \<longrightarrow> setSize_helper F (Suc A)"
  by (metis Diff_insert_absorb Set.set_insert setSize_helper.intros(2))


lemma setSizeBack_helper:
  assumes "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc A) \<and> x \<notin> F) \<longrightarrow> setSize_helper F A"
  shows "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) \<longrightarrow> setSize_helper F (Suc A)"
proof -
have b0: "\<And>A::nat. \<forall>(F::'a set) x::'a. ((setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F)
  \<longrightarrow> (\<exists> y. y \<in> (insert x F) \<and> setSize_helper ((insert x F) - {y}) (Suc A)))"
    by (metis Diff_insert_absorb add_diff_cancel_left' insertI1 insert_not_empty plus_1_eq_Suc setSize_helper.simps)
have b1: "\<forall>(F::'a set) (x::'a) y::'a. ((finite F \<and> setSize_helper (insert x (F - {y})) (Suc A) \<and> x \<notin> F)
  \<longrightarrow> setSize_helper (F - {y}) A)"
  using assms by auto
have b2: "\<forall>(F::'a set) x::'a. (setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F)
  \<longrightarrow> ((\<exists> y. (y\<noteq>x \<and> y \<in> F \<and> setSize_helper (insert x (F - {y})) (Suc A))) \<or> setSize_helper F (Suc A))"
  by (metis Diff_insert_absorb b0 empty_iff insert_Diff_if insert_iff)
have b3: "\<forall>(F::'a set) x::'a. (setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F \<and> finite F)
  \<longrightarrow> ((\<exists> y. (y\<noteq>x \<and> y \<in> F \<and> setSize_helper (F - {y}) A)) \<or> setSize_helper F (Suc A))"
  by (meson b1 b2)
show "\<forall>(F::'a set) x::'a. (finite F \<and> setSize_helper (insert x F) (Suc (Suc A)) \<and> x \<notin> F) \<longrightarrow> setSize_helper F (Suc A)"
  by (meson b3 setSize_remove)
qed


lemma setSizeBack: "\<And> F x. (finite F \<and> setSize_helper (insert x F) (Suc A) \<and> x \<notin> F) \<Longrightarrow> setSize_helper F A"
  apply (induction A)
  apply (metis Suc_inject empty_iff insertI1 insert_eq_iff nat.distinct(1) setSize_helper.simps)
  using setSizeBack_helper by blast


lemma setSizeonlyOne: assumes "finite X" shows "\<exists>! Y. setSize_helper X Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  apply (metis empty_not_insert setSize_helper.simps)
  by (metis insert_not_empty setSizeBack setSize_helper.intros(2) setSize_helper.simps)

lemma setSizeSuc: assumes "finite X" and "z \<notin> X" shows "setSize (insert z X) = lnsuc\<cdot>(setSize X)"
  apply (simp add: setSize_def)
  using assms setSizeonlyOne
  by (metis (mono_tags, lifting) Diff_insert_absorb finite.insertI insertI1 setSize_remove theI_unique)

lemma setSizeEmpty: "setSize {} = Fin 0"
  by (metis finite.emptyI setSize_def setSize_helper.intros(1) setSizeonlyOne theI_unique)

lemma setSizeSingleton: "setSize {x} = lnsuc\<cdot>(Fin 0)"
  by (simp add: setSizeEmpty setSizeSuc)

lemma setsize_union_helper1:
  assumes "finite F"
      and "x \<notin> F"
      and "x \<notin> X"
    shows "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F \<Longrightarrow>
       setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
proof -
  assume a0: "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F"
  have b0: "X \<union> insert x F = insert x (X \<union> F)"
    by simp
  have b1: "setSize (X \<union> insert x F) = lnsuc\<cdot>(setSize (X \<union> F))"
    by (metis Un_iff Un_infinite assms(1) assms(2) assms(3) b0 finite_UnI fold_inf setSizeSuc setSize_def sup_commute)
  have b2: "setSize (X \<inter> insert x F) = setSize (X \<inter> F)"
    by (simp add: assms(3))
  show "setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
    by (metis (no_types, lifting) a0 ab_semigroup_add_class.add_ac(1) add.commute assms(1) assms(2)
      b1 b2 lnat_plus_suc setSizeSuc)
qed

lemma setsize_union_helper2:
  assumes "finite F"
      and "x \<notin> F"
      and "x \<in> X"
    shows "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F \<Longrightarrow>
       setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
proof -
  assume a0: "setSize (X \<union> F) + setSize (X \<inter> F) = setSize X + setSize F"
  have b0: "setSize (X \<union> insert x F) = setSize (X \<union> F)"
    by (metis Un_Diff_cancel assms(3) insert_Diff1)
  have b1: "setSize (X \<inter> insert x F) =  lnsuc\<cdot>(setSize (X \<inter> F))"
    by (simp add: assms(1) assms(2) assms(3) setSizeSuc)
  show "setSize (X \<union> insert x F) + setSize (X \<inter> insert x F) = setSize X + setSize (insert x F)"
    by (metis a0 ab_semigroup_add_class.add_ac(1) assms(1) assms(2) b0 b1 lnat_plus_suc setSizeSuc)
qed

lemma setsize_union_helper3: assumes "finite X" and "finite Y"
  shows "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
  apply (rule finite_induct)
  apply (simp add: assms)
  apply simp
  by (meson setsize_union_helper1 setsize_union_helper2)

lemma setsize_union_helper4: assumes "infinite X \<or> infinite Y"
  shows "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
proof -
  have b0: "setSize (X \<union> Y) = \<infinity>"
    by (metis (full_types) assms infinite_Un setSize_def)
  have b1: "setSize X = \<infinity> \<or> setSize Y = \<infinity>"
    by (meson assms setSize_def)
  show ?thesis
    using b0 b1 plus_lnatInf_r by auto
qed

lemma setsize_union: "setSize (X \<union> Y) + setSize (X \<inter> Y) = setSize X + setSize Y"
  by (meson setsize_union_helper3 setsize_union_helper4)

lemma setsize_union_disjoint: assumes "X \<inter> Y = {}"
  shows "setSize (X \<union> Y) = setSize X + setSize Y"
  by (metis Fin_02bot add.left_neutral assms bot_is_0 lnat_plus_commu setSizeEmpty setsize_union)

lemma setsize_subset_union: assumes "X \<subseteq> Y"
  shows "setSize (X \<union> Y) = setSize Y"
  by (simp add: assms sup.absorb2)

lemma set_union_ins: "\<And> F G x. setSize (F \<union> G) \<le> setSize (F \<union> (insert x G))"
  by (metis Fin_Suc Fin_leq_Suc_leq  Un_insert_right finite_insert insert_absorb lnat_po_eq_conv
  setSizeSuc setSize_def)

lemma setsize_mono_union_helper1:
  assumes "finite F" and "finite G"
  shows "setSize F \<le> setSize (F \<union> G)"
proof -
  have b0:  "\<And>P. P = (\<lambda>G. setSize F \<le> setSize (F \<union> G)) \<Longrightarrow> P G"
    by (metis assms(2) finite_induct order_refl set_union_ins sup_bot.right_neutral trans_lnle)
  have b1: "(\<lambda>G. setSize F \<le> setSize (F \<union> G)) G"
    using b0 by auto
  show "setSize F \<le> setSize (F \<union> G)"
    by (simp add: b1)
qed

lemma setsize_mono_union_helper2:
  assumes "infinite F \<or> infinite G"
  shows "setSize F \<le> setSize (F \<union> G)"
proof -
  have b0: "setSize (F \<union> G) = \<infinity>"
    by (meson assms infinite_Un setSize_def)
  show ?thesis
    by (simp add: b0)
qed

lemma setsize_mono_union: "setSize F \<le> setSize (F \<union> G)"
  by (meson setsize_mono_union_helper1 setsize_mono_union_helper2)


lemma setsize_mono:
  assumes "F \<subseteq> G"
  shows "setSize F \<le> setSize G"
  by (metis Un_absorb1 assms setsize_mono_union)

*)




definition setflat :: "'a set set \<rightarrow> 'a set" where
"setflat = (\<Lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"

lemma setflat_mono: "monofun (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule monofunI)
  apply auto[1]
  apply (simp add: less_set_def)
  apply (rule subsetI)
  by auto


lemma setflat_cont[simp, cont2cont]: "cont (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule contI2)
  using setflat_mono apply simp
  apply auto[1]
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by blast

lemma setflat_insert: "setflat\<cdot>S = {K  | Z K. K\<in>Z \<and> Z \<in>S}"
  unfolding setflat_def
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 setflat_cont)

lemma setflat_empty:"(setflat\<cdot>S = {}) \<longleftrightarrow> (\<forall>x\<in>S. x = {})"
  by(simp add: setflat_insert, auto)

lemma setflat_not_empty:"(setflat\<cdot>S \<noteq> {}) \<longleftrightarrow> (\<exists>x\<in>S. x \<noteq> {})"
  by (simp add: setflat_empty)

lemma setflat_obtain: assumes "f \<in> setflat\<cdot>S"
  shows "\<exists> Z \<in> S. f \<in> Z"
proof -
  have "f \<in> {a. \<exists>A aa. a = aa \<and> aa \<in> A \<and> A \<in> S}"
    by (metis assms setflat_insert)
  then show ?thesis
    by blast
qed

lemma setflat_union: "setflat\<cdot>S = \<Union>S"
  apply (simp add: setflat_insert)
  apply (subst Union_eq)
  by auto

lemma setflatten_mono2: assumes "\<And>b. b\<in>S1 \<Longrightarrow>( \<exists>c. c\<in>S2 \<and> b \<subseteq> c)"
  shows "setflat\<cdot>S1 \<subseteq> setflat\<cdot> S2"
  by (metis Sup_mono assms setflat_union)

lemma setfilter_easy: "Set.filter (\<lambda>f. True) X = X"
  using member_filter by auto

lemma setfilter_cont[simp, cont2cont]: "cont (Set.filter P)"
  by (simp add: contI2 SetPcpo.less_set_def lub_eq_Union monofun_def subset_eq)




definition seqComp  :: "(('In::cpo \<rightarrow> 'Intern::cpo) set) \<rightarrow> (('Intern \<rightarrow> 'Out) set)
    \<rightarrow> (('In \<rightarrow> 'Out::cpo) set)" where
"seqComp = (\<Lambda> sps1 sps2 . {spf2 oo spf1 | spf1 spf2.
                                spf1 \<in> sps1 \<and> spf2 \<in> sps2})"

abbreviation seqComp_abbr ::
"(('In::cpo \<rightarrow> 'Intern::cpo) set) \<Rightarrow> (('Intern \<rightarrow> 'Out) set)
    \<Rightarrow> (('In \<rightarrow> 'Out::cpo) set)"  (infixr "\<then>" 100)
where "f \<then> g == seqComp\<cdot>f\<cdot>g"

lemma cont_oo_set[simp]:"cont (\<lambda>sps2. {spf2 oo spf1 |spf1 spf2. spf1 \<in> sps1 \<and> spf2 \<in> sps2})"
  by(auto simp add: cont_def lub_eq_Union is_lub_def is_ub_def less_set_def)

lemma cont_oo_set2[simp]:"cont (\<lambda>sps1. \<Lambda> sps2. {spf2 oo spf1 |spf1 spf2. spf1 \<in> sps1 \<and> spf2 \<in> sps2})"
  apply(rule contI)
  apply(rule is_lubI)
  apply(rule is_ubI)
  apply(rule cfun_belowI)
  apply simp
  apply(simp add: less_set_def lub_eq_Union)
   apply auto[2]
   apply auto[1]
  apply(rule cfun_belowI)
  apply simp
  apply(auto simp add: cfun_below_iff less_set_def lub_eq_Union is_ub_def)[1]
  by blast

lemma seqcomp_insert:"sps1 \<then> sps2 ={spf2 oo spf1 | spf1 spf2.
                                spf1 \<in> sps1 \<and> spf2 \<in> sps2} "
  by(simp add: seqComp_def)

lemma seqComp_nempty_mp1: "F \<then> G \<noteq> {} \<Longrightarrow> G \<noteq> {}"
  using seqcomp_insert by auto

lemma seqComp_nempty_mp2: "F \<then> G \<noteq> {} \<Longrightarrow> F \<noteq> {}"
  using seqcomp_insert by auto

lemma seqcomp_image:"{f} \<then> sps2 =(\<lambda>spf. spf oo f) ` sps2"
  by(auto simp add: seqcomp_insert image_iff)

lemma seqcomp_ID[simp]:"{ID} \<then> sps2 = sps2"
  by(auto simp add: seqcomp_image)

lemma seqcomp_image2:"sps2 \<then> {f} =(\<lambda>spf. f oo spf) ` sps2"
  by(auto simp add: seqcomp_insert image_iff)

lemma seqcomp_ID2[simp]:"sps2 \<then> {ID} = sps2"
  by(auto simp add: seqcomp_image2)

lemma seqcomp_image3: "{f} \<then> {g} = {g oo f}"
  by(auto simp add: seqcomp_image)

lemma seqcomp_image_sps: "{f} \<then> SPS \<then> {g} = (\<lambda>x. g oo x oo f) ` SPS"
  apply(auto simp add: seqcomp_insert)[1]
  using Cfun.cfun.Rep_cfun_inject apply fastforce
  by (metis (no_types, lifting) cfcomp2 cfun_eqI)

lemma seqcomp_sps_elem:
  assumes "spf \<in> SPS"
  shows "g oo spf oo f \<in> {f} \<then> SPS \<then> {g}"
  apply(subst seqcomp_image_sps)
  using assms by blast

lemma seqcomp_assoc: "(FST \<then> SND) \<then> THRD = FST \<then> (SND \<then> THRD)"
  apply(auto simp add: seqcomp_insert)[1]
  using Cfun.cfun.Rep_cfun_inject by fastforce+

lemma seqcomp_subset:
  assumes "f1 \<subseteq> f2"
    and "g1 \<subseteq> g2"
  shows "f1 \<then> g1 \<subseteq> f2 \<then> g2"
  apply (simp add: seqcomp_insert)
  apply (rule subsetI)
  using assms by blast

lemma seqcomp_nempty:
  assumes "f \<noteq> {}"
    and "g \<noteq> {}"
  shows "f \<then> g \<noteq> {}"
  apply (simp add: seqcomp_insert)
  using assms(1) assms(2) by blast

lemma seqcomp_wrapped_subset1:
  assumes sps_ref: "X \<subseteq> Y"
      and in_mapping: "f2 oo f1 = f"
      and out_mapping: "g2 oo g1 = g"
    shows "{f1} \<then> {f2} \<then> X \<then> {g1} \<then> {g2} \<subseteq> {f} \<then> Y \<then> {g}"
  apply(subst seqcomp_assoc[symmetric])
  apply(subst seqcomp_image3)
  apply(subst in_mapping)
  apply(subst seqcomp_image3)
  apply(subst out_mapping)
  using sps_ref by (simp add: seqcomp_subset)

lemma seqcomp_wrapped_subset2:
  assumes sps_ref: "X \<subseteq> Y"
      and in_mapping: "f2 oo f1 = f"
      and out_mapping: "g2 oo g1 = g"
    shows "{f} \<then> X \<then> {g} \<subseteq> {f1} \<then> {f2} \<then> Y \<then> {g1} \<then> {g2}"
  apply(subst(2) seqcomp_assoc[symmetric])
  apply(subst seqcomp_image3)
  apply(subst in_mapping)
  apply(subst seqcomp_image3)
  apply(subst out_mapping)
  using sps_ref by (simp add: seqcomp_subset)

lemma seqcomp_wrapped_eq:
  assumes in_mapping: "f2 oo f1 = f"
      and out_mapping: "g2 oo g1 = g"
    shows "{f1} \<then> {f2} \<then> X \<then> {g1} \<then> {g2} = {f} \<then> X \<then> {g}"
  apply(subst seqcomp_assoc[symmetric])
  apply(subst seqcomp_image3)
  apply(subst in_mapping)
  apply(subst seqcomp_image3)
  apply(subst out_mapping)
  by simp


text \<open>It may happen that for streams \<open>i\<^sub>1,i\<^sub>2\<close> we have \<open>f\<^sub>1(i\<^sub>1) = o\<^sub>1\<close> and
\<open>f\<^sub>2(i\<^sub>2) = o\<^sub>2\<close>, but that no "joint" \<open>f\<in>S\<close> exists, where \<open>f(i\<^sub>1) = o\<^sub>1\<close> and
\<open>f(i\<^sub>2) = o\<^sub>2\<close>. We then speak of an incomplete specification \<open>S\<close>. From an
observational point, \<open>S\<close> and \<open>S\<union>{f}\<close> cannot be distinguished, but when refinement
is used to specialize \<open>S\<close>, this may become a deficit. \<close>

definition spsComplete ::"('I1::cpo \<rightarrow> 'O1::cpo) set \<Rightarrow> ('I1 \<rightarrow> 'O1) set"
  where "spsComplete sps = {spf. \<forall>sb. \<exists>spf2\<in>sps. spf\<cdot>sb = spf2\<cdot>sb}"


text\<open>We give a small example for the completion of two components on
  the datatype containg just \<open>a\<close> and \<open>b\<close>.
 \<^item> \<open>spsConst = {[a \<mapsto> a, b \<mapsto> a], [a \<mapsto> b, b \<mapsto> b]}\<close>
 \<^item> \<open>spsID = {[a \<mapsto> a, b \<mapsto> b], [a \<mapsto> b, b \<mapsto> a]}\<close>
\<close>


theorem spscomplete_belowI:
  assumes "\<And>spf sb. spf\<in>S1 \<Longrightarrow> \<exists>spf2 \<in> S2. spf\<cdot>sb = spf2\<cdot>sb"
  shows "S1 \<subseteq> spsComplete S2"
  unfolding spsComplete_def
  using assms by auto


theorem spscomplete_below: "sps \<subseteq> spsComplete sps"
  using spscomplete_belowI by auto

text\<open>After applying the @{const spsComplete} function the \gls{sps} is indeed
 complete. Applying the function a second time does not change the
component anymore. Completion is idempotent.\<close>

theorem spscomplete_complete [simp]:
 "spsComplete (spsComplete sps) = spsComplete sps"
  unfolding spsComplete_def apply auto[1]
  by metis


definition spsIsComplete :: "('I1::cpo \<rightarrow> 'O1::cpo) set \<Rightarrow> bool" where
"spsIsComplete sps \<equiv> (spsComplete sps) = sps"


theorem spscomplete_empty[simp]: "spsIsComplete {}"
  unfolding spsComplete_def spsIsComplete_def by auto


theorem spscomplete_one[simp]: "spsIsComplete {f}"
  unfolding spsComplete_def spsIsComplete_def apply auto[1]
  by (simp add: cfun_eqI)


theorem spscomplete_univ[simp]: "spsIsComplete UNIV"
  by (simp add: spsIsComplete_def spscomplete_below top.extremum_uniqueI)

lemma spscomplete_consistency[simp]:"spsComplete S \<noteq> {} \<Longrightarrow> S \<noteq> {}"
  using spscomplete_empty by(auto simp add: spsIsComplete_def)

lemma spscomplete_preserve_pred:
  assumes "\<And>spf1. spf1\<in> SPS \<Longrightarrow> (\<And>i. P i (spf1\<cdot>i))"
      and "spf2\<in> spsComplete SPS"
    shows "P i (spf2\<cdot>i)"
proof-
  have "SPS \<noteq> {}"
    using assms(2) spscomplete_consistency by (metis empty_iff)
  then obtain spf1 where spf1_def:"spf2\<cdot>i = spf1\<cdot>i " and "spf1\<in> SPS"
    using assms apply(auto simp add: spsComplete_def)[1]
    by blast
  then show ?thesis
    by (simp add: assms(1))
qed


lemma spscomplete_io_rel[simp]:
  shows"spsComplete {f |f.  \<forall>i. P i (f\<cdot>i)} = {f |f. \<forall>i. P i (f\<cdot>i)}"
  apply(simp add: spsComplete_def)
  by metis

lemma spsiscomplete_io_rel[simp]:"spsIsComplete {f |f.  \<forall>i. P i (f\<cdot>i)}"
  apply(simp add: spsIsComplete_def spsComplete_def)
  by metis




text\<open>The @{const spsComplete} function is monotonic.
 Therefore if a component \<open>sps1\<close> refines a second component \<open>sps2\<close>
  then this also holds after completion.\<close>

theorem spscomplete_mono: assumes "sps1 \<subseteq> sps2"
  shows "spsComplete sps1 \<subseteq> spsComplete sps2"
  apply(rule spscomplete_belowI)
  unfolding spsComplete_def
  apply (auto)[1]
  by (meson assms in_mono)



lemma seqcomp_complete_belowI:
  assumes "A \<subseteq> spsComplete C" and "B \<subseteq>spsComplete D"
  shows  "A \<then> B  \<subseteq> spsComplete( C \<then> D)"
proof(rule spscomplete_belowI)
  fix spf sb
  assume as: "spf \<in> A \<then> B"
  obtain spfA and spfB where "spfA \<in> A" and "spfB \<in> B" and "spf = spfB oo spfA"
    using as by(auto simp add: seqcomp_insert)

  obtain spfC where "spfC \<in> C" and "spfC\<cdot>sb = spfA\<cdot>sb"
    using assms(1) \<open>spfA \<in> A\<close> apply(auto simp add: spsComplete_def)[1]
    apply (simp add: subset_iff) by metis
  obtain spfD where "spfD \<in> D" and "spfD\<cdot>(spfA\<cdot>sb) = spfB\<cdot>(spfA\<cdot>sb)"
    using assms(2) \<open>spfB \<in> B\<close> apply(auto simp add: spsComplete_def)[1]
    apply(simp add: subset_iff) by metis

  have "spf\<cdot>sb = (spfD oo spfC)\<cdot>sb"
    by(simp add: \<open>spf = spfB oo spfA\<close> \<open>spfC\<cdot>sb = spfA\<cdot>sb\<close> \<open>spfD\<cdot>(spfA\<cdot>sb) = spfB\<cdot>(spfA\<cdot>sb)\<close>)
  moreover have "(spfD oo spfC) \<in> ( C \<then> D)"
    using \<open>spfC \<in> C\<close> \<open>spfD \<in> D\<close> by(auto simp add: seqcomp_insert)
  ultimately show "\<exists>spf2\<in>C \<then> D. spf\<cdot>sb = spf2\<cdot>sb"
    by blast
qed

lemma seqcomp_self_below: "spsComplete A \<then> spsComplete B  \<subseteq> spsComplete( A \<then> B)"
  by (simp add: seqcomp_complete_belowI subsetI)


end
