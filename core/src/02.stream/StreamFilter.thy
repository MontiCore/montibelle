theory StreamFilter
imports Stream StreamWhile

begin
text \<open>@{term sfilter}: Remove all elements from the stream which are
  not included in the given set.\<close>
definition sfilter    :: "'a set \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"sfilter M \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          (if (a \<in> M) then \<up>a \<Zcat> (h\<cdot>(srt\<cdot>s)) else h\<cdot>(srt\<cdot>s))))"




abbreviation sfilter_abbr :: "'a set \<Rightarrow> 'a stream \<Rightarrow> 'a stream" ("(_ \<ominus> _)" [66,65] 65)
where "F \<ominus> s \<equiv> sfilter F\<cdot>s"


definition sboolfilter::  "'a stream \<rightarrow> bool stream \<rightarrow> 'a stream" where
"sboolfilter \<equiv> \<Lambda> i ora.  sprojfst\<cdot>({d. snd d} \<ominus> (szip\<cdot>i\<cdot>ora))"

fixrec sbool_apply :: "bool stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"sbool_apply\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"sbool_apply\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"sbool_apply\<cdot>((up\<cdot>a) && as)\<cdot>((up\<cdot>b) && bs) = 
  (if (undiscr a =  False) then (updis False) && sbool_apply\<cdot>as\<cdot>((up\<cdot>b) && bs)
                        else up\<cdot>b && sbool_apply\<cdot>as\<cdot>bs)"


subsection \<open>@{term sfilter}\<close>

text \<open>basic properties of @{term sfilter}\<close>

lemma sfilter_cont[simp]: "cont(\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          (if (a \<in> M) then \<up>a \<Zcat> (h\<cdot>(srt\<cdot>s)) else h\<cdot>(srt\<cdot>s))))"
  by(intro cont2cont)

lemma strict_sfilter[simp]: "sfilter M\<cdot>\<epsilon> = \<epsilon>"
by (subst sfilter_def [THEN fix_eq2], simp)

lemma sfilter_in[simp]: 
  "a \<in> M \<Longrightarrow> sfilter M\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> sfilter M\<cdot>s" 
by (subst sfilter_def [THEN fix_eq2], simp)

lemma sfilter_nin[simp]: 
  "a \<notin> M \<Longrightarrow> sfilter M\<cdot>(\<up>a \<Zcat> s) = sfilter M\<cdot>s" 
by (subst sfilter_def [THEN fix_eq2], simp)

lemma sfilter_in_sup[simp]: "a \<in> M \<Longrightarrow> sfilter M\<cdot>(\<up>a) = \<up>a"
by (subst sfilter_def [THEN fix_eq2], simp)

lemma sfilter_notin_sup[simp]: "a \<notin> M \<Longrightarrow> sfilter M\<cdot>(\<up>a) = \<epsilon>"
by (subst sfilter_def [THEN fix_eq2], simp)

lemma sfilter_empty[simp]: "sfilter {}\<cdot>s = \<epsilon>"
  by (induction s; simp)

lemma smapfilter: assumes "\<And>msg. msg \<notin> S \<Longrightarrow> f msg \<notin> f ` S"
  shows "smap f\<cdot>(S\<ominus>s) = (f`S) \<ominus> (smap f\<cdot>s)"
  apply(induction s; simp)
  apply(rename_tac msg stream, case_tac "msg\<in>S"; simp)
  apply(subst sfilter_nin, simp add: assms)
  ..

text \<open>@{term sfilter} and @{term sinftimes}\<close>

lemma sfilter_sinftimes_in[simp]: 
  "sfilter {a}\<cdot>(sinftimes (\<up>a)) = sinftimes (\<up>a)"
apply (rule stream.take_lemma)
apply (induct_tac n, auto)
apply (subst sinftimes_unfold, simp)
apply (rule sym)
by (subst sinftimes_unfold, simp)

lemma sfilter_sinftimes_nin:
  "a \<notin> F \<Longrightarrow> (F \<ominus> (sinftimes (\<up>a))) = \<epsilon>"
proof -
  assume a_nin_F: "a \<notin> F"
  have "\<And>i. (F \<ominus> (stake i\<cdot>(sinftimes (\<up>a)))) = \<epsilon>"
  proof (induct_tac i, simp_all)
    fix n assume "F \<ominus> (stake n\<cdot>(sinftimes (\<up>a))) = \<epsilon>"
    hence "F \<ominus> (stake (Suc n)\<cdot>(\<up>a \<Zcat> sinftimes (\<up>a))) = \<epsilon>" using a_nin_F by simp
    thus "F \<ominus> stake (Suc n)\<cdot>(sinftimes (\<up>a)) = \<epsilon>" by (subst sinftimes_unfold)
  qed
  hence "(F \<ominus> (\<Squnion>i. stake i\<cdot>(sinftimes (\<up>a)))) = \<epsilon>" by (simp add:contlub_cfun_arg)
  thus ?thesis by (simp add: reach_stream)
qed

lemma slen_sfilter_sdrop_ile: 
  "#(sfilter X\<cdot>(sdrop n\<cdot>p)) \<le> #(sfilter X\<cdot>p)"
apply (rule spec [where x = "n"])
apply (rule ind [of _ p], auto, simp add: len_stream_def)
apply (subst lnle_def, simp del: lnle_conv; fail)
apply (case_tac "x", auto)
apply (case_tac "a \<in> X", auto)
apply (erule_tac x="nat" in allE)
by (rule trans_lnle, auto)

lemma slen_sfilter_sdrop: 
  "\<forall>p X. #(sfilter X\<cdot>p) = \<infinity> \<longrightarrow> #(sfilter X\<cdot>(sdrop n\<cdot>p)) = \<infinity>" 
apply (induct_tac n, auto)
apply (rule_tac x=p in scases, auto)
by (case_tac "a\<in>X", auto)

text \<open>@{term sfilter} on @{term "stake n"} returns \<open>\<epsilon>\<close> if none of the first
  @{term n} elements is included in the filter\<close>
lemma sfilter_empty_snths_nin_lemma: 
  "\<forall>p. (\<forall>n. Fin n < #p \<longrightarrow> snth n p \<notin> X) \<longrightarrow> sfilter X\<cdot>(stake k\<cdot>p) = \<epsilon>"
apply (induct_tac k, auto)
apply (rule_tac x=p in scases, auto)
apply (case_tac "a\<in>X", auto)
apply (erule_tac x="0" in allE, simp)
apply (case_tac "n", auto)
apply (erule_tac x="s" in allE, auto)
by (erule_tac x="Suc n" in allE, auto)

text \<open>@{term sfilter} returns \<open>\<epsilon>\<close> if no element is included in the filter\<close>
lemma ex_snth_in_sfilter_nempty:
  "(\<forall>n. Fin n < #p \<longrightarrow> snth n p \<notin> X) \<Longrightarrow> sfilter X\<cdot>p = \<epsilon>"
apply (subgoal_tac "sfilter X\<cdot>p = (\<Squnion>k. sfilter X\<cdot>(stake k\<cdot>p))")
apply (erule ssubst)
apply (subst lub_eq_bottom_iff, simp)
apply (subst sfilter_empty_snths_nin_lemma, simp+)
apply (subst contlub_cfun_arg [THEN sym], simp)
by (simp add: reach_stream)

text \<open>@{term sfilter} returns the original streams if every element is included in the filter\<close>
lemma sfilter_snths_in_lemma: 
  "\<forall>p. (\<forall>n. Fin n < #p \<longrightarrow> snth n p \<in> X) \<longrightarrow> sfilter X\<cdot>(stake k\<cdot>p) = stake k\<cdot>p"
  apply (induct_tac k, auto)
  apply (rule_tac x=p in scases, auto)
  apply (case_tac "a\<in>X", auto)
   apply (case_tac "n", auto)
   apply (erule_tac x="s" in allE, auto)
   apply (erule_tac x="Suc n" in allE, auto)
  by (erule_tac x="0" in allE, simp)

lemma sfilter_snths_in_stream_lemma:assumes a1:" \<And> n . Fin n <#p  \<Longrightarrow> snth n p \<in> X" 
  shows  " p =  sfilter X\<cdot>(p)"
  apply (subst reach_stream [THEN sym], rule sym)
  apply (subst reach_stream [THEN sym],case_tac "#p=\<infinity>")
  apply (metis (no_types, opaque_lifting) approxl1 assms monofun_cfun_arg sfilter_snths_in_lemma slen_stake_fst_inf ub_stake)
  by (metis (no_types, opaque_lifting) assms fin2stake ninf2Fin sfilter_snths_in_lemma)

lemma slen_sfilterl1[simp]: "#(sfilter S\<cdot>x) \<le> #x"
apply (rule ind [of _ x], auto, simp add: len_stream_def)
apply (subst lnle_def, simp del: lnle_conv)
apply (case_tac "a \<in> S", auto)
by (rule trans_lnle, auto)

lemma sfilterl4:
  "#(sfilter X\<cdot>x) = \<infinity> \<Longrightarrow> #x = \<infinity>"
by (insert slen_sfilterl1 [of X x], auto)

lemma sfilterl2: 
  "\<forall>z. #(sfilter X\<cdot>s) \<le> #(sfilter X\<cdot>((stake n\<cdot>z) \<Zcat> s))"
apply (induct_tac n, auto)
apply (rule_tac x=z in scases, auto)
apply (case_tac "a\<in>X", auto)
apply (erule_tac x="sa" in allE)
by (drule trans_lnle, auto) 

lemma sfilterl3:
  "\<forall>s. #s = Fin k \<and> sfilter S\<cdot>s = \<epsilon> \<longrightarrow> 
       sfilter S\<cdot>(s\<Zcat>Z) = sfilter S\<cdot>Z" 
apply (induct_tac k, auto)
apply (rule_tac x=s in scases, auto)
by (case_tac "a \<in> S", auto)

text \<open>A stream can be split by @{term stake} and @{term sdrop} for filtering\<close>
lemma split_sfilter: "sfilter X\<cdot>x = sfilter X\<cdot>(stake n\<cdot>x) \<Zcat> sfilter X\<cdot>(sdrop n\<cdot>x)"
apply (rule_tac x=x in spec)
apply (induct_tac n, simp)
apply (rule allI)
apply (rule_tac x=x in scases, simp)
apply (erule_tac x="s" in allE, auto)
by (case_tac "a \<in> X", auto)

lemma int_sfilterl1[simp]: "sfilter S\<cdot>(sfilter M\<cdot>s) = sfilter (S \<inter> M)\<cdot>s"
apply (rule ind [of _ s], auto)
apply (case_tac "a \<in> S \<inter> M", auto)
by (case_tac "a \<in> M", auto)

lemma add_sfilter:
  "#x = Fin k \<Longrightarrow> sfilter t\<cdot>(x \<Zcat> y) = sfilter t\<cdot>x \<Zcat> sfilter t\<cdot>y"
apply (simp add: atomize_imp)
apply (rule_tac x="y" in spec)
apply (rule_tac x="x" in spec)
apply (induct_tac k, auto)
apply (rule_tac x="x" in scases, auto)
by (case_tac "a \<in> t", auto)

text \<open>After applying @{term "smap f"}, all elements are in the range of @{term f}\<close>
lemma sfilter_smap_nrange: 
  "m \<notin> range f \<Longrightarrow> sfilter {m}\<cdot>(smap f\<cdot>x) = \<epsilon>"
apply (rule ex_snth_in_sfilter_nempty [rule_format], simp)
apply (subst smap_snth_lemma, simp+)
apply (rule notI)
apply (drule sym)
by (drule_tac f="f" in range_eqI, simp)

lemma smap_filter: "inj f \<Longrightarrow> smap f\<cdot>(A \<ominus> s) = f ` A \<ominus> smap f\<cdot>s"
  apply(induction s; simp)
  apply(case_tac "a\<in>A"; simp)
  by (metis inj_image_mem_iff sfilter_nin)

lemma sfilter_lub_inf: assumes "\<And>n. \<exists>i. Fin n \<le> #(A \<ominus> (Y i))" and "chain Y"
  shows " #(A \<ominus> (\<Squnion>i. Y i)) = \<infinity>"
proof(rule ccontr)
  assume as: "#(A \<ominus> (\<Squnion>i::nat. Y i)) \<noteq> \<infinity>"
  obtain n where n_def:"#(A \<ominus> (\<Squnion>i. Y i)) = Fin n"
    using as lncases by auto
  obtain i where i_def:"Fin (Suc n) \<le>  #(A \<ominus> (Y i))"
    using assms(1) by blast
  have "#(A \<ominus> (Y i)) \<le> #(A \<ominus> (\<Squnion>i::nat. Y i))"
    using assms(2) cont_pref_eq1I is_ub_thelub mono_slen by blast
  thus False
    using dual_order.trans i_def n_def by fastforce
qed

lemma snth_filter: "Fin n < #s \<Longrightarrow> snth n s\<in>A \<Longrightarrow> sfilter A\<cdot>s \<noteq>\<bottom>"
  apply(induction n arbitrary: s)
  apply(rule_tac x="s" in scases)
  apply auto[2]
  apply(simp add: snth_rt)
  by (metis Fin_02bot Fin_Suc inject_Fin lnzero_def n_not_Suc_n not_le only_empty_has_length_0 sfilter_in sfilter_nin slen_rt_ile_eq slen_scons stream.sel_rews(2) strictI surj_scons)



lemma sfilter_conc2[simp]: assumes "#(sfilter A\<cdot>s2) = \<infinity>" and "#s1 < \<infinity>"
  shows "#(sfilter A\<cdot>(s1\<Zcat>s2)) = \<infinity>"
proof -
  have "(sfilter A\<cdot>(s1\<Zcat>s2)) = ((sfilter A\<cdot>s1) \<Zcat> (sfilter A\<cdot>s2))"
    using add_sfilter assms(2) lnless_def ninf2Fin by fastforce 
  thus ?thesis by (simp add: assms(1) slen_sconc_snd_inf) 
qed



lemma sfilter_conc_adm: "adm (\<lambda>b. #b<\<infinity> \<longrightarrow> #(A \<ominus> b) < #(A \<ominus> b \<Zcat> \<up>a))" (is "adm ?F")
by (metis (mono_tags, lifting) admI inf_chainl4 lnless_def lub_eqI lub_finch2)

lemma sfilter_conc: assumes "a\<in>A" 
  shows "#x<\<infinity> \<Longrightarrow> #(A \<ominus> x) < #(A \<ominus> (x \<Zcat> \<up>a))" (is "_ \<Longrightarrow> ?F x")
  proof(induction x)
    case adm
    then show ?case using sfilter_conc_adm by blast
  next
    case bottom
    then show ?case  using assms(1) lnless_def by auto
  next
    case (step a x)
    then show ?case
      apply(cases "a \<in> A",simp_all)
       apply (metis dual_order.antisym fold_inf inf_ub not_le_imp_less)+
      done
  qed

lemma sfilter_sinf [simp]: assumes "#s<\<infinity>" and "(A \<ominus> s) \<noteq> \<epsilon>"
  shows "A \<ominus> (s\<^sup>\<infinity>) = ((A \<ominus> s)\<^sup>\<infinity>)"
by (metis add_sfilter assms(1) assms(2) infI lnless_def rek2sinftimes sinftimes_unfold)

lemma sfilter_srt_sinf [simp]: assumes "#(A \<ominus> s) = \<infinity>" 
  shows  "#(A \<ominus> (srt\<cdot>s)) = \<infinity>"
  apply(cases s rule: scases,simp_all)
  using inf_scase[of s] assms slen_sfilterl1[of A s] 
  apply auto[2]
  apply(case_tac "aa \<in> A";simp)
  using inject_scons by auto

lemma sfilter_ntimes [simp]: "#({True} \<ominus> ((sntimes n (\<up>False))\<Zcat>ora2)) = #({True} \<ominus> ora2)"
  apply(induction n)
    by auto


lemma sbool_ntimes_f: assumes "({True} \<ominus> s) \<noteq>\<bottom>"
  obtains n where "(sntimes n (\<up>False)) \<Zcat> \<up>True \<sqsubseteq> s"
proof -
  have h1: "\<exists>i. snth i s = True"
    by (metis assms ex_snth_in_sfilter_nempty singletonD)
  obtain n where "Fin n < #s" and n_def: "n = Least (\<lambda>i. snth i s = True)"
  apply(subst LeastI) 
  apply (metis (no_types, lifting) assms ex_snth_in_sfilter_nempty linorder_not_less lnat_fin_le not_less_Least order_less_le_trans singletonD) 
    by blast                               
  have "snth n s = True"
    using LeastI h1 n_def by force
  have "\<And>i. i<n \<Longrightarrow> snth i s \<noteq> True" using not_less_Least n_def by fastforce
  hence"\<And>i. i<n \<Longrightarrow> snth i s = False" by auto      
  hence "(sntimes n (\<up>False)) \<sqsubseteq> s"
    using \<open>Fin n < #s\<close> snth2sntimes by blast
  obtain xs where xs_def: "s = (sntimes n (\<up>False)) \<Zcat> xs"
    using \<open>n\<star>\<up>False \<sqsubseteq> s\<close> approxl3 by auto
  hence "xs\<noteq>\<bottom>"
    by (metis assms sfilter_ntimes slen_empty_eq strict_sfilter)
  have "shd xs = snth n s"
    by (simp add: sdropl6 snth_def xs_def)
  hence "shd xs = True"
    using \<open>snth n s = True\<close> by auto   
  thus ?thesis
    by (metis (full_types)\<open>xs \<noteq> \<epsilon>\<close> lscons_conv minimal monofun_cfun_arg sup'_def surj_scons that xs_def)
qed


lemma sfilter_sValuesl3:
  "sValues\<cdot>s \<subseteq> X \<longrightarrow> sfilter X\<cdot>s = s"
apply (rule impI)
apply (rule stream.take_lemma)
apply (simp add: atomize_imp)
apply (rule_tac x="s" in spec)
apply (rule_tac x="X" in spec)
apply (induct_tac n, simp+)
apply (rule allI)+
apply (rule impI)
by (rule_tac x="xa" in scases, simp+)

lemma sfilter_sValuesl4 [simp]:
  "sfilter (sValues\<cdot>s)\<cdot>s = s"
by (rule sfilter_sValuesl3 [rule_format, of "s" "sValues\<cdot>s"], simp)

lemma sfilter_fin: assumes "#(A \<ominus> s) < \<infinity>" 
  shows "\<exists>n. (A \<ominus> (sdrop n\<cdot>s)) = \<bottom>"
  apply(rule ccontr)
  apply auto[1]
  by (metis len_stream_def assms fun_approxl2 lnat_well_h2 sconc_neq_h sconc_snd_empty split_sfilter)

lemma s_one_dom_inf: assumes "sValues\<cdot>s = {x}" and "#s = \<infinity>"
    shows "s = ((\<up>x)\<^sup>\<infinity>)"
  by (metis Fin_02bot Fin_Suc Suc_n_not_le_n assms(1) assms(2) bot_is_0 inject_Fin less_or_eq_imp_le sinftimes_unfold singleton_iff slen_scons slen_sinftimes snth2sValues snth_sinftimes snths_eq strict_icycle slen_zero)

lemma sfilter_bot_dom: "(A \<ominus> s) = \<bottom> \<Longrightarrow> sValues\<cdot>s \<subseteq> UNIV - A"
  apply(induction s rule: ind)
    apply auto[3]
  by (metis DiffD2 inject_scons rev_subsetD sfilter_in sfilter_nin strictI)


lemma add_sfilter2: assumes "#x < \<infinity>" 
  shows "sfilter A\<cdot>(x \<Zcat> y) = sfilter A\<cdot>x \<Zcat> sfilter A\<cdot>y"
  by (metis (no_types) add_sfilter assms lncases lnless_def)



lemma sfilter2dom:
  "sfilter {z}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> z \<in> sValues\<cdot>x"
apply (subgoal_tac "\<exists>k. snth k x = z \<and> Fin k < #x", erule exE)
apply (erule conjE)
apply (drule sym, simp)
apply (rule snth2sValues, simp; fail)
apply (rule ccontr, simp)
by (insert ex_snth_in_sfilter_nempty [of x "{z}"], auto)


lemma sbfilter_sbdom[simp]: "sValues\<cdot>(sfilter A\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply(rule ind [of _s]; simp)
  apply(case_tac "a\<in>A")
  by auto

text \<open>Further results concerning @{term sfilter}\<close>

lemma sfilter_sValues_eps[simp]: "sValues\<cdot>s \<inter> A = {} \<Longrightarrow> (A \<ominus> s) = \<epsilon>"
by (meson disjoint_iff_not_equal ex_snth_in_sfilter_nempty snth2sValues)


lemma sValues_sfilter_subset: assumes "u\<noteq>\<bottom>"
  shows "sValues\<cdot>(A\<ominus>s)\<subseteq>sValues\<cdot>(A \<ominus> (u && s))"

  apply(cases u;simp add: assms)
  apply(case_tac x)
  apply (simp add: lscons_conv)
  by (metis assms equalityE lscons_conv sValues_subset sfilter_in sfilter_nin)

lemma sValues_sfilter2: assumes  "x\<in>A"
shows "x\<in>sValues\<cdot>s \<Longrightarrow> x\<in>(sValues\<cdot>(A \<ominus> s))"
apply(induction s rule: ind)
apply(rule admI)
apply(rule impI)
apply (metis (mono_tags, lifting) UN_iff ch2ch_Rep_cfunR contlub_cfun_arg sValues_lub)
apply simp+
by(case_tac "a\<in> A",auto simp add: assms)



lemma sfilter_union_len:
  assumes "A \<inter> B = {}"
  shows "#(sfilter (A\<union>B)\<cdot>s) = #(sfilter A\<cdot>s) + #(sfilter B\<cdot>s)"
  apply (induction s)
  apply (subst ladd_insert[symmetric])
  apply (simp add: len_stream_def; fail)
  apply (simp; fail)
  apply (case_tac "a \<in> A"; simp)
  apply (metis add.assoc assms disjoint_iff_not_equal lnat_suc_plus sfilter_nin)
  by (metis (no_types, opaque_lifting) Un_iff ab_semigroup_add_class.add_ac(1)
      lnat_plus_suc sfilter_in sfilter_nin slen_scons)

lemma sfilter_subset_len:
  assumes "A \<subseteq> B"
  shows "#(sfilter A\<cdot>s) \<le> #(sfilter B\<cdot>s)"
  apply (induction s)
  apply (subst lnle_def)
  apply (rule adm_below)
  apply (simp add: len_stream_def; fail)
  apply (simp add: len_stream_def; fail)
  apply (simp; fail)
  apply (case_tac "a \<in> A")
  apply (metis (no_types, opaque_lifting) assms lnsuc_lnle_emb sfilter_in
      slen_scons subsetD)
  by (metis (no_types, lifting) dual_order.trans less_lnsuc sfilter_in
      sfilter_nin slen_scons)

lemma sValues_sfilter[simp]: "sValues\<cdot>(A\<ominus>s) = sValues\<cdot>s \<inter> A"
  apply (induction s, simp_all)
  apply (rule adm_eq)
  apply (intro cont2cont)
  apply (rule cont_compose [where f="\<lambda>x. sValues\<cdot>x"])
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: less_set_def le_infI1; fail)
  apply (simp add: less_set_def lub_eq_Union; fail)
  apply (intro cont2cont; fail)
  by (case_tac "a \<in> A"; simp)

lemma sfilter_svalues_fin_len:
  assumes "finite (sValues\<cdot>s)"
    and "\<And>m. m \<in> sValues\<cdot>s \<Longrightarrow> #(sfilter {m}\<cdot>s) < \<infinity>"
  shows "#s < \<infinity>"
  apply (subst sfilter_sValuesl4[symmetric])
  apply (insert assms)
  apply (rule_tac F="sValues\<cdot>s" in finite_induct)
  apply (simp; fail)+
  apply (subst insert_is_Un)
  by (metis (no_types, lifting) inf_bot_left insert_disjoint(2)
      only_empty_has_length_0 plus_lnat0_r sconc_slen sconc_slen2
      sfilter2dom sfilter_union_len)

lemma sfilter_svalues_inf_len_ex:
  assumes "#s = \<infinity>"
    and "finite (sValues\<cdot>s)"
  shows "\<exists>m \<in> sValues\<cdot>s. #({m} \<ominus> s) = \<infinity>"
  by (metis assms(1) assms(2) less_irrefl order.not_eq_order_implies_strict
      sfilter_svalues_fin_len slen_sfilterl1)

lemma sfilter_image:"inj f \<Longrightarrow> (sfilter S\<cdot>i = \<epsilon>) \<longleftrightarrow> (sfilter (f ` S)\<cdot>(smap f\<cdot>i) = \<epsilon>)"
  apply auto[1]
  apply (induction i,simp_all)
  apply(case_tac "a\<in>S";simp)
  apply(case_tac "f a \<in> (f` S)";simp)
  apply(simp add: image_iff,auto)
  apply (metis injD)
  apply(induction i,simp_all)
  apply(case_tac "f a\<in> (f` S)";simp)
  by(case_tac "a\<in> S";simp)

lemma sfilter_smap:"(sfilter S\<cdot>i = \<epsilon>) \<longleftrightarrow> (smap f\<cdot>((sfilter S\<cdot>i)) = \<epsilon>)"
  apply auto[1]
  apply(induction i,simp_all)
  by(case_tac "a\<in>S";simp)

lemma sfilter_redimage:"inj f \<Longrightarrow> f ` {m. fst (f m) = c} \<ominus> smap f\<cdot>(s) = {m. fst ( m) = c} \<ominus> smap f\<cdot>(s)"
  apply(induction s,simp_all)
  apply(case_tac "f a \<in> {m. fst ( m) = c}";simp)
  apply(case_tac "f a \<in> f`{m. fst (f m) = c}";simp)
  by (meson inj_image_mem_iff mem_Collect_eq)

lemma sfilter2filter:"sfilter {m. P m}\<cdot>(<ls>) = <(filter P ls)>"
  by(induction ls,simp_all)

lemma sValues2snth2: "z \<in> sValues\<cdot>s \<Longrightarrow> \<exists>n. snth n s = z \<and> Fin n < #s"
by (auto simp add: sValues_def2)

lemma snth_sfilter_ex: assumes "Fin n < #(sfilter A\<cdot>s)" and  "snth n (sfilter A\<cdot>s) = msg"
  shows "\<exists>n. Fin n < #s \<and> snth n s = msg"
proof (rule ccontr)
  assume h: "\<not>(\<exists>n. Fin n < #s \<and> snth n s = msg)"
  hence h': "\<forall>n. Fin n < #s \<Longrightarrow> snth n s \<noteq> msg" by simp
  then obtain n where n: "snth n (sfilter A\<cdot>s) = msg \<and> Fin n < #(sfilter A\<cdot>s)"
    using assms by blast
  hence "snth n (sfilter A\<cdot>s) \<in> sValues\<cdot>(sfilter A\<cdot>s)"
    using snth2sValues by blast
  hence "snth n (sfilter A\<cdot>s) \<in> sValues\<cdot>s"
    by simp
  hence "\<exists>n. Fin n < #s \<and> snth n s = msg"
    using sValues2snth2 n by blast
  thus False 
    using  h' h by force
qed

lemma snth_sfilter_ex2: assumes "Fin n < #s" and "snth n s = msg" and "msg \<in> A"
  shows "\<exists>n. Fin n < #(sfilter A\<cdot>s) \<and> snth n (sfilter A\<cdot>s) = msg"
proof (rule ccontr)
  assume h1: "\<not>(\<exists>n. Fin n < #(sfilter A\<cdot>s) \<and> snth n (sfilter A\<cdot>s) = msg)"
  then obtain n where h2: "snth n (sfilter A\<cdot>s) = msg \<and> Fin n < #(sfilter A\<cdot>s) \<and> msg \<in> A"
    using assms by (meson sValues2snth2 sValues_sfilter2 snth2sValues)
  hence "\<exists>n. Fin n < #(sfilter A\<cdot>s) \<and> snth n (sfilter A\<cdot>s) = msg"
    using h2 by blast
  thus False 
    using h1 by blast
qed

lemma sfilter_id[simp]: "sfilter UNIV = ID"
  by(rule cfun_eqI, rename_tac s, induct_tac s; simp)

lemma sfitler_univ_len:
  assumes" S1 \<union> S2 = UNIV"
  and"S1 \<inter> S2 = {}"
  shows "#(sfilter S1\<cdot>b) + #(sfilter S2\<cdot>b) = #b"
  by(subst sfilter_union_len[symmetric],simp_all add: assms)

lemma sfilter_bool_len:"#(sfilter {True}\<cdot>b) + #(sfilter {False}\<cdot>b) = #b"
  by(simp_all add: sfitler_univ_len UNIV_bool)

lemma slen_infinite_true_or_false:
  "#b = \<infinity> \<longrightarrow> #(sfilter {True}\<cdot>b) = \<infinity> \<or> #(sfilter {False}\<cdot>b) = \<infinity>"
  apply(subst sfilter_bool_len[symmetric])
  apply auto 
  by (metis inf_great linorder_less_linear plus_lnatInf_r plus_unique_l)

lemma sfilter_smap_len:
  assumes "\<forall>a :: 'a::{countable}. ((f a) \<in> (B :: 'b::{countable} set) \<longleftrightarrow> a \<in> A)"
  shows "#(A \<ominus> s) = #(B \<ominus> (smap f)\<cdot>s)"
  apply(induct s, simp_all)
   apply(rule adm_eq)
    apply(simp add: cont_compose_mix)
   apply(rule cont_compose_mix)+
   apply(simp)
  by(case_tac "a \<in> A", simp_all add: assms)

lemmas sfilter_smap_len_symmetric = sfilter_smap_len[symmetric]

lemma
  szip_sfilter_infty_len:
  assumes "#(M \<ominus> ora) = \<infinity>"
    and "#s = \<infinity>"
  shows "#(szip\<cdot>ora\<cdot>s) = \<infinity>"
  apply(insert assms, simp)
  using sfilterl4 by blast


lemma sfilter_tpl_sprojfst: "sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> tpls) = M \<ominus> (sprojfst\<cdot>tpls)"
  apply(induction tpls, simp_all)
  by (metis (no_types, lifting) Product_Type.old.prod.exhaust case_prod_conv mem_Collect_eq sfilter_in sfilter_nin sprojfst_scons)

lemma sfilter_szip_sprojfst: "#s \<ge> #ora \<Longrightarrow> sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> szip\<cdot>ora\<cdot>s) = M \<ominus> ora"
proof -
  assume assms: "#s \<ge> #ora"
  have belowness: "sprojfst\<cdot>(szip\<cdot>ora\<cdot>s) \<sqsubseteq> ora"
    by(rule sprojfst_szip_below[of ora s])
  then have equallity: "sprojfst\<cdot>(szip\<cdot>ora\<cdot>s) = ora"
    by (simp add: assms eq_slen_eq_and_less slen_sprojfst)
  
  have "sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> (szip\<cdot>ora\<cdot>s)) = M \<ominus> (sprojfst\<cdot>(szip\<cdot>ora\<cdot>s))"
    by (rule sfilter_tpl_sprojfst)

  thus ?thesis
    using equallity by argo
qed

lemma sfilter_tpl_sprojsnd: "sprojsnd\<cdot>({(x, m) . m \<in> M} \<ominus> tpls) = M \<ominus> (sprojsnd\<cdot>tpls)"
  apply(induction tpls, simp_all)
  by (metis (no_types, lifting) Product_Type.old.prod.exhaust case_prod_conv mem_Collect_eq sfilter_in sfilter_nin sprojsnd_scons)

lemma sfilter_szip_sprojsnd: "#s \<ge> #ora \<Longrightarrow> sprojsnd\<cdot>({(x, m) . m \<in> M} \<ominus> szip\<cdot>s\<cdot>ora) = M \<ominus> ora"
proof -
  assume assms: "#s \<ge> #ora"
  have belowness: "sprojsnd\<cdot>(szip\<cdot>s\<cdot>ora) \<sqsubseteq> ora"
    by(rule sprojsnd_szip_below[of s ora])
  then have equallity: "sprojsnd\<cdot>(szip\<cdot>s\<cdot>ora) = ora"
    by (simp add: assms eq_slen_eq_and_less slen_sprojsnd)
  
  have "sprojsnd\<cdot>({(x, m) . m \<in> M} \<ominus> (szip\<cdot>s\<cdot>ora)) = M \<ominus> (sprojsnd\<cdot>(szip\<cdot>s\<cdot>ora))"
    by (rule sfilter_tpl_sprojsnd)

  thus ?thesis
    using equallity by argo
qed


lemma svalues_sfilter_in: "a \<in> sValues\<cdot>(A \<ominus> s) \<longrightarrow> a \<in> sValues\<cdot>s"
  by simp

lemma sfilter_stake_exists:
  shows "\<exists>k. sfilter X\<cdot>(stake n\<cdot>s) = stake k\<cdot>(sfilter X\<cdot>s)"
proof (cases "Fin n < #s")
  case True
  then show ?thesis 
  proof (induction n arbitrary: s)
  case 0
  then show ?case
    by (metis Rep_cfun_strict1 stream.take_0 strict_sfilter)
  next
  case (Suc n)
  from Suc.IH[of "srt\<cdot>s"] obtain k
    where IH: " Fin n < #s \<Longrightarrow> sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s)) = stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
    by (metis Suc.prems empty_is_shortest lnat_fin8 srt_decrements_length)
    show ?case
  proof (cases "shd s \<in> X")
    case True
    have "sfilter X\<cdot>(stake (Suc n)\<cdot>s)
        = sfilter X\<cdot>(\<up>(shd s) \<Zcat> stake n\<cdot>(srt\<cdot>s))"
      using stake_shd_srt 
      by (metis Suc.prems convert_inductive_asm) 
      also from True have "... = \<up>(shd s) \<Zcat> sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s))"
      by simp
    also from IH have "... = \<up>(shd s) \<Zcat> stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
      by (metis Suc.prems convert_inductive_asm)
      also have "sfilter X\<cdot>s = \<up>(shd s) \<Zcat> sfilter X\<cdot>(srt\<cdot>s)"
      using True 
      by (metis Suc.prems sfilter_in stake_shd_srt stream.take_strict supconc_neps2 surj_scons)
      hence "\<up>(shd s) \<Zcat> stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))
         = stake (Suc k)\<cdot>(sfilter X\<cdot>s)"
      by simp
    finally show ?thesis
      by (rule exI[of _ "Suc k"])
  next
    case False
    have "sfilter X\<cdot>(stake (Suc n)\<cdot>s)
        = sfilter X\<cdot>(\<up>(shd s) \<Zcat> stake n\<cdot>(srt\<cdot>s))"
      using stake_shd_srt 
      by (metis Suc.prems convert_inductive_asm) 
    also from False have "... = sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s))"
      by simp
    also from IH have "... = stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
      by (metis Suc.prems convert_inductive_asm)
    also from False have "sfilter X\<cdot>s = sfilter X\<cdot>(srt\<cdot>s)"
      by (metis Suc.prems sfilter_nin stake_shd_srt stream.take_strict supconc_neps2 surj_scons)
    hence "stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s)) = stake k\<cdot>(sfilter X\<cdot>s)"
      by simp
    finally show ?thesis
      by (rule exI[of _ k])
  qed
qed
next
  case False
  have "sfilter X\<cdot>(stake n\<cdot>s) = sfilter X\<cdot>s" 
    using False
    by (metis fin2stake_lemma fin_le_inf less2nat linorder_le_less_linear ninf2Fin)  
  then show ?thesis 
    by (metis False fin2stake fin_le_inf ninf2Fin sfilterl4)
qed


lemma sboolfilter_cont: "cont (\<lambda> i ora. sprojfst\<cdot>({d. snd d} \<ominus> (szip\<cdot>i\<cdot>ora)))"
  by (intro cont2cont)                                                

lemma strict_sboolfilter_fst[simp]: "sboolfilter\<cdot>\<epsilon>\<cdot>s = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma strict_sboolfilter_snd[simp]: "sboolfilter\<cdot>s\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma sboolfilter_singleton_true[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>True) = \<up>a"
  by (simp add: sboolfilter_def)
lemma sboolfilter_singleton_false[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>False) = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma sboolfilter_singelton_msg_true[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>True \<Zcat> bs) =  \<up>a"
  by (simp_all add: sboolfilter_def)

lemma sboolfilter_singelton_msg_false[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>False \<Zcat> bs) = \<epsilon>"
  by (simp_all add: sboolfilter_def)

lemma sboolfilter_sconc_true[simp]: "sboolfilter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>True \<Zcat> bs) = \<up>a \<Zcat> sboolfilter\<cdot>as\<cdot>bs"
  by (simp add: sboolfilter_def)

lemma sboolfilter_sconc_false[simp]: "sboolfilter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) = sboolfilter\<cdot>as\<cdot>bs"
  by (simp add: sboolfilter_def)

lemma slen_suc_neq: " #t < \<infinity> \<Longrightarrow> #t = #s \<Longrightarrow> lnsuc\<cdot>(#t) \<noteq> #s"
  by (simp add: order_less_imp_not_eq2)

lemma sboolfilter_len_le:
  "#(sboolfilter\<cdot>x\<cdot>ora) \<le> #x"
  apply (simp add: sboolfilter_def) 
  by (metis (no_types, lifting) slen_sfilterl1 min.bounded_iff slen_sprojfst szip_len)

lemma sboolfilter_len_eq_imp_eq: "#x = Fin k \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
proof -
  assume len_eq: "#x = #(sboolfilter\<cdot>x\<cdot>ora)" and fin: "#x = Fin k"
  show "x = sboolfilter\<cdot>x\<cdot>ora"
    using len_eq apply (induction x arbitrary: ora rule: finind2)
    using fin apply auto
    apply (case_tac ora; simp)
    apply (rename_tac s a ora b bs)
    apply (case_tac b)
    apply simp_all
    apply metis
    by (metis sboolfilter_len_le lnle_and_gt_inf(1) refl_lnle slen_suc_neq)+
qed

lemma sboolfilter_len_eq_imp_eq2: "#x \<noteq> \<infinity> \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
  using ninf2Fin sboolfilter_len_eq_imp_eq by blast

lemma sboolfilter_len_eq_imp_eq3: "#x < \<infinity> \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
  by (meson lnat_well_h2 sboolfilter_len_eq_imp_eq)

lemma sboolfilter_refold: "(\<up>a \<Zcat> sboolfilter\<cdot>s\<cdot>ora)
      = (sboolfilter\<cdot>(\<up>a \<Zcat>s)\<cdot>(\<up>True \<Zcat>ora))"
  by simp

lemma sboolfilter_liveness_helper: "#i = \<infinity> \<longrightarrow> sprojsnd\<cdot>({d. snd d} \<ominus> szip\<cdot>i\<cdot>ora) = {True} \<ominus> ora"
proof (induction ora arbitrary:i)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a ora)
  then show ?case 
    apply (cases i)
     apply simp
    apply (cases a)
    by simp_all
qed

lemma sboolfilter_live [simp]:
  assumes "#y=\<infinity>"
  shows "#(sboolfilter\<cdot>y\<cdot>ora) = #({True} \<ominus> ora)"
proof -
 have a: "#(sboolfilter\<cdot>y\<cdot>ora)
            = #(sprojsnd\<cdot>({d. snd d} \<ominus> szip\<cdot>y\<cdot>ora))"
   by (simp add: sboolfilter_def slen_sprojs_eq)
  then have b: "... = #({True} \<ominus> ora)"
        using assms sboolfilter_liveness_helper by fastforce
  from a b
  show "#(sboolfilter\<cdot>y\<cdot>ora) = #({True} \<ominus> ora)" by simp
qed

lemma sboolfilter_inf_true: "sboolfilter\<cdot>y\<cdot>((\<up>True)\<^sup>\<infinity>) = y"
  apply (induction y)
  apply auto
  by (metis sboolfilter_sconc_true sinftimes_unfold)

lemma bstream_cases [case_names bottom true false]:
  assumes bottom: "x = \<bottom> \<Longrightarrow> P \<bottom>"
      and true: "\<And>as. x=(\<up>True \<Zcat> as) \<Longrightarrow> P x"
      and false: "\<And>as. x=(\<up>False \<Zcat> as) \<Longrightarrow> P x"
  shows "P x"
  using assms apply (cases x; simp)
  by (case_tac a; simp)

lemma bstream_p_t_unfold: "\<exists>ora1. P (\<up>True\<Zcat>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto

lemma bstream_p_f_unfold: "\<exists>ora1. P (\<up>False \<Zcat> ora1) \<Longrightarrow> \<exists>ora2. P ora2"
by auto   



lemma srcdups_slen_filter_mono: "#(srcdups\<cdot>(sfilter A\<cdot>y)) \<le> #(srcdups\<cdot>(sfilter A\<cdot>(\<up>x) \<Zcat> sfilter A\<cdot>y))"
  by (metis dual_order.refl sconc_fst_empty sfilter_in_sup sfilter_notin_sup srcdups_slen_mono)

lemma adm_slen_srcdups_sboolfilter:
 "adm (\<lambda>a. #(srcdups\<cdot>(sboolfilter\<cdot>a\<cdot>ora)) \<le> #(srcdups\<cdot>a))" 
  apply (subst lnle_def)
  apply (rule adm_below) 
   apply (rule cont_compose [where f="\<lambda>x. srcdups\<cdot>(sboolfilter\<cdot>x\<cdot>ora)"])  
    apply simp_all
    using cont_compose_mix len_stream_cont by blast



lemma adm_slen_srcdups_sfilter:
 "adm (\<lambda>a. #(srcdups\<cdot>(A \<ominus> a)) \<le> #(srcdups\<cdot>a))" 
proof (rule admI)
  fix Y :: "nat \<Rightarrow>  'a stream"
  assume ch: "chain Y"
  assume hyp:
    "\<forall>i. #(srcdups\<cdot>(A \<ominus> (Y i))) \<le> #(srcdups\<cdot>(Y i))"

  let ?L = "\<lambda> a.  #(srcdups\<cdot>(A \<ominus> a))"
  let ?R = "\<lambda> a.  #(srcdups\<cdot>a)"

  have contL: "cont ?L" 
    using cont_compose_mix len_stream_cont by blast
  have contR: "cont ?R" 
    using cont_compose_mix len_stream_cont by blast

  from ch have L_lub: "?L (\<Squnion>i. Y i) = (\<Squnion>i. ?L (Y i))"
    using contlub_cfun_arg cont2contlubE contL by blast
  from ch have R_lub: "?R (\<Squnion>i. Y i) = (\<Squnion>i. ?R (Y i))"
    using contlub_cfun_arg cont2contlubE contR by blast

  have pw: "\<And>i. ?L(Y i) \<sqsubseteq> ?R(Y i)" using hyp by simp
  have "(\<Squnion>i. ?L(Y i)) \<le> (\<Squnion>i. ?R(Y i))"
    using ch contR ch2ch_cont contL pw lub_mono lnle_conv by blast

  thus " #(srcdups\<cdot>(A \<ominus> (\<Squnion>i. Y i))) \<le>  #(srcdups\<cdot>(\<Squnion>i. Y i))"
    by (simp add: L_lub R_lub)
qed

lemma slen_srcdups_filter_mono:
  "# (srcdups\<cdot>(A \<ominus> s)) \<le> # (srcdups\<cdot>s)"
proof (induction s)
  case adm then show ?case  by (simp add: adm_slen_srcdups_sfilter)
next
  case bottom then show ?case by simp
next
  case (step a s)
  then show ?case
    apply (cases "a \<in> A") 
     apply simp_all
    prefer 2 subgoal 
      using order.trans srcdups_slen_mono by blast
    apply (cases s, simp_all)
    apply (case_tac "a=aa", simp_all)
    apply (case_tac "aa\<in> A", simp_all)
    using srcdups_slen_leq lnsuc_lnle_emb trans_lnle by blast
qed

lemma slen_srcdups_sboolfilter_leq: 
  "#(srcdups\<cdot>(sboolfilter\<cdot>s\<cdot>ora)) \<le> #(srcdups\<cdot>(s))"
proof (induction s arbitrary:ora)
  case adm then show ?case 
    apply (rule adm_all) 
    using adm_slen_srcdups_sboolfilter by blast
next
  case bottom then show ?case by simp
next
  case (step a s)
  then show ?case
    apply (cases ora, simp_all) 
    apply (rename_tac x y)
     apply (case_tac x, simp_all)
    prefer 2
      using order.trans srcdups_slen_mono apply blast
    apply (cases s, simp_all)
    apply (rename_tac b t)
    apply (case_tac "a\<noteq>b", simp_all)
      using srcdups_slen_leq lnsuc_lnle_emb trans_lnle apply blast
      apply (case_tac y, simp)
      using neq02Suclnle slen_empty_eq srcdups_nbot supconc_neps2 apply blast
        apply (case_tac aa, simp_all)  
      apply (subst sboolfilter_refold)  
        apply blast
       apply (subst sboolfilter_refold)  
      by blast 
  qed

lemma "#(srcdups\<cdot>(sboolfilter\<cdot>(\<up>(1::nat))\<cdot>(\<up>False))) <  #(srcdups\<cdot>(\<up>1))"
  by simp
lemma "#(srcdups\<cdot>(sboolfilter\<cdot>(\<up>(1::nat))\<cdot>(\<up>True))) =  #(srcdups\<cdot>(\<up>1))"
  by simp

lemma sboolfilter_sprojsnd_distr:
  "sprojsnd\<cdot>(sboolfilter\<cdot>xs\<cdot>bs) = sboolfilter\<cdot>(sprojsnd\<cdot>xs)\<cdot>bs"
  apply (induct xs arbitrary: bs, simp_all)
  apply (case_tac a)
  apply (case_tac bs, simp_all)
  by (case_tac ab, simp_all)

lemma slen_srcdups_sprojsnd_sboolfilter_mono: 
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>s\<cdot>ora))) \<le>  #(srcdups\<cdot>(sprojsnd\<cdot>s))"
  apply (simp add: sboolfilter_sprojsnd_distr) 
  using slen_srcdups_sboolfilter_leq by blast



lemma sdropwhile_shd_neq: "y \<noteq> \<epsilon> \<Longrightarrow> shd y \<noteq> a \<Longrightarrow> y = sdropwhile (\<lambda>x. x = a)\<cdot>y"
  by (metis (full_types) sdropwhile_f shd1 streamcases)

lemma sdropwhile_shd_neq2:
  assumes "shd y \<noteq> a"
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>y = y"
  using assms 
  by (metis sdropwhile_shd_neq strict_sdropwhile)

lemma smap_sboolfilter_commutative: 
  "smap f\<cdot>(sboolfilter\<cdot>s\<cdot>ora) = sboolfilter\<cdot>(smap f\<cdot>s)\<cdot>ora"
  apply(induct ora arbitrary: s, simp_all)
  apply(case_tac s, simp_all)
  by(case_tac a, simp_all)

lemma sdrop_sboolfilter: "sdrop n\<cdot>s = sboolfilter\<cdot>s\<cdot>((sntimes n (\<up>False)) \<Zcat> ((\<up>True)\<^sup>\<infinity>))" 
  apply (induction n arbitrary: s; simp)
  apply (simp add: sboolfilter_inf_true)
  by (metis sboolfilter_sconc_false sdrop_forw_rt strict_sboolfilter_fst strict_sdrop surj_scons)

lemma sdrophwile_sboolfilter: "\<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sboolfilter\<cdot>s\<cdot>ora"
  by (metis sdrop_sboolfilter sdropwhile_neq_eps_sdrop strict_sboolfilter_snd)

lemma sbool_apply_sconc_f_t[simp]: "sbool_apply\<cdot>(\<up>True \<Zcat> xs)\<cdot>(\<up>y \<Zcat> ys) = \<up>y \<Zcat> (sbool_apply\<cdot>xs\<cdot>ys)"
  by (metis lscons_conv sbool_apply.simps(3) undiscr_Discr)

lemma sbool_apply_sconc_f_any[simp]: "sbool_apply\<cdot>(\<up>False \<Zcat> xs)\<cdot>(\<up>y \<Zcat> ys) = \<up>False \<Zcat> (sbool_apply\<cdot>xs\<cdot>(\<up>y \<Zcat> ys))"
  by (metis (no_types, lifting) lscons_conv sbool_apply.simps(3) undiscr_Discr)

lemma sboolfilter_sboolfilter: "sboolfilter\<cdot>(sboolfilter\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sboolfilter\<cdot>msg\<cdot>(sbool_apply\<cdot>ora1\<cdot>ora2 )"
  apply (induction msg arbitrary: ora1 ora2)
    apply (rule adm_all)+
    apply (rule adm_eq; simp)
    apply simp
  apply (case_tac ora1 rule: bstream_cases; simp)
  apply (case_tac ora2 rule: bstream_cases; simp)
  by (case_tac ora2 rule: bstream_cases; simp)

lemma sboolfilter_sconc: "\<exists>ora2. sboolfilter\<cdot>(as \<Zcat> bs)\<cdot>ora = sboolfilter\<cdot>as\<cdot>ora \<Zcat> sboolfilter\<cdot>bs\<cdot>ora2"
proof (cases "#as = \<infinity>")
  case True
  then show ?thesis   
    apply (simp add: sboolfilter_def)
    by (metis  sconc_snd_empty strict_sfilter strict_sprojfst strict_szip_snd)
next
  case False
  obtain k where "#as = Fin k" 
    using False infI by auto
  then show ?thesis 
    apply (cases "#ora \<le> #as")
    apply (simp_all add: sboolfilter_def)
    apply (metis szip_sconc_len_leq sconc_snd_empty strict_sfilter strict_sprojfst strict_szip_snd)
    apply (simp add: szip_sconc_len_gr add_sfilter sprojfst_sconc) 
    by blast
qed

lemma sdropwhile_filter_stakewhile_empty: "sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>"
  apply (induction s arbitrary:ora)
    apply (rule adm_all)
    apply (rule adm_eq; simp)
    apply simp
  apply (case_tac "a=aa"; simp)
  by (case_tac ora rule: bstream_cases; simp)

lemma srcdups_neq2:
  assumes "a \<noteq> shd s" 
  shows "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s" 
  using assms 
  by (metis sconc_snd_empty srcdups_neq srcdups_sup strict_srcdups surj_scons)

lemma smap_inj_preserves_srcdups_fixed:
  assumes injf: "inj f"
  shows "srcdups\<cdot>(smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>s)"
proof (induction s)
  case adm
  then show "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
    using StreamWhile.srcdups_smap_adm by auto
next
  case bottom
  then show ?case by auto
next
  case (step a s)
  have smap_cons: "smap f\<cdot>(\<up>a \<Zcat> s) = \<up>(f a) \<Zcat> smap f\<cdot>s"
    by simp

  show ?case
  proof (cases "s = \<epsilon>")
    case True
    then show ?thesis
      by (simp add: smap_cons)
  next
    case False
    have s_cons: "s = \<up>(shd s) \<Zcat> (srt\<cdot>s)"
      using False
      by (simp add: surj_scons)

    show ?thesis
    proof (cases "a = shd s")
      case Eq: True
      have in_drop: "srcdups\<cdot>(\<up>a \<Zcat> s) = srcdups\<cdot>s"
        using False Eq
        by (metis s_cons srcdups_eq)
      have out_drop: "srcdups\<cdot>(\<up>(f a) \<Zcat> smap f\<cdot>s) = srcdups\<cdot>(smap f\<cdot>s)"
        using False Eq
        by (metis in_drop smap_cons srcdups2srcdups srcdups_smap_com step)
      from step.IH show ?thesis
        by (simp add: smap_cons in_drop out_drop)
    next
      case Neq: False
      have in_keep: "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s"
      proof -
        have "sdropwhile (\<lambda>z. z = a)\<cdot>s = s"
          using False Neq
          by (simp add: sdropwhile_shd_neq2)
        then show ?thesis
          using False
          by (simp add: Neq srcdups_neq2)
      qed
      have fmap_neq: "f (shd s) \<noteq> f a"
        using injf Neq by (metis injD)

      have out_keep: "srcdups\<cdot>(\<up>(f a) \<Zcat> smap f\<cdot>s) = \<up>(f a) \<Zcat> srcdups\<cdot>(smap f\<cdot>s)"
      proof -
        have "sdropwhile (\<lambda>z. z = f a)\<cdot>(smap f\<cdot>s) = smap f\<cdot>s"
          using False fmap_neq
          by (simp add: smap_hd_rst)
        then show ?thesis
          by (simp add: srcdups_step)
      qed
      from step.IH show ?thesis
        by (simp add: smap_cons in_keep out_keep)
    qed
  qed
qed

lemma sdropwhile_sboolfilter_ex:
  shows "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>y\<cdot>ora) = sboolfilter\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>y)\<cdot>ora2"
proof -
  let ?P = "\<lambda>x. x = a"
  have decomp: "y = stakewhile ?P\<cdot>y \<Zcat> sdropwhile ?P\<cdot>y"
    by (simp add: stakewhileDropwhile)
  obtain ora2 where filt_decomp:
    "sboolfilter\<cdot>(stakewhile ?P\<cdot>y \<Zcat> sdropwhile ?P\<cdot>y)\<cdot>ora
     = sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora  \<Zcat> sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2"
    using sboolfilter_sconc by blast
  hence filt_y:
    "sboolfilter\<cdot>y\<cdot>ora  = sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora  \<Zcat> sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2"
    using decomp by simp
  have drop_take_empty:
    "sdropwhile ?P\<cdot>(sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora) = \<epsilon>"
    using sdropwhile_filter_stakewhile_empty[of a y ora] by simp
  have lhs:
    "sdropwhile ?P\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
     = sdropwhile ?P\<cdot>(sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2)"
    using filt_y drop_take_empty 
    by (metis dropwhile_sconc_empty lncases notinfI3 sboolfilter_len_le sconc_snd_empty sdropwhile_takewhile_neq_eps_neq_inf
        strict_sboolfilter_fst strict_sdropwhile)
  obtain ora3 where lhs2: "sdropwhile ?P\<cdot>(sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2) = sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>(sbool_apply\<cdot>ora2\<cdot>ora3)"
    using sdrophwile_sboolfilter by (metis sboolfilter_sboolfilter)
  then show ?thesis
    by (metis lhs2 lhs)
qed

lemma srcdups_sboolfilter_shd: "(sboolfilter\<cdot>as\<cdot>bs) \<noteq> \<epsilon> \<Longrightarrow> shd (sboolfilter\<cdot>as\<cdot>bs) = a 
  \<Longrightarrow> srcdups\<cdot>(sboolfilter\<cdot>as\<cdot>bs) = \<up>a \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>as\<cdot>bs))"
  by (metis srcdups_eq srcdups_step surj_scons)

lemma srcdups_sboolfilter_ex:
  assumes len: "#(srcdups\<cdot>y) = Fin n"  shows "\<exists>ora2. srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora) = sboolfilter\<cdot>(srcdups\<cdot>y)\<cdot>ora2"
  using len
proof (induction n arbitrary: y ora)
  case 0
  then show ?case 
    by (metis Fin_0 slen_empty_eq srcdups_nbot strict_sboolfilter_fst)
next
  case (Suc n)
  obtain a ys where
    y_ne: "y \<noteq> \<epsilon>" and  a_def: "a = shd y" and
    srcdups_y: "srcdups\<cdot>y = \<up>a \<Zcat> srcdups\<cdot>ys" and
    ys_def: "ys = sdropwhile (\<lambda>x. x = a)\<cdot>y" and
    len_ys: "#(srcdups\<cdot>ys) = Fin n"
    by (metis (no_types, lifting) ext Fin_0 Suc.prems lnat_fin4 old.nat.distinct(1) slen_scons slen_zero srcdups_eq srcdups_step strict_srcdups
        surj_scons)
  obtain ora1 where dropwhile_filter_ys:
   "sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>y\<cdot>ora)  = sboolfilter\<cdot>ys\<cdot>ora1"
    using ys_def sdropwhile_sboolfilter_ex by blast
  obtain ora2 where IH_tail:
    "srcdups\<cdot>(sboolfilter\<cdot>ys\<cdot>ora1)  = sboolfilter\<cdot>(srcdups\<cdot>ys)\<cdot>ora2"
    using Suc.IH len_ys by blast
  show ?case
  proof (cases "sboolfilter\<cdot>y\<cdot>ora = \<epsilon>")
    case True
    then show ?thesis 
      by (metis strict_sboolfilter_snd strict_srcdups)
  next
    case False
    define a' where "a' = shd (sboolfilter\<cdot>y\<cdot>ora)"
    have srcdups_filtered_unfold:
      "srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
       = \<up>a' \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a')\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
      using a'_def False srcdups_sboolfilter_shd[of "y" "ora" a'] by blast
    have "\<exists>ora2. srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
                = sboolfilter\<cdot>(srcdups\<cdot>y)\<cdot>ora2" 
      using srcdups_filtered_unfold dropwhile_filter_ys IH_tail  srcdups_y  
      by (metis a'_def sboolfilter_sconc_false sboolfilter_sconc_true sdropwhile_shd_neq2)
    then show ?thesis by blast
  qed
qed

lemma srcdups_sboolfilter_id_if_fin_len_eq:
  assumes a1: "#(srcdups\<cdot>y) < \<infinity>"
      and a2: "#(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  shows "srcdups\<cdot>y = srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)"
  using assms 
  by (metis srcdups_sboolfilter_ex lnat_well_h2 sboolfilter_len_eq_imp_eq3)

lemma srcdups_sboolfilter_len_eq_imp: "#(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>y)) \<Longrightarrow>
   #(srcdups\<cdot>(sprojsnd\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
  #(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis linorder_not_less order_le_imp_less_or_eq slen_sprojfst slen_sprojsnd slen_srcdups_sboolfilter_leq
      srcdups_sprojsnd_swap_len_le)

lemma srcdups_sboolfilter_len_eq_imp2: "
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
  #(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis order_antisym_conv slen_sprojs_eq2 slen_sprojsnd slen_srcdups_sboolfilter_leq
      srcdups_sprojsnd_swap_len_le)


lemma sprojfst_srcdups_sboolfilter_id_if_fin_len_eq:
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<noteq> \<infinity> \<Longrightarrow>
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
   sprojfst\<cdot>(srcdups\<cdot>y) = sprojfst\<cdot>(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis inf_ub order_le_imp_less_or_eq slen_sprojfst srcdups_sboolfilter_id_if_fin_len_eq
      srcdups_sboolfilter_len_eq_imp2)

lemma sprojfst_srcdups_sboolfilter_id_if_fin_len_eq2:
  "#(srcdups\<cdot>y) < \<infinity> \<Longrightarrow>
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>y)) \<Longrightarrow>
   #(srcdups\<cdot>(sprojsnd\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
   sprojfst\<cdot>(srcdups\<cdot>y) = sprojfst\<cdot>(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  using srcdups_sboolfilter_len_eq_imp srcdups_sboolfilter_id_if_fin_len_eq by metis


lemma
  sfilter_finites_suffix:
  assumes "#s = \<infinity>"
    and "#(M \<ominus> s) \<noteq> \<infinity>"
  shows "\<exists>n. \<forall> i \<ge> n. snth i s \<notin> M"
proof-
  obtain s1 s2 n
    where s_eq: "s = s1 \<Zcat> s2"
      and s_len: "Fin n = #s1"
      and s2_no_m: "M \<ominus> s2 = \<epsilon>"
    by (metis assms(1,2) order_less_le sfilter_fin slen_sfilterl1 slen_stake_fst_inf split_streaml1)

  have "\<And>i. snth (n + i) s = snth i s2"
    by(simp add: s_eq snth_scons2 s_len)

  then have i_in_s2: "\<forall>i\<ge>n. snth i s = snth (i-n) s2"
    by (metis le_add_diff_inverse)

  have s2_no_m_snth: "\<And>i. snth i s2 \<notin> M"
    using s2_no_m
    by (metis assms(1) fair_sdrop fin_le_inf s_eq s_len sdropl6 snth_filter)

  show ?thesis
    apply(rule_tac x="n" in exI)
    by(simp add: i_in_s2 s2_no_m_snth)
qed

lemma shd_filter: "#s > 0 \<Longrightarrow> shd s \<in> M \<Longrightarrow> sfilter M\<cdot>s \<noteq> \<epsilon>"
  by(rule snth_filter[of 0], auto)

lemma shd_filter_shd: "#s > 0 \<Longrightarrow> shd s \<in> M \<Longrightarrow> shd (sfilter M\<cdot>s) = shd s"
  by (metis Stream.slen_empty_eq order_less_le sfilter_in shd1 surj_scons)


lemma
  sfilter_inf_snthI:
  assumes "#(M \<ominus> s) = \<infinity>"
  shows "\<And>i. \<exists>j \<ge> i. snth j s \<in> M"
  apply(rule ccontr, simp)
  apply(subgoal_tac "#(M \<ominus> sdrop i\<cdot>s) = \<infinity>")
  defer
  using assms slen_sfilter_sdrop apply blast
  by (simp add: ex_snth_in_sfilter_nempty snth_sdrop)

lemma
  sfilter_inf_snthE:
  assumes "#s = \<infinity>"
    and "\<And>i. \<exists>j \<ge> i. snth j s \<in> M"
  shows "#(M \<ominus> s) = \<infinity>"
  by (meson assms(1,2) sfilter_finites_suffix)


lemma
  snth_sfilter_ex3:
  assumes "#s = \<infinity>"
    and "\<And>i. \<exists>j\<ge>i. snth j s \<in> A"
  shows "\<And>i. \<exists>j\<ge>i. snth j (A \<ominus> s) \<in> A"
proof (rule ccontr, simp)
  fix i :: nat
  assume a: "\<forall>j\<ge>i. snth j (A \<ominus> s) \<notin> A"
  obtain j m where "j \<ge> i" and "m = snth j s" and "m \<in> A"
    using assms(2) by blast
  then have "m \<in> sValues\<cdot>(A \<ominus> s)"
    by (simp add: assms(1) snth2sValues)
  show False
    by (metis Int_iff assms(1,2) fin_le_inf a sValues_sfilter sfilter_finites_suffix snth2sValues)
qed

lemma
  snth_sfilter_ex3_subset:
  assumes "#(A \<ominus> s) = \<infinity>"
    and "A \<subseteq> B"
    and "\<And>i. \<exists>j\<ge>i. snth j (A \<ominus> s) \<in> A"
  shows "\<And>i. \<exists>j\<ge>i. snth j (B \<ominus> s) \<in> A"
proof (rule ccontr, simp)
  fix i :: nat
  assume a: "\<forall>j\<ge>i. snth j (B \<ominus> s) \<notin> A"
  obtain j m where "j \<ge> i" and "m = snth j (A \<ominus> s)" and "m \<in> A"
    using assms by blast
  then have "m \<in> sValues\<cdot>(A \<ominus> s)"
    by (metis assms(1) fin_le_inf snth2sValues)
  then have "m \<in> sValues\<cdot>(B \<ominus> s)"
    using assms(2) by auto
  thus False
    by (metis a assms(1,2) inf.orderE int_sfilterl1 sfilter_inf_snthI)
qed


lemma sfilter_shd_snth_1: "shd s \<notin> M \<Longrightarrow> snth (Suc 0) s \<in> M \<Longrightarrow> shd (M \<ominus> s) = snth (Suc 0) s"
 by (metis (no_types, lifting) sfilter_in_sup sfilter_nin shd1 snth_rt snth_shd split_sfilter stake2shd stream.sel_rews(2) strict_sfilter
    surj_scons)

lemma sfilter_shd_in_snth_1: "shd s \<in> M \<Longrightarrow> snth (Suc 0) s \<in> M \<Longrightarrow> snth (Suc 0) (M \<ominus> s) = snth (Suc 0) s"
  by (metis Stream.slen_empty_eq[of "srt\<cdot>s"] linorder_less_linear[of "#(srt\<cdot>(s))" "\<bottom>"] lnat_le_zero[of "#(srt\<cdot>s)"]
      lnzero_def sconc_snd_empty[of "\<up>(shd (srt\<cdot>s))"] sfilter_in[of "shd s" "M" "srt\<cdot>s"]
      sfilter_in[of "shd (srt\<cdot>(s))" "M" \<epsilon>] sfilter_in_sup[of "shd (srt\<cdot>s)" "M::'a set"]
      shd_filter_shd[of "srt\<cdot>(s)" "M"] snth_rt[of "0" "\<up>(shd s) \<Zcat> (M::'a set) \<ominus> srt\<cdot>s"] snth_rt[of "0" "s"]
      snth_shd[of "srt\<cdot>(\<up>(shd s) \<Zcat> (M) \<ominus> srt\<cdot>s)"] snth_shd[of "srt\<cdot>s"]
      srt_supconc[of "shd s" "M \<ominus> srt\<cdot>s"] srt_supconc[of "shd (srt\<cdot>s)" \<epsilon>]
      srt_supconc[of "shd (srt\<cdot>s)" "M \<ominus> \<epsilon>"] surj_scons[of "s"])

lemma
  sfilter_snth_snth_suc:
  assumes "Fin e = #(M \<ominus> stake n\<cdot>s)"
  assumes "snth n s \<notin> M"
  assumes "snth (Suc n) s \<in> M"
  shows "snth e (M \<ominus> s) = snth (Suc n) s"
  by (smt Suc_def2 add.commute assms(1,2,3) sdropl6 sfilter_shd_snth_1 snth_def snth_sdrop split_sfilter)

lemma
  sfilter_snth_in_snth_suc':
  assumes "Fin e = #(M \<ominus> stake n\<cdot>s)"
  assumes "snth n s \<in> M"
  assumes "snth (Suc n) s \<in> M"
  shows "snth (Suc e) (M \<ominus> s) = snth (Suc n) s"
  by (smt Suc_def2 add.commute assms(1,2,3) sdropl6 sfilter_shd_in_snth_1 snth_def snth_sdrop split_sfilter)

lemma
  sfilter_snth_in_snth_suc:
  assumes "Fin e = lnsuc\<cdot>(#(M \<ominus> stake n\<cdot>s))"
  assumes "snth n s \<in> M"
  assumes "snth (Suc n) s \<in> M"
  shows "snth e (M \<ominus> s) = snth (Suc n) s"
proof-
  obtain e' where e'_eq: "Suc e' = e"
    by (metis Stream.slen_empty_eq assms(1) fin_zero not0_implies_Suc slen_scons supconc_neps)

  have 1: "Fin e' = #(M \<ominus> stake n\<cdot>s)"
    by (metis assms(1) e'_eq lnat_fin4)

  show ?thesis
    using sfilter_snth_in_snth_suc'[OF 1 assms(2,3)]
    using e'_eq by blast
qed

end
