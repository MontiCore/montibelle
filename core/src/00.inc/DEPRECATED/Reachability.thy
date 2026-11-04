
theory Reachability
imports inc.SetPcpo
begin

default_sort type


primrec reachn::"nat \<Rightarrow> 's set \<Rightarrow> ('s \<Rightarrow> 'i \<Rightarrow>('s \<times> 'o)set) \<Rightarrow> 's set" where
"reachn 0 S f = S" |
"reachn (Suc n) S f = \<Union>{(fst `(f state i)) | state i. state\<in> reachn n S f}"


lemma reach_def2helper:"\<Union>{(fst `(f state i)) | state i. state\<in> reachn n S f} = reachn n (\<Union>{fst `(f state i) | state i. state\<in>S}) f"
  by(induction n,auto)

lemma reachn_def2:"reachn (Suc n) S f = reachn n (\<Union>{fst `(f s i) | s i. s\<in>S}) f"
  using reach_def2helper by (metis reachn.simps(2))

lemma reachnsimps[simp]:
  "reachn 0 S f = S"
  "reachn (Suc n) S f = \<Union>{(fst `(f state i)) | state i. state\<in> reachn n S f}"
  by simp+
  
lemma reachn_step: 
  assumes "state\<in> reachn n S f"
  shows"fst`(f state i) \<subseteq> reachn (Suc n) S f"
  using assms by auto


definition occurn::"nat \<Rightarrow> 's set \<Rightarrow>('s \<Rightarrow> 'i \<Rightarrow>('s \<times> 'o)set) \<Rightarrow> 's set" where
"occurn n S f = \<Union>{reachn m S f | m. m \<le> n}"



theorem reachn_sub_occurn:"reachn n S f \<subseteq> occurn n S f"
  by(auto simp add: occurn_def)

theorem reachn_sub_occurm:"n\<le>m \<Longrightarrow> reachn n S f \<subseteq> occurn m S f"
  by(auto simp add: occurn_def)
  
lemma [simp]:
  assumes"state\<in> reachn n S f"
  and "n < m"
  shows"fst`(f state i) \<subseteq> occurn m S f"
  proof -
    have "Suc n \<le> m"
      using assms(2) by linarith
    then show ?thesis
      by (meson assms(1) dual_order.trans reachn_step reachn_sub_occurm)
  qed

lemma [simp]:"S \<subseteq> occurn n S f"
  using reachn_sub_occurm[of 0 n S f] by auto

theorem occurn_chain:"chain (\<lambda>n. occurn n S f)"
  apply(rule chainI)
  by(auto simp add: le_Suc_eq occurn_def less_set_def)


definition reach::"'s set \<Rightarrow> ('s \<Rightarrow> 'i \<Rightarrow>('s \<times> 'o)set) \<Rightarrow> 's set" where
"reach S f \<equiv> \<Squnion>n. reachn n S f"

abbreviation "unreachable S T \<equiv> UNIV - reach S T"




lemma reach_insert:"reach S f = (\<Union>n. reachn n S f)"
  by(simp add: reach_def lub_eq_Union)

hide_fact reach_def

lemma reach_insert2:"reach S f = (\<Union>n. occurn n S f)"
  by(auto simp add: reach_insert occurn_def)

lemma reach_unfold:"reach S f = (\<Union>n. reachn n S f) \<union>(reachn n S f)"
  by(auto simp add: reach_insert)

lemma 
  assumes "\<forall>s i. \<forall>(ns,no)\<in> T s i. I s \<longrightarrow> I ns"  
  and "\<forall>s\<in>S. I s"
  and "x \<in> reach S T"
  shows"I x"
  oops

lemma [simp]:"range nat = UNIV"
  apply auto
  apply(subst nat_int[symmetric])
  by blast



lemma testreach:"reach {0::nat} (\<lambda>n i. {(Suc n,i)}) = range nat"
  oops


primrec idn::"'i list \<Rightarrow>('i \<Rightarrow>('s \<times> 'o)list) \<Rightarrow> ('s list)"where
"idn [] f = []" |
"idn (x#xs) f = (map fst (f x)) @ idn xs f"

definition set2list::"'a::finite set \<Rightarrow> 'a list" where
"set2list S = folding.F Cons [] S"

primrec listreachn_h::"'s list \<Rightarrow> ('s \<Rightarrow> 'i::finite \<Rightarrow>('s \<times> 'o)list) \<Rightarrow> 's list" where
"listreachn_h [] f = []" |
"listreachn_h (x#xs) f = (idn (set2list UNIV) (f x)) @ listreachn_h xs f"

primrec listreachn::"nat \<Rightarrow> 's list \<Rightarrow> ('s \<Rightarrow> 'i::finite \<Rightarrow>('s \<times> 'o)list) \<Rightarrow> 's list" where
"listreachn 0 L f = L" |
"listreachn (Suc n) L f = listreachn_h (listreachn n L f) f"



primrec reachi::"'s set \<Rightarrow> 'i list \<Rightarrow> ('s \<Rightarrow> 'i \<Rightarrow>('s \<times> 'o)set) \<Rightarrow> 's set" where
"reachi S [] f = S" |
"reachi S (x#xs) f = reachi (\<Union>{fst ` (f s x) | s. s\<in>S}) xs f"

lemma reachi_step: 
  assumes "state\<in> reachi S ls f"
  shows"fst`(f state x) \<subseteq> reachi  S (ls@[x]) f"
  using assms
  by(induction ls arbitrary: S,auto)
 


primrec occuri::"'s set \<Rightarrow> 'i list \<Rightarrow>('s \<Rightarrow> 'i \<Rightarrow>('s \<times> 'o)set) \<Rightarrow> 's set" where
"occuri S [] f = S" |
"occuri S (x#xs) f = S \<union> occuri  (\<Union>{fst ` (f s x) | s. s\<in>S}) xs f"


theorem reachi_sub_occuri:"reachi S I f \<subseteq> occuri S I f"
  by(induction I arbitrary: S,auto)

theorem reachl_sub_occurls:"reachi S ls f \<subseteq> occuri S (ls@rst) f"
  apply(induction ls arbitrary: S,auto)
  by(cases rst,simp_all)
  
lemma [simp]:
  assumes"state\<in> reachi S I f"
  shows"fst`(f state x) \<subseteq> occuri S (I@(x#xs))f"
  using assms reachi_step reachl_sub_occurls by fastforce

lemma [simp]:"S \<subseteq> occuri S I f" 
  by(cases I,simp_all)

lemma reachi_sub_reachn:
  assumes "S1 \<subseteq> S2"
  shows "reachi S1 I f \<subseteq> reachn (length I) S2 f"
  using assms
  apply(induction I arbitrary: S1 S2,simp)
  apply(simp only: length_Cons reachn_def2 reachi.simps)
  apply(subgoal_tac "(\<Union> {fst ` f s a |s. s \<in> S1}) \<subseteq> (\<Union> {fst ` f s i |s i. s \<in> S2})")
  apply auto
  by (metis fst_conv image_eqI subset_iff)

theorem reachi_sub_reachn2: "reachi S I f \<subseteq> reachn (length I) S f"
  by(simp add: reachi_sub_reachn)

value"reachi {1::int,4} [1,5,8,4] (\<lambda>n i. {(n+i,i), (n-i,n)})"


definition freach_h :: "('s \<Rightarrow> 'i \<Rightarrow> ('s \<times> 'o)) \<Rightarrow> 's \<Rightarrow> 'i set \<Rightarrow> 's set  \<Rightarrow> 's set" where
  "freach_h f initial domain states 
     = states \<union> {fst (f s elem) | elem s. s \<in> (states \<union> {initial}) \<and> elem \<in> domain}"

definition freach :: "('s \<Rightarrow> 'i \<Rightarrow> ('s \<times> 'o)) \<Rightarrow> 's \<Rightarrow> 'i set \<Rightarrow> 's set" where
  "freach f initial domain = {initial} \<union> fix\<cdot>(\<Lambda> S. freach_h f initial domain S)"

lemma freach_h_mono: "monofun (\<lambda>S. freach_h f initial domain S)"
  apply (rule monofunI)
  by (auto simp add: less_set_def freach_h_def)

lemma freach_h_cont[simp]: "cont (\<lambda>S. freach_h f initial domain S)"
  apply (rule contI2)
  apply (simp add: freach_h_mono)
  by (auto simp add: chain_def less_set_def lub_eq_Union freach_h_def)

lemma freach_insert: 
  "freach f initial domain = {initial} \<union> freach f initial domain 
     \<union> {fst (f s elem) | elem s. s \<in> (freach f initial domain \<union> {initial}) \<and> elem \<in> domain}"
  apply (subst freach_def)
  apply(subst fix_eq,simp)
  apply(simp add: freach_h_def)
  by (simp add: freach_def)

lemma freach_empty [simp]: "freach f i {} = {i}"
  apply (simp add: freach_def)
  apply (subst fix_strict)
  apply (simp add: freach_h_def) 
  by (simp add: UU_eq_empty)

lemma freach_mono: "monofun (freach f i)"
  apply (rule monofunI)
  apply (simp add: less_set_def)
  apply (simp add: freach_def)
  apply (rule parallel_fix_ind, auto)
  apply (rule admI)
  apply (subgoal_tac "fst (\<Squnion>i. Y i) = (\<Union>i. fst (Y i))", simp)
  apply (subgoal_tac "snd (\<Squnion>i. Y i) = (\<Union>i. snd (Y i))", simp)
  apply blast
  apply (metis (mono_tags, lifting) lub_prod set_cpo_simps(2) snd_conv)
  apply (simp add: lub_prod set_cpo_simps(2))
  by (auto simp add: freach_h_def)

lemma freach_initial_in:
  "i \<in> freach f i domain"
  by (simp add: freach_def)

lemma freach_suc_in:
  assumes "a \<in> freach f i domain"
  shows "\<forall>e \<in> domain. fst (f a e) \<in> freach f i domain"
  using assms freach_insert by fastforce

end