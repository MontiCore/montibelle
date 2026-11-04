theory StreamRelator

imports stream.Stream
begin

definition rel_stream::"('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'b stream \<Rightarrow> bool"where
"rel_stream P s1 s2 = (#s1 = #s2 \<and> (\<forall>n. Fin n <#s1 \<longrightarrow> P (snth n s1) (snth n s2)))"

definition stream_all::"('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool"where
"stream_all P s = (\<forall>x\<in> sValues\<cdot>s. P x)"

lemma stream_allI:
  assumes"\<And>x. x\<in> sValues\<cdot>s \<Longrightarrow> P x"
  shows "stream_all P s"
  by(auto simp add: stream_all_def assms)


lemma rel_stream_Nil: "rel_stream P \<epsilon> ys = (ys = \<epsilon>)"
  apply (simp add: rel_stream_def)
  by (simp add: lnzero_def)

lemma rel_stream_Nil2: "rel_stream P xs \<epsilon> = (xs = \<epsilon>)"
  apply (simp add: rel_stream_def )
  using empty_is_shortest by auto



lemma nat_cases:"(\<forall>n. P n) = (P 0 \<and> (\<forall>n. P (Suc n)))"
  using old.nat.inducts by auto

lemma rel_stream_Cons:
  "rel_stream P (updis x && xs) (updis y && ys) = (P x y \<and> rel_stream P xs ys)"
  apply(simp add: lscons_conv rel_stream_def)
  apply(subst nat_cases)
  by auto


(*
lemma rel_stream_Cons1:
  "rel_stream P (updis x && xs) ys = (\<exists>z zs. ys = \<up>z \<Zcat> zs \<and> P x z \<and> rel_stream P xs zs)"
  apply(simp add: lscons_conv)
  sorry

lemma rel_stream_Cons2:
  "rel_stream P xs (updis y && ys) = (\<exists>z zs. xs = \<up>z \<Zcat> zs \<and> P z y \<and> rel_stream P zs ys)"
  apply(simp add: lscons_conv)
  sorry
*)
lemma [relator_eq,simp]:"(rel_stream (=)) = (=)"
  apply rule+
  by(rule snths_eq,simp_all add: rel_stream_def)

lemma rel_stream_mono[relator_mono]:assumes"A \<le> B"
  shows "rel_stream A \<le> rel_stream B"
  using assms unfolding rel_stream_def
  by auto

definition natstream::"nat stream"where
"natstream = fix\<cdot>(\<Lambda> s. \<up>0 \<Zcat> smap Suc\<cdot>s)"


lemma natstreamlenh:"#natstream \<noteq> Fin n"
proof(induction n)
  case 0
  then show ?case 
    sorry
next
  case (Suc n)
  then show ?case 
    apply(simp add: natstream_def)
    by(subst fix_eq,simp)
qed

lemma natstreamlen[simp]:"# natstream = \<infinity>"
  using natstreamlenh
  by (simp add: infI)

lemma natstream_snth[simp]:"snth n natstream = n"
proof(induction n)
  case 0
  then show ?case
    sorry
next
  case (Suc n)
  then show ?case
    apply(simp add: natstream_def)
    apply(subst fix_eq,simp)
    apply(subst smap_snth_lemma)
    using natstreamlen natstream_def apply auto[1]
    by simp
qed

definition f2s::"(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" where
"f2s f = smap f\<cdot>natstream"

lemma f2slen[simp]:"# (f2s f) = \<infinity>"
  by(simp add: f2s_def)

lemma f2s_snth[simp]:"snth n (f2s f) = f n"
  apply(simp add: f2s_def)
  apply(subst smap_snth_lemma)
  using natstreamlen natstream_def by auto

lemma snth_stake[simp]:"\<And>x. x < n \<Longrightarrow>  snth x(stake n\<cdot>(s)) = snth x s"
proof -
  fix x::nat
  show "x < n \<Longrightarrow> snth x (stake n\<cdot>s) = snth x s "
    apply(induction x arbitrary: n s,simp)
    apply(case_tac s,simp_all)
    using gr0_conv_Suc apply force
    apply(case_tac n,simp_all)
    by(case_tac s,simp_all)
qed

lemma rel_stream_OO[relator_distr,simp]: "rel_stream R OO rel_stream S = rel_stream (R OO S)"
  apply (rule sym)
  apply (intro ext)
  apply (rule iffI)
  unfolding rel_stream_def apply auto[2]
proof(subst relcompp_apply,auto)
  fix x::"'a stream" and xa::"'b stream"
  assume a1:"#x=#xa"
  assume a2:"\<forall>n. Fin n < #xa \<longrightarrow> (R OO S) (snth n x) (snth n xa)"
  then have "\<forall>n. Fin n< #xa \<longrightarrow> (\<exists>c. R (snth n x) c \<and> S c (snth n xa))"
    by(subst (asm) relcompp_apply,simp)
  then obtain f where f_def:"\<forall>n. Fin n < #xa \<longrightarrow> (R (snth n x) (f n) \<and> S (f n) (snth n xa))"
    by metis
  show "\<exists>b. #xa = #b \<and> (\<forall>n. Fin n < #xa \<longrightarrow> R (snth n x) (snth n b)) \<and> #b = #xa \<and> (\<forall>n. Fin n < #b \<longrightarrow> S (snth n b) (snth n xa))"
    apply(cases "#xa")
    apply(rule_tac x="stake x1\<cdot>(f2s f)" in exI)
    apply(auto simp add: f_def a1 a2)
    apply (simp add: slen_stake_fst_inf)+
    apply(auto simp add: f_def a1 a2)
    apply(rule_tac x="(f2s f)" in exI)
    by(auto simp add: f_def a1 a2)
qed

lemma rel_stream_lu[transfer_rule]:"left_unique (rel_stream (=)) "
  apply(rule left_uniqueI)
  apply(rule snths_eq)
  by(simp_all add: rel_stream_def)
 
lemma rel_stream_ru[transfer_rule]:"right_unique (rel_stream (=)) "
  apply(rule right_uniqueI)
  apply(rule snths_eq)
  by(simp_all add: rel_stream_def)
 
lemma [transfer_rule]:"bi_unique (rel_stream (=)) "
  apply(rule bi_uniqueI)
  by(simp_all only: rel_stream_lu rel_stream_ru)


lemma [transfer_rule]:"right_total (rel_stream (=)) "
  apply(rule right_totalI)
  apply(rule_tac x="y" in exI)
  by(simp_all add: rel_stream_def)



lemma left_total_rel_stream[transfer_rule]: 
  "left_total A \<Longrightarrow> left_total (rel_stream A)"
  apply(rule left_totalI)
proof(simp add: rel_stream_def, erule left_totalE)
  fix x::"'a stream"
  assume a1:"(\<And>x. \<exists>y. A x y)"
  then have "\<forall>n. Fin n< #x \<longrightarrow> (\<exists>c. A (snth n x) c)"
    by simp
  then obtain f where f_def:"\<forall>n. Fin n < #x \<longrightarrow> A (snth n x) (f n)"
    by metis
  show "\<exists>y. #x = #y \<and> (\<forall>n. Fin n < #x \<longrightarrow> A (snth n x) (snth n y))"
    apply(cases "#x")
    apply(rule_tac x="stake x1\<cdot>(f2s f)" in exI)
    apply(auto simp add: f_def a1)
    apply (simp add: slen_stake_fst_inf)+
    apply(rule_tac x="(f2s f)" in exI)
    by(auto simp add: f_def a1 )
qed

lemma left_unique_rel_stream[transfer_rule]: 
  "left_unique A \<Longrightarrow> left_unique (rel_stream A)"
  apply(rule left_uniqueI)
  apply(simp add: rel_stream_def left_unique_def)
  apply(rule snths_eq)
  by auto
  

lemma right_total_rel_stream [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (rel_stream A)"
  apply(rule right_totalI)
proof(simp add: rel_stream_def right_total_def)
  fix y::"'b stream"
  assume a1:"\<forall>y. \<exists>x. A x y"
  then have "\<forall>n. Fin n< #y \<longrightarrow> (\<exists>c. A c (snth n y))"
    by simp
  then obtain f where f_def:"\<forall>n. Fin n < #y \<longrightarrow> A (f n) (snth n y)"
    by metis
  show "\<exists>x. #x = #y \<and> (\<forall>n. Fin n < #x \<longrightarrow> A (snth n x) (snth n y))"
    apply(cases "#y")
    apply(rule_tac x="stake x1\<cdot>(f2s f)" in exI)
    apply(auto simp add: f_def a1)
    apply (simp add: slen_stake_fst_inf f_def)+
    apply(rule_tac x="(f2s f)" in exI)
    by(auto simp add: f_def a1)
qed

lemma right_unique_rel_stream [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (rel_stream A)"
  apply(rule right_uniqueI)
  apply(simp add: rel_stream_def right_unique_def)
  apply(rule snths_eq)
  by auto
  

lemma bi_total_rel_stream [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (rel_stream A)"
  apply(rule bi_totalI)
  by (simp_all add: bi_total_alt_def left_total_rel_stream right_total_rel_stream)

lemma bi_unique_rel_stream [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (rel_stream A)"
  apply(rule bi_uniqueI)
  by (simp_all add: bi_unique_alt_def left_unique_rel_stream right_unique_rel_stream)

 
lemma rel_stream_conversep [simp]: "rel_stream A\<inverse>\<inverse> = (rel_stream A)\<inverse>\<inverse>"
  apply rule+
  unfolding rel_stream_def by auto

definition map_stream::"('a \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b stream"where
"map_stream f = Rep_cfun (smap f)"


lemma quotient_stream[quot_map]: 
  assumes"Quotient R Abs Rep T"
  shows "Quotient (rel_stream R) (map_stream Abs) (map_stream Rep) (rel_stream T)"
  apply(insert assms,simp add: map_stream_def)
  unfolding Quotient_alt_def4
  apply (simp add: rel_stream_OO[symmetric])+
  apply (simp add: rel_stream_def)
  apply auto
  by (simp_all add: smap_snth_lemma snths_eq)


functor map_stream
  by(auto simp add: o_def map_stream_def smapsmap2smap)

setup_lifting type_definition_stream


end