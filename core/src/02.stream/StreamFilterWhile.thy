theory StreamFilterWhile
imports StreamFilter StreamWhile

begin





text \<open>@{term sfilter} after @{term stakewhile}: produce the empty stream\<close>
lemma sfilter_twl1[simp]: 
  "sfilter X\<cdot>(stakewhile (\<lambda>x. x\<notin>X)\<cdot>p) = \<epsilon>"
apply (rule ind [of _ p], auto)
by (case_tac "a\<in>X", auto)

text \<open>@{term sfilter} after @{term stakewhile}: redundant filtering\<close>
lemma sfilter_twl2[simp]: 
  "sfilter X\<cdot>(stakewhile (\<lambda>x. x\<in>X)\<cdot>p) = stakewhile (\<lambda>x. x\<in>X)\<cdot>p"
apply (rule ind [of _ p], auto)
by (case_tac "a\<in>X", auto)


lemma sfilter_dwl1[simp]: 
  "sfilter X\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p) = sfilter X\<cdot>p"
apply (rule ind [of _ p], auto)
by (case_tac "a\<in>X", auto)

lemma sfilter_dwl2:
  "sfilter T\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> sdropwhile (\<lambda>a. a \<notin> T)\<cdot>s \<noteq> \<epsilon>"
apply (rule notI)
apply (erule notE)
apply (subst sfilter_dwl1 [THEN sym])
  by simp


text \<open>elimination rule for @{term sfilter} after @{term sdropwhile}\<close>
lemma sfilter_srtdwl3[simp]: 
  "sfilter X\<cdot>(srt\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p)) = srt\<cdot>(sfilter X\<cdot>p)"
apply (rule ind [of _ p], auto)
  by (case_tac "a\<in>X", auto)


text \<open>@{term "sfilter M"} after @{term "srtdw (\<lambda>x. x \<notin> M)"} almost behaves
  like @{term "sfilter M"} alone\<close>
lemma sfilterl8:
  "sfilter M\<cdot>x \<noteq> \<epsilon> \<Longrightarrow>
    #(sfilter M\<cdot>x) = lnsuc\<cdot>(#(sfilter M\<cdot>(srtdw (\<lambda>x. x \<notin> M)\<cdot>x)))"
  apply(induction x rule: ind)
  apply (simp add: len_stream_def; fail)
  apply auto[1]
  by (case_tac "a \<in> M", auto)

lemma sfilter_srtdwl2:
  "#(sfilter X\<cdot>s) = \<infinity> \<Longrightarrow> #(sfilter X\<cdot>(srtdw (\<lambda>a. a \<notin> X)\<cdot>s)) = \<infinity>"
apply (case_tac "sfilter X\<cdot>s = \<epsilon>", auto)
by (drule sfilterl8, auto)


lemma strdw_filter_h: "b\<in>sValues\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
proof(rule ind [of _s])
  have "adm (\<lambda>a. lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by (simp add: len_stream_def)
  thus "adm (\<lambda>a. b \<in> sValues\<cdot>a \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by simp
  show "b \<in> sValues\<cdot>\<epsilon> \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>\<epsilon>)) = #({b} \<ominus> \<epsilon>)" by simp
  fix a 
  fix s
  assume IH: " b \<in> sValues\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
  show " b \<in> sValues\<cdot>(\<up>a \<Zcat> s) \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<Zcat> s))) = #({b} \<ominus> \<up>a \<Zcat> s)"
  proof (cases "a=b")
    case True thus ?thesis by simp 
  next
    case False
    hence f1:"#({b} \<ominus> \<up>a \<Zcat> s) = #({b} \<ominus> s)" using sfilter_nin singletonD by auto
    hence f2:"#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<Zcat> s)) = #({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(s))" using False by auto
    hence "b \<in> sValues\<cdot>(\<up>a \<Zcat> s) \<Longrightarrow> b\<in>sValues\<cdot>s" using False by auto
    thus ?thesis using IH f2 local.f1 by auto 
  qed
qed

lemma strdw_filter: "b\<in>sValues\<cdot>s \<Longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
by(simp add: strdw_filter_h)

lemma stwbl_filterlen[simp]: "b\<in>sValues\<cdot>ts \<longrightarrow> #({b} \<ominus> stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts) = Fin 1"
  apply(rule ind [of _ ts])
    apply(rule adm_imp)
     apply simp
    apply (simp add: len_stream_def; fail)
   apply (simp; fail)
  apply auto[1]
  by (metis (mono_tags, lifting) Fin_02bot Fin_Suc One_nat_def lnzero_def sconc_snd_empty sfilter_in sfilter_nin singletonD singletonI slen_scons strict_sfilter slen_zero stwbl_f stwbl_t)











text \<open>After filtering by filter @{term T}, the head of the result is in @{term T}
  (for non-empty results)\<close>
lemma sfilter_ne_resup: "sfilter T\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (sfilter T\<cdot>s) \<in> T"
apply (subst sfilter_dwl1 [THEN sym])
apply (rule_tac x="sdropwhile (\<lambda>x. x \<notin> T)\<cdot>s" in scases, auto)
apply (drule sfilter_dwl2, simp)
apply (rule_tac x="s" in scases, auto)
apply (case_tac "aa \<in> T", auto)
apply (drule inject_scons, simp)
by (drule sdropwhile_resup, simp) 


text \<open>same result for @{term sconc} syntax\<close>
lemma sfilter_resl2:
  "sfilter T\<cdot>s = \<up>a \<Zcat> as \<Longrightarrow> a \<in> T"
apply (case_tac "sfilter T\<cdot>s = \<epsilon>", simp)
by (drule sfilter_ne_resup, simp)

text \<open>After filtering with filter @{term T}, each element is in @{term T}\<close>
lemma sfilterl7:
  "\<lbrakk>Fin n < #x; sfilter T\<cdot>s = x\<rbrakk> \<Longrightarrow> snth n x \<in> T"
apply (simp add: atomize_imp)
apply (rule_tac x="s" in spec)
apply (rule_tac x="x" in spec)
apply (induct_tac n, auto)
apply (rule sfilter_ne_resup)
apply (rule_tac x="sfilter T\<cdot>xa" in scases, auto)
apply (rule_tac x="xa" in scases, auto)
apply (simp add: Fin_Suc [THEN sym] del: Fin_Suc)
apply (case_tac "a \<in> T", auto)
apply (case_tac "sfilter T\<cdot>s = \<epsilon>",simp+)
apply (simp add: Fin_Suc [THEN sym] del: Fin_Suc)
apply (rule_tac x="sfilter T\<cdot>s" in scases, auto)
apply (erule_tac x="sa" in allE,simp+)
apply (frule sfilter_resl2)
  apply (drule mp)
by (rule_tac x="srt\<cdot>(sdropwhile (\<lambda>x. x\<notin>T)\<cdot>s)" in exI,simp+)


lemma sfilter_red:assumes "\<And>t. t\<in> sValues\<cdot>s2 \<Longrightarrow> t\<notin> S"
  shows "sfilter S\<cdot>(s1\<Zcat>s2) = sfilter S\<cdot>s1"
  apply(cases "#s1 = \<infinity>",simp)
  apply(subst add_sfilter2)
  apply (simp add: not_le_imp_less)
  using assms 
  apply(subgoal_tac "S \<ominus> s2 = \<epsilon>",simp)
  by (metis sbfilter_sbdom sfilter_ne_resup sfilter_sValuesl3)


lemma sValues_sfilter1: assumes "x\<in>sValues\<cdot>(A\<ominus>s)" 
  shows "x\<in>A"
  using assms apply(simp add: sValues_def2)
  using sfilterl7 by blast

lemma sfilterEq2sValues_h: "sfilter A\<cdot>s = s \<longrightarrow> sValues\<cdot>s \<subseteq> A"
  apply(rule ind [of _s])
  apply (subst admI sValues_sfilter)
  apply (metis inf.orderI sValues_sfilter)
  apply(simp)
  apply(simp; fail)
  apply(rule impI)
  by (metis inf.orderI sValues_sfilter)

lemma sfilterEq2sValues: "sfilter A\<cdot>s = s \<Longrightarrow> sValues\<cdot>s \<subseteq> A"
  by (simp add: sfilterEq2sValues_h)

lemma lshd_dropwhile: "lshd\<cdot>((sdropwhile (\<lambda>x. x\<notin>S)\<cdot>input)) = lshd\<cdot>( S \<ominus> input)"
  apply(induction input; simp?)
  by(rename_tac msg input, case_tac "msg \<in> S"; simp)

lemma shd_dropwhile: assumes "( S \<ominus> input) \<noteq> \<epsilon>"
  shows "shd ((sdropwhile (\<lambda>x. x\<notin>S)\<cdot>input)) = shd ( S \<ominus> input)"
  apply(subst shd_def, subst lshd_dropwhile, subst shd_def[symmetric])
  ..

lemma filtered_stream_step:
  assumes " S \<ominus> input \<noteq> \<epsilon>"
  shows "input = ((stakewhile (\<lambda>x. x\<notin>S)\<cdot>input) \<Zcat> (\<up>(shd (S \<ominus> input))) \<Zcat> srt\<cdot>(sdropwhile (\<lambda>x. x\<notin>S)\<cdot>input))"
  by (metis  sfilter_dwl2 surj_scons shd_dropwhile assms stakewhileDropwhile)

lemma stakewhile_finite: assumes "S \<ominus> input \<noteq> \<epsilon>"
  shows "#(stakewhile (\<lambda>x. x \<notin> S)\<cdot>input) < \<infinity>"
proof (rule ccontr)
  assume "\<not> #(stakewhile (\<lambda>x. x \<notin> S)\<cdot>input) < \<infinity>"
  hence "#(stakewhile (\<lambda>x. x \<notin> S)\<cdot>input) = \<infinity>"
    by(cases "#(stakewhile (\<lambda>x. x \<notin> S)\<cdot>input)"; simp)
  hence h1: "input = (stakewhile (\<lambda>x::'a. x \<notin> S)\<cdot>input)"
    apply(subst filtered_stream_step[OF assms])
    using sconc_fst_inf by blast
  have "S \<ominus> input = \<epsilon>"
    by (subst h1, simp)
  thus False     
    using assms by blast
qed


end