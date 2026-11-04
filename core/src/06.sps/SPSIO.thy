theory SPSIO

imports SPSComp
begin




definition spsIO::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set" where
"spsIO sps = {(sb, spf\<cdot>sb) | sb spf. spf\<in>sps}"


theorem sps_union_io: "spsIO (sps1 \<union> sps2) = (spsIO sps1) \<union> (spsIO sps2)"
  by(auto simp add: spsIO_def)

lemma sps_union: "spsIO (\<Union> SPSs) = \<Union>{spsIO sps | sps .sps \<in> SPSs}"
  by(auto simp add: spsIO_def)


theorem spscomplete_set:
 "spsComplete sps = {spf . spfIO spf \<subseteq> spsIO sps}"
  unfolding spsComplete_def spsIO_def spfIO_def
  apply auto[1]
  by auto


theorem spscomplete_io: "spsIO (spsComplete sps) = spsIO sps"
  unfolding spsComplete_def spsIO_def
  apply auto[1]
  by auto


theorem spscomplete_ioeq: assumes "spsIO sps1 = spsIO sps2"
  shows "spsComplete sps1 = spsComplete sps2"
  apply(simp add: spscomplete_set)
  using assms spsIO_def by blast


theorem spsio_empty[simp]: "spsIO {} = {}"
  unfolding spsIO_def
  by blast


theorem spsio_one: "spsIO {f} = spfIO f"
  by(simp add: spsIO_def spfIO_def)


theorem spsio_univ: "spsIO UNIV = UNIV"
  apply(auto simp add: spsIO_def)[1]
  apply(rule_tac x="\<Lambda> x. b" in exI)
  by simp


theorem spsio_refine: assumes "sps1 \<subseteq> sps2"
  shows "spsIO sps1 \<subseteq> spsIO sps2"
  apply(simp add: spsIO_def)
  using assms by blast

                                               
theorem assumes "spsIsConsistent sps" shows "spsIO sps \<noteq> {}"
  apply(simp add: spsIO_def)
  using assms spsIsConsistent_def by blast

(*
text\<open>The input/output behaviour of a composed \gls{sps} looks like 
the following.\<close>

theorem spscfcomp_io: 
  "spsIO (spsCfcomp sps1 sps2) = {(sb, spf1\<cdot>(spf2\<cdot>sb)) | sb spf1 spf2. 
                                          spf1\<in>sps1 \<and> spf2\<in>sps2}"
  apply(simp add: spsIO_def spsCfcomp_def)
  by force
*)


definition spsIOtoSet :: "('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set" where
"spsIOtoSet s = {f | f. \<forall> a. (a,f\<cdot>a) \<in> s}"


theorem spsiotoset_apply: "spsIOtoSet (spsIO f) = spsComplete f"
  apply(simp add: spsIOtoSet_def spsIO_def spsComplete_def)
  by blast


theorem spsiotoset_complete: "spsComplete (spsIOtoSet s) = (spsIOtoSet s)"
  apply(simp add: spsIOtoSet_def spsComplete_def)
  by (metis (mono_tags, opaque_lifting))

lemma assumes "spsIsComplete f"
  shows "spsIOtoSet (spsIO f) = f"
  using assms spsIsComplete_def spsiotoset_apply by auto



definition rel2sps::"('I::cpo \<Rightarrow> 'O::cpo \<Rightarrow> bool) \<Rightarrow> ('I \<rightarrow> 'O) set" where
"rel2sps P = {spf | spf. \<forall>input. P input (spf\<cdot>input)}"
end
