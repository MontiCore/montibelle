theory StreamOther
imports StreamWhile StreamIterate StreamFilter
begin


text \<open>Some special results about @{term smap} and injective functions
  on streams of natural successors\<close>
lemma inj_sfilter_smap_siteratel1:
  "inj f \<Longrightarrow> sfilter {f j}\<cdot>(smap f\<cdot>(siterate Suc (Suc (k + j)))) = \<epsilon>"
apply (rule ex_snth_in_sfilter_nempty [rule_format])
apply (simp add: atomize_imp)
apply (rule impI)
apply (subst smap_snth_lemma, simp+)
apply (simp add: snth_siterate_Suc)
apply (rule notI)
by (frule_tac x="Suc (n+(k+j))" and y="j" in injD, simp+)

lemma inj_sfilter_smap_siteratel2[simp]:
  "inj f \<Longrightarrow> #(sfilter {m}\<cdot>(smap f\<cdot>(siterate Suc j))) \<noteq> \<infinity>"
apply (case_tac "m\<in>range f")
apply (rule_tac b="m" and f="f" in rangeE, simp+)
apply (rule notI)
apply (drule_tac n="Suc x" in slen_sfilter_sdrop [rule_format], simp)
apply (simp add: sdrop_siterate)
apply (simp add: inj_sfilter_smap_siteratel1)
by (simp add: sfilter_smap_nrange)


end