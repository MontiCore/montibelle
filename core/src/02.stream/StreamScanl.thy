theory StreamScanl
imports stream.Stream

begin


primrec SSCANL::
"nat \<Rightarrow> ('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i stream \<Rightarrow> 'o stream" where
  SSCANL_zero_def: "SSCANL 0 f q s = \<epsilon>" |
  "SSCANL (Suc n) f q s = (if s=\<epsilon> then \<epsilon> 
                           else \<up>(f q (shd s)) \<Zcat> 
                                (SSCANL n f (f q (shd s)) (srt\<cdot>s)))"

text \<open>@{term sscanl}: Apply a function elementwise to the input
stream. Behaves like \<open>map\<close>, but also takes the previously generated
output element as additional input to the function. For the first 
computation, an initial value is provided.\<close>
definition sscanl :: "('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i stream \<rightarrow> 'o stream" where
"sscanl f q \<equiv> \<Lambda> s. \<Squnion>i. SSCANL i f q s"

subsection \<open>@{term sscanl}\<close>

lemma SSCANL_empty[simp]: "SSCANL n f q \<epsilon> = \<epsilon>"
by (induct_tac n, auto)

lemma mono_SSCANL: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> SSCANL n f q x \<sqsubseteq> SSCANL n f q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
by (simp, rule monofun_cfun_arg, simp)

text \<open>result of @{term "SSCANL n"} only depends on first @{term n}
  elements of input stream\<close>
lemma contlub_SSCANL:
  "\<forall>f q s. SSCANL n f q s = SSCANL n f q (stake n\<cdot>s)"
apply (induct_tac n, auto)
apply (rule_tac x=s in scases)
apply auto[2]
apply (rule_tac x=s in scases)
by auto

text \<open>@{term SSCANL} is a chain. This means that, for all fixed inputs,
  @{term "SSCANL i"} returns a prefix of @{term "SSCANL (Suc i)"}\<close>
lemma chain_SSCANL: "chain SSCANL"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (rule monofun_cfun_arg)
apply (erule_tac x="x" in allE)
apply (erule_tac x="x xa (shd xb)" in allE)
by (erule_tac x="srt\<cdot>xb" in allE, auto)

text \<open>@{term sscanl} is a continuous function\<close>
lemma cont_lub_SSCANL: "cont (\<lambda>s. \<Squnion>i. SSCANL i f q s)" 
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "q"])
apply (rule fun_belowD [of _ _ "f"])
apply (rule chainE)
apply (rule chain_SSCANL)
apply (rule pr_contI)
apply (rule monofunI)
apply (rule mono_SSCANL [rule_format], assumption)
apply (rule allI)
apply (rule_tac x="i" in exI)
by (rule contlub_SSCANL [rule_format])

text \<open>Basic simplification rules for @{term sscanl}\<close>
lemma sscanl_empty[simp]: "sscanl f q\<cdot>\<epsilon> = \<epsilon>"
apply (simp add: sscanl_def)
apply (subst beta_cfun, rule cont_lub_SSCANL)
by (subst is_lub_const 
  [THEN lub_eqI, of "\<epsilon>", THEN sym], simp)

lemma sscanl_scons[simp]: 
  "sscanl f q\<cdot>(\<up>a\<Zcat>s) = \<up>(f q a) \<Zcat> sscanl f (f q a)\<cdot>s"  
apply (simp add: sscanl_def)
apply (subst beta_cfun, rule cont_lub_SSCANL)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (rule chain_SSCANL [THEN chainE])
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
by (rule chain_SSCANL [THEN chainE], simp)

lemma sscanl_one[simp]: "sscanl f a\<cdot>(\<up>b) = \<up>(f a b)"
by (insert sscanl_scons [of f a b \<epsilon>], auto)

text \<open>applying @{term sscanl} never shortens the stream\<close>
lemma fair2_sscanl: "#x \<le> #(sscanl f a\<cdot>x)"
apply (rule spec [where x = a])
  apply (rule ind [of _ x], auto)
  apply(simp add: len_stream_def)
by (subst lnle_def, simp del: lnle_conv)

lemma sscanl_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanl f q\<cdot>s) = (f q (shd s))"
by (metis shd1 sscanl_scons surj_scons)

lemma sscanl_srt: "srt\<cdot>(sscanl f a\<cdot>s) = sscanl f (f a (shd s)) \<cdot>(srt\<cdot>s) "
by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanl_empty sscanl_scons stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

lemma sscanl_snth:  "Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sscanl f a\<cdot>s) = f (snth n (sscanl f a\<cdot>s)) (snth (Suc n) s)"
  apply(induction n arbitrary:  a s)
  apply(rule_tac x="s" in scases;simp)
  apply (metis less_irrefl only_empty_has_length_0 sscanl_shd)
  by(rule_tac x="s" in scases;simp)

lemma fair_sscanl[simp]: "#(sscanl f a\<cdot>x) = #x"
apply (rule spec [where x = a])
by (rule ind [of _ x], auto, simp add: len_stream_def)


primrec sscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"sscanl_nth 0 f q s =  f q (shd s)" |
"sscanl_nth (Suc n) f q s = sscanl_nth n f (f q (shd s)) (srt\<cdot>s)"

lemma sscanl2sscanl_nth:
  "Fin n<#s \<Longrightarrow> snth n (sscanl f q\<cdot>s) = sscanl_nth n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a stream" and k :: "lnat"
  assume a1: "0 < #s"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0_rev slen_zero by auto
  thus "shd (sscanl f q\<cdot>s) = f q (shd s)"
    by (simp add: sscanl_shd)
next
  fix n :: "nat" and  q :: "'a" and s :: "'a stream"
  assume a2: "\<And>q s. Fin n < #s \<Longrightarrow> snth n (sscanl f q\<cdot>s) = sscanl_nth n f q s"
  assume a3: "Fin (Suc n) < #s"
  thus "snth (Suc n) (sscanl f q\<cdot>s) = sscanl_nth n f (f q (shd s)) (srt\<cdot>s)"
    by (metis a2 a3 leI not_less slen_rt_ile_eq snth_rt sscanl_srt)
qed

lemma sscan_ntimes_loop:
  assumes "\<And>r. sscanl f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanl f state\<cdot>r)" 
  shows "sscanl f state\<cdot>(sntimes n s) = sntimes n out"
  using assms
  by (induction n, simp_all)

lemma sscanl_inftimes_loop:
  assumes "\<And>r. sscanl f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanl f state\<cdot>r)"
  shows "sscanl f state\<cdot>(sinftimes s) = sinftimes out"
  using assms
  by (metis rek2sinftimes sinftimes_unfold slen_empty_eq sscanl_empty fair_sscanl strict_icycle) 


text \<open>Each element of @{term sValues} of @{term sscanl} is in the range of f\<close>
lemma sscanl_sValues: "sValues\<cdot>(sscanl f i\<cdot>s) \<subseteq> {f i s | i s. True}"
  apply (induction s rule: ind, simp_all)
  apply (rename_tac a s)
  apply (rule conjI)
  apply auto[2]
  apply (simp add: sValues_def2)
  apply (erule exE)
  apply (rename_tac n)
  apply (case_tac "n > 0")
  apply (rule_tac x = "snth (n - 1) (sscanl f (f i a)\<cdot>s)" in exI)
  apply (rule_tac x = "snth n s" in exI)
  apply (metis (no_types, lifting) Suc_pred' sscanl_snth)
  apply (rule_tac x = "f i a" in exI)
  apply (rule_tac x = "shd s" in exI)
  by (metis empty_is_shortest gr0I snth_shd sscanl_shd)

end