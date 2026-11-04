theory StreamWhile
imports Stream StreamFoot
begin

text \<open>@{term stakewhile}: Take the first elements of a stream as
  long as the given function evaluates to \<open>true\<close>.\<close>
definition stakewhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"stakewhile f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. if (f a) then \<up>a \<Zcat> h\<cdot>(srt\<cdot>s) else \<epsilon>))"


text \<open>@{term sdropwhile}: Drop the first elements of a stream as
  long as the given function evaluates to \<open>true\<close>.\<close>
definition sdropwhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"sdropwhile f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then h\<cdot>(srt\<cdot>s) else s))"


text \<open>The following two functions are "delayed" variants
  of @{term stakewhile} and @{term sdropwhile}.\<close>

text \<open>@{term stwbl}: Take while predicate holds but also keep
  first element violating condition.\<close>
definition stwbl      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"stwbl f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then \<up>a \<Zcat>  h\<cdot>(srt\<cdot>s) else \<up>a))"


text \<open>@{term srtdw}: Rest (\<open>srt\<close>) of stream after dropwhile.\<close>
definition srtdw      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"srtdw f \<equiv> \<Lambda> x. srt\<cdot>(sdropwhile f\<cdot>x)"


text \<open>@{term srcdups}: Remove successive duplicate values from stream.\<close>
definition srcdups    :: "'a stream \<rightarrow> 'a stream" where
"srcdups \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                        \<up>a \<Zcat>  h\<cdot>(sdropwhile (\<lambda> z. z = a)\<cdot>(srt\<cdot>s))))"



subsection \<open>@{term stakewhile}\<close>

text \<open>basic properties of @{term stakewhile}\<close>

lemma stakewhile_cont:"cont(\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. if (f a) 
                                  then \<up>a \<Zcat> h\<cdot>(srt\<cdot>s) else \<epsilon>))"
  by(intro cont2cont)

lemma strict_stakewhile[simp]: "stakewhile f\<cdot>\<epsilon> = \<epsilon>"
by (subst stakewhile_def [THEN fix_eq2], simp)

lemma stakewhile_t[simp]: "f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> stakewhile f\<cdot>s"
by (subst stakewhile_def [THEN fix_eq2], simp)

lemma stakewhile_f[simp]: "\<not>f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a \<Zcat> s) = \<epsilon>"
by (subst stakewhile_def [THEN fix_eq2], simp)

lemma stakewhile_in_sup[simp]: "f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a) = \<up>a"
by (subst stakewhile_def [THEN fix_eq2], simp)

lemma stakewhile_notin_sup [simp]: "\<not>f a \<Longrightarrow> stakewhile f\<cdot>(\<up>a) = \<epsilon>"
by (subst stakewhile_def [THEN fix_eq2], simp)

lemma stakewhile_less [simp]: "#(stakewhile f\<cdot>s)\<le>#s"
apply(rule ind [of _ s], auto)
apply (metis (mono_tags, lifting) admI inf_chainl4 inf_ub l42)
  by (metis bot_is_0 lnle_def lnsuc_lnle_emb minimal slen_empty_eq slen_scons stakewhile_f stakewhile_t)

lemma stakewhile_slen[simp]: "\<not>f (snth n s) \<Longrightarrow> #(stakewhile f\<cdot>s)\<le>Fin n"
apply(induction n arbitrary: s)
apply (metis Fin_02bot lnat_po_eq_conv lnzero_def sdrop_0 slen_empty_eq snth_def stakewhile_f strict_stakewhile surj_scons)
apply(case_tac s rule: scases;simp)
by(case_tac "f a";simp)

lemma stakewhile_sinf[simp]: "stakewhile (\<lambda>a. a \<noteq> x)\<cdot>\<up>x\<^sup>\<infinity> = \<epsilon>"
by (metis (full_types)sinftimes_unfold stakewhile_f)

lemma stakewhile_below[simp]: "stakewhile f\<cdot>s \<sqsubseteq> s"
apply(induction s rule: ind)
apply(simp; fail)+
by (metis minimal monofun_cfun_arg stakewhile_f stakewhile_t)

lemma stakewhile_id_snth: assumes "stakewhile f\<cdot>s = s" and "Fin n < #s"
shows "f (snth n s)"
by (metis Fin_leq_Suc_leq assms(1) assms(2) less2eq less2lnleD lnless_def stakewhile_slen)

lemma stakewhile_snth: assumes  "Fin n < #(stakewhile f\<cdot>s)"
shows "f (snth n s)"
by (meson assms not_less stakewhile_slen)

lemma stakewhile_notin: 
  shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> #(stakewhile f\<cdot>s) = Fin n \<Longrightarrow> \<not> f (snth n s)"
  apply(induction n arbitrary:s)
  apply (metis Fin_02bot lnat.con_rews slen_scons snth_shd stakewhile_t surj_scons)
  apply(rule_tac x="s" in scases;simp)
  by (metis Fin_Suc empty_is_shortest inject_lnsuc ln_less not_le_imp_less notinfI3 slen_scons stakewhile_f stakewhile_t)

lemma stakewhile_dom[simp]:assumes "\<not>f a"
  shows "a\<notin>sValues\<cdot>(stakewhile f\<cdot>s)"
  apply(auto simp add: sValues_def2)[1]
  by (metis assms snth_less stakewhile_below stakewhile_snth)

lemma stakewhile_finite_below: 
shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> s\<sqsubseteq>s' \<Longrightarrow> stakewhile f\<cdot>s = stakewhile f\<cdot>s'"
apply(induction s arbitrary: s')
    apply simp+
  apply(case_tac "f a"; simp)
  apply (metis less_fst_sconsD stakewhile_t)
  using less_fst_sconsD stakewhile_f by blast

lemma stakewhile_noteq[simp]: assumes "\<not>f (snth n s)" and "Fin n < #s"
  shows "stakewhile f\<cdot>s \<noteq> s"
proof (rule ccontr)
  assume "\<not> stakewhile f\<cdot>s \<noteq> s"
  hence "sValues\<cdot>(stakewhile f\<cdot>s) = sValues\<cdot>s" by simp
  hence "(snth n s)\<in>sValues\<cdot>(stakewhile f\<cdot>s)" by (simp add: assms(2) snth2sValues)
  thus False by (simp add: assms(1)) 
qed

text \<open>If @{term "stakewhile (\<lambda>p. p = t)"} returns an infinite stream, all prefixes
  of the original stream only consist of "@{term t}"s\<close>
lemma stakewhile_sinftimes_lemma: 
  "\<forall>z. #(stakewhile (\<lambda>p. p = t)\<cdot>z) = \<infinity> \<longrightarrow> stake n\<cdot>z = stake n\<cdot>(sinftimes (\<up>t))"
apply (induct_tac n, auto)
apply (subst sinftimes_unfold, simp)
apply (rule_tac x=z in scases, auto)
by (case_tac "a=t", auto)

text \<open>If @{term "stakewhile (\<lambda>p. p = t)"} returns an infinite stream, the original stream
  is an infinite "@{term t}"-stream\<close>
lemma stakewhile_sinftimesup: 
  "#(stakewhile (\<lambda>p. p = t)\<cdot>z) = \<infinity> \<Longrightarrow> z = sinftimes (\<up>t)"
apply (rule stream.take_lemma)
by (rule stakewhile_sinftimes_lemma [rule_format])

subsection \<open>@{term stwbl}\<close>

text \<open>basic properties for @{term stwbl}\<close>

lemma stwbl_cont[simp]:"cont(\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a.
                          if (f a) then \<up>a \<Zcat>  h\<cdot>(srt\<cdot>s) else \<up>a))"
  by(intro cont2cont)

lemma strict_stwbl[simp]: "stwbl f\<cdot>\<epsilon> = \<epsilon>"
by (subst stwbl_def [THEN fix_eq2], simp)

lemma stwbl_t[simp]: "f a \<Longrightarrow> stwbl f\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> stwbl f\<cdot>s"
by (subst stwbl_def [THEN fix_eq2], simp)

lemma stwbl_f[simp]: "\<not> f a \<Longrightarrow> stwbl f\<cdot>(\<up>a \<Zcat> s) = \<up>a"
by (subst stwbl_def [THEN fix_eq2], simp)

lemma stwbl_notEps: "s\<noteq>\<epsilon> \<Longrightarrow> (stwbl f\<cdot>s)\<noteq>\<epsilon>"
by (metis lnat.con_rews lnzero_def sconc_snd_empty slen_scons slen_zero stwbl_f stwbl_t surj_scons)

lemma stwbl_eps: "stwbl f\<cdot>s = \<epsilon> \<longleftrightarrow> s=\<epsilon>"
using strict_stwbl stwbl_notEps by blast

lemma stwbl2stbl[simp]: "stwbl f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s"
  apply(rule ind [of _s])
    apply simp_all
  by (metis sconc_snd_empty stwbl_f stwbl_t)


lemma stwbl_conc[simp]: "b\<in>sValues\<cdot>ts \<Longrightarrow>
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts \<Zcat> xs)) =
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(ts))"
  apply(induction ts rule: ind)
    apply(rule adm_imp)
     apply (simp; fail)
    apply(rule admI)
    apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf stwbl2stbl)
   apply simp+
  by (metis (full_types, lifting) assoc_sconc stwbl_f stwbl_t)

subsection \<open>@{term sdropwhile}\<close>

text \<open>basic properties for @{term sdropwhile}\<close>

lemma sdropwhile_cont[simp]:"cont(\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a.
                          if (f a) then h\<cdot>(srt\<cdot>s) else s))"
  by(intro cont2cont)

lemma strict_sdropwhile[simp]: "sdropwhile f\<cdot>\<epsilon> = \<epsilon>"
by (subst sdropwhile_def [THEN fix_eq2], simp)

lemma sdropwhile_t[simp]: "f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a \<Zcat> s) = sdropwhile f\<cdot>s"
by (subst sdropwhile_def [THEN fix_eq2], simp)

lemma sdropwhile_f[simp]: "\<not>f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> s"
by (subst sdropwhile_def [THEN fix_eq2], simp)

lemma sdropwhile_in_sup [simp]: "f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a) = \<epsilon>"
by (subst sdropwhile_def [THEN fix_eq2], simp)

lemma sdropwhile_notin_sup  [simp]: "\<not>f a \<Longrightarrow> sdropwhile f\<cdot>(\<up>a) = \<up>a"
by (subst sdropwhile_def [THEN fix_eq2], simp)

lemma sdropwhile_sconc:
  assumes "\<forall>n. Fin n < #s1 \<longrightarrow> f (snth n s1)"
    and "#s1 < \<infinity>"
  shows "sdropwhile f\<cdot>(s1 \<Zcat> s2) = sdropwhile f\<cdot>s2"
proof-
  obtain n where n_def: "#s1 = Fin n"
    using assms(2) lnat_well_h2 by blast
  show ?thesis
    using assms
  proof (induction s1 arbitrary: s2 rule: finind [where n="n"])
    case 1
    then show ?case
      by (simp add: n_def)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 a s)
    then show ?case
      apply (cases "f a")
      apply (metis Fin_Suc Groups.add_ac(2) assoc_sconc inf_ub leD leI lnsuc_lnle_emb order.not_eq_order_implies_strict sconc_slen2 sdropwhile_t slen_lnsuc slen_sconc_snd_inf snth_scons)
      by (metis Fin_02bot gr_0 lnzero_def shd1 slen_scons snth_shd)
  qed
qed


lemma sdropwhile_sValues: "sValues\<cdot>(sdropwhile f\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply (induction s rule: ind, simp_all)
  apply (rename_tac a s)
  apply (case_tac "f a")
  by (rule subset_insertI2, simp_all)

lemma sdropwhile_dropfst: assumes"\<And>x. x\<in> sValues\<cdot>s1 \<Longrightarrow> P x"
  and "#s1<\<infinity>"
shows"sdropwhile P \<cdot>(s1 \<Zcat> s2) = sdropwhile P\<cdot>s2"
  apply(rule sdropwhile_sconc,simp_all add: assms)
  using assms(1) sValues_def2 by auto

lemma sdropwhile_dropstream: assumes"\<And>x. x\<in> sValues\<cdot>s \<Longrightarrow> (P x)"
  shows"sdropwhile P \<cdot>(s) = \<epsilon>"
  using assms apply(induction s,simp_all)
  apply(rule adm_imp)
  apply(auto)[2]
  apply(rule adm_upward)
  using sValues_prefix by blast


text \<open>special cases of @{term sfilter} after @{term sdropwhile}\<close>


text \<open>Construct @{term stwbl} from @{term stakewhile}, @{term stake} and @{term sdropwhile}\<close>
lemma stwbl_stakewhile: "stwbl f\<cdot>s = stakewhile f\<cdot>s \<Zcat> (stake (Suc 0)\<cdot>(sdropwhile f\<cdot>s))"
apply (rule stream.take_lemma)
apply (rule_tac x="s" in spec)
apply (induct_tac n, simp+)
apply (rule allI)
apply (rule_tac x="x" in scases, simp+)
by (case_tac "f a", simp+)


lemma stwbl_fin [simp]: assumes "a\<in>sValues\<cdot>s" and "\<not> f a"
  shows "#(stwbl f\<cdot>s) < \<infinity>"
by (metis assms(1) assms(2) inf_ub lnle_conv lnless_def notinfI3 sconc_slen sValues2snth stakewhile_slen stwbl_stakewhile ub_slen_stake)


text \<open>Constructing @{term sdropwhile} from @{term stakewhile} and @{term sdrop}\<close>
lemma stakewhile_sdropwhilel1:
  "\<forall>x. #(stakewhile f\<cdot>x) = Fin n \<longrightarrow> sdropwhile f\<cdot>x = sdrop n\<cdot>x"  
apply (induct_tac n, auto)
apply (rule_tac x=x in scases, auto)
apply (case_tac "f a", auto)
apply (rule_tac x=x in scases, auto)
by (case_tac "f a", auto)

lemma stwbl2stakewhile: assumes "a\<in>sValues\<cdot>s" and "\<not>f a"
  shows "\<exists>x. (stwbl f\<cdot>s) = stakewhile f\<cdot>s \<Zcat> \<up>x" 
proof -
  have "#(stwbl f\<cdot>s) < \<infinity>" using assms(1) assms(2) snth2sValues stwbl_fin by blast
  hence "stwbl f\<cdot>s \<noteq> \<epsilon>" by (metis assms(1) assms(2) stakewhile_dom strict_stakewhile stwbl_notEps) 
  thus ?thesis
  proof -
    obtain nn :: nat where
      f1: "stakewhile f\<cdot>s = stake nn\<cdot>s \<and> #(stakewhile f\<cdot>s) = Fin nn"
      by (metis (no_types) \<open>\<not> f a\<close> \<open>a \<in> sValues\<cdot>s\<close> approxl2 stakewhile_below stakewhile_dom)
    have f2: "s = stake nn\<cdot>s \<Zcat> sdrop nn\<cdot>s"
      by (metis split_streaml1)
    have "sdropwhile f\<cdot>s = sdrop nn\<cdot>s"
      using f1 stakewhile_sdropwhilel1 by blast
    then show ?thesis
      using f2 f1 by (metis (no_types) \<open>\<not> f a\<close> \<open>a \<in> sValues\<cdot>s\<close> sconc_snd_empty stake2shd stakewhile_dom stwbl_stakewhile)
  qed 
qed

text \<open>@{term sdropwhile} is idempotent\<close>
lemma sdropwhile_idem: "sdropwhile f\<cdot>(sdropwhile f\<cdot>x) = sdropwhile f\<cdot>x"
apply (rule ind [of _ x], auto)
by (case_tac "f a", auto)

text \<open>@{term stakewhile} after @{term sdropwhile} gives the empty stream\<close>
lemma tdw[simp]: "stakewhile f\<cdot>(sdropwhile f\<cdot>s) = \<epsilon>"
apply (rule ind [of _ s], auto)
by (case_tac "f a", auto)

lemma stakewhileDropwhile: "stakewhile f\<cdot>s \<Zcat> (sdropwhile f\<cdot>s) = s "
apply(rule ind [of _s])
apply (rule admI)
apply (metis (no_types, lifting) approxl2 inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf split_streaml1 stakewhile_below stakewhile_sdropwhilel1)
apply (simp;fail)
by (metis assoc_sconc sconc_fst_empty sdropwhile_f sdropwhile_t stakewhile_t tdw)

text \<open>For the head of @{term "sdropwhile f\<cdot>x"}, @{term f} does not hold\<close>
lemma sdropwhile_resup: "sdropwhile f\<cdot>x = \<up>a \<Zcat> s \<Longrightarrow> \<not> f a"
apply (subgoal_tac "sdropwhile f\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> s")
apply (case_tac "f a", auto)
apply rotate_tac
apply (drule cfun_arg_cong [of _ _ "stakewhile f"], simp)
apply (drule sym, simp)
by (rule sdropwhile_idem)

lemma stakewhileDropwhile2: "y = stakewhile f\<cdot>y \<Zcat> (sdropwhile f\<cdot>y)"
  by (simp add: stakewhileDropwhile)

lemma dropwhile_sconc_empty:
  assumes "#sa = Fin k"
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>sa = \<epsilon> \<Longrightarrow>
         sdropwhile (\<lambda>x. x = a)\<cdot>(sa \<Zcat> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
  apply (induction sa rule: finind)
  using assms apply simp
  apply simp
  by (case_tac "a=aa"; simp)

lemma sdropwhile_eq_const_stream: "sdropwhile (\<lambda>x. x = a)\<cdot> ((\<up>a)\<^sup>\<infinity>) = \<epsilon>"
  by (metis (full_types) sdropwhile_dropstream sinf_sValues stakewhile_dom stakewhile_in_sup)

lemma sdropwhile_takewhile_neq_eps_neq_inf:
  assumes "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon>" 
  shows "#(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity>"
  using assms 
  by (metis eq_less_and_fst_inf sdropwhile_dropstream stakewhile_below stakewhile_dom)

lemma sdropwhile_neq_eps_sdrop: "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>n .sdropwhile (\<lambda>x. x = a)\<cdot>s = sdrop n\<cdot>s"
  using sdropwhile_takewhile_neq_eps_neq_inf 
  by (metis LNat.LNat.lnat.exhaust stakewhile_sdropwhilel1)




subsection \<open>@{term srtdw}\<close>

text \<open>basic properties of @{term srtdw}\<close>

lemma srtdw_cont[simp]:"cont(\<lambda> x. srt\<cdot>(sdropwhile f\<cdot>x))"
  by(intro cont2cont)

lemma srtdw_eps [simp]: "srtdw f\<cdot>\<epsilon> = \<epsilon>"
by (simp add: srtdw_def)

lemma srtdw_sup[simp]: "srtdw f\<cdot>(\<up>a) = \<epsilon>"
apply (simp add: srtdw_def)
by (case_tac "f a", auto)

lemma srtdw_in_sup[simp]: "f a \<Longrightarrow> srtdw f\<cdot>(\<up>a\<Zcat>as) = srtdw f\<cdot>as"
by (auto simp add: srtdw_def)

lemma srtdw_notin_sup[simp]: "\<not> f a \<Longrightarrow> srtdw f\<cdot>(\<up>a\<Zcat>as) = as"
by (simp add: srtdw_def)

text \<open>streams can be split by @{term stwbl} and @{term srtdw}\<close>
lemma stwbl_srtdw: "stwbl f\<cdot>s \<Zcat> srtdw f\<cdot>s = s"
apply (rule stream.take_lemma)
apply (rule_tac x="s" in spec)
apply (induct_tac n, simp+)
apply (rule allI)
apply (rule_tac x="x" in scases, simp+)
by (case_tac "f a", simp+)

lemma slen_srtdw: "#(srtdw f\<cdot>x) \<le> #x"
  apply (induction x rule:ind)
  apply(simp add: len_stream_def)
apply (subst lnle_conv [THEN sym], simp del: lnle_conv, simp)
apply (case_tac "f a", simp+)
by (rule trans_lnle, simp+)

lemma stwbl_below [simp]: "stwbl f\<cdot>s \<sqsubseteq> s"
by (metis (no_types) minimal monofun_cfun_arg sconc_snd_empty stwbl_srtdw)

lemma srtdw_stwbl [simp]: "srtdw f\<cdot> (stwbl f\<cdot>s) = \<epsilon>" (is "?F s")
proof(rule ind [of _s ])
  show "adm ?F" by simp
  show "?F \<epsilon>" by simp
  fix a
  fix s
  assume IH: "?F s"
  thus "?F (\<up>a \<Zcat> s)" 
  proof (cases "f a")
    case True thus ?thesis by (simp add: IH)
  next
    case False thus ?thesis by simp
  qed
qed

lemma stwbl_eq_dw: assumes "srtdw P\<cdot>x \<noteq> \<epsilon>" and "x\<sqsubseteq>y"
  shows "stwbl P\<cdot>x = stwbl P\<cdot>y"
  using assms apply(induction x arbitrary: y)
  apply simp+
  by (metis (full_types) less_fst_sconsD sconc_snd_empty srtdw_stwbl stwbl_f stwbl_srtdw stwbl_t)

lemma stakewhile_stwbl [simp]: "stakewhile f\<cdot>(stwbl f\<cdot>s) = stakewhile f\<cdot>s"
proof -
  have "\<And>s sa. (s::'a stream) \<sqsubseteq> s \<Zcat> sa"
    by simp
  then have "stakewhile f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s \<longrightarrow> stakewhile f\<cdot>(stwbl f\<cdot>s) = stakewhile f\<cdot>s"
    by (metis (no_types) below_antisym monofun_cfun_arg stwbl_below stwbl_stakewhile)
  then show ?thesis
    using stakewhile_finite_below stwbl_below by blast
qed

lemma stakewhile_below_stwbl: "stakewhile P\<cdot>s \<sqsubseteq> stwbl P\<cdot>s"
  by (metis stakewhile_below stakewhile_stwbl)


lemma stwbl_id_help:
  shows "(\<forall>a\<in>sValues\<cdot>s. f a) \<longrightarrow> stwbl f\<cdot>s = s"
  apply (rule ind [of _s])
    apply(rule adm_imp)
     apply(rule admI, rule ccontr)
     using sValues_chain2lub apply blast
    apply(rule admI)
    apply (metis cont2contlubE cont_Rep_cfun2 lub_eq)
   using strict_stwbl apply blast
  apply (rule impI)
  by simp

lemma stwbl_id [simp]: "(\<And> a. a\<in>sValues\<cdot>s \<Longrightarrow> f a) \<Longrightarrow> stwbl f\<cdot>s = s"
by (simp add: stwbl_id_help)


lemma srtdw_conc: "b\<in>sValues\<cdot>ts  \<Longrightarrow> (srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<Zcat> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts) \<Zcat> as"
  apply(induction ts arbitrary: as rule: ind)
  apply (rule adm_imp,simp)
  apply auto[3]
  apply(rule admI)
  apply (rule allI)
  apply (metis (no_types, lifting) approxl3 assoc_sconc is_ub_thelub)
  by(case_tac "a = b";simp)

lemma stwbl_sfoot: assumes "a\<in>sValues\<cdot>s" and "\<not>f a"
  shows "\<not> f (sfoot (stwbl f\<cdot>s))" 
proof(rule ccontr)
  assume "\<not> \<not> f (sfoot (stwbl f\<cdot>s))"
  hence "f (sfoot (stwbl f\<cdot>s))" by blast
  obtain x where x_def:"(stwbl f\<cdot>s) = stakewhile f\<cdot>s \<Zcat> \<up>x"
    using assms(1) assms(2) stwbl2stakewhile by blast
  hence "sfoot (stwbl f\<cdot>s) = x"
    using assms(1) assms(2) sfoot1 stwbl_fin by blast
  have "stakewhile f\<cdot>s \<Zcat> \<up>x \<sqsubseteq> s" by (metis stwbl_below x_def)
  have "f x"
    using \<open>f (sfoot (stwbl f\<cdot>s))\<close> \<open>sfoot (stwbl f\<cdot>s) = x\<close> by blast
  thus False
    by (metis approxl2 assms(1) assms(2) inject_sconc sconc_snd_empty sdropwhile_resup stakewhileDropwhile stakewhile_below stakewhile_dom stakewhile_stwbl x_def)
qed

subsection \<open>@{term srcdups}\<close>

text \<open>Basic simplification rules for @{term srcdups}\<close>

lemma srcdups_cont[simp]:"cont(\<lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                        \<up>a \<Zcat>  h\<cdot>(sdropwhile (\<lambda> z. z = a)\<cdot>(srt\<cdot>s))))"
  by(intro cont2cont)

lemma strict_srcdups[simp]: "srcdups\<cdot>\<epsilon> = \<epsilon>" 
by (subst srcdups_def [THEN fix_eq2], simp)

lemma srcdups_sup[simp]: "srcdups\<cdot>(\<up>a) = \<up>a"
by (subst srcdups_def [THEN fix_eq2], simp)

lemma srcdups_eq[simp]: "srcdups\<cdot>(\<up>a\<Zcat>\<up>a\<Zcat>s) = srcdups\<cdot>(\<up>a\<Zcat>s)" 
apply (subst srcdups_def [THEN fix_eq2], simp)
by (rule sym, subst srcdups_def [THEN fix_eq2], simp)

lemma srcdups_neq[simp]: 
  "a\<noteq>b \<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> \<up>b \<Zcat> s) = \<up>a \<Zcat>  srcdups\<cdot>(\<up>b \<Zcat> s)" 
  by (subst srcdups_def [THEN fix_eq2], simp)
    
lemma srcdups_slen [simp]: "#(srcdups\<cdot>s) \<le> #s"
  apply (rule ind [of _ s])
  apply (simp_all)
  apply (metis (mono_tags, lifting) admI inf_chainl4 inf_ub l42)
  apply (rule_tac x=s in scases, simp_all)
  apply (case_tac "a = aa", simp_all)
  using less_lnsuc order.trans by blast
    
lemma srcdups_eq2:"a=b \<Longrightarrow> srcdups\<cdot>(\<up>a\<Zcat>\<up>b\<Zcat>s) = srcdups\<cdot>(\<up>b\<Zcat>s)"
  by simp
    
lemma srcdups_ex:"\<exists>y. srcdups\<cdot>(\<up>a\<Zcat>s) = \<up>a\<Zcat>y"
  by(subst srcdups_def [THEN fix_eq2], auto)
    
lemma srcdups_shd[simp]:"shd (srcdups\<cdot>(\<up>a\<Zcat>s)) = a"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups_srt:"srt\<cdot>(srcdups\<cdot>(\<up>a\<Zcat>s)) = (srcdups\<cdot>(sdropwhile (\<lambda>z. z = a)\<cdot>s))"
  by(subst srcdups_def [THEN fix_eq2], auto)
    
lemma srcdups_shd2[simp]:"s\<noteq>\<epsilon> \<Longrightarrow> shd (srcdups\<cdot>s) = shd s"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups_srt2:"s\<noteq>\<epsilon> \<Longrightarrow> srt\<cdot>(srcdups\<cdot>s) = (srcdups\<cdot>(sdropwhile (\<lambda>z. z = shd s)\<cdot>(srt\<cdot>s)))"
  by(subst srcdups_def [THEN fix_eq2],auto)

lemma srcdups_imposs_h:"Fin 1 < #(srcdups\<cdot>s) \<Longrightarrow> shd(srcdups\<cdot>s)\<noteq>shd(srt\<cdot>(srcdups\<cdot>s))"
  apply (cases "s=\<epsilon>")
  using empty_is_shortest apply fastforce
  apply (subst srcdups_srt2,auto)
  apply (subgoal_tac "srcdups\<cdot>(sdropwhile (\<lambda>z. z = shd s)\<cdot>(srt\<cdot>s))\<noteq>\<epsilon>")
  apply (metis (mono_tags, lifting) sdropwhile_resup srcdups_shd2 strict_srcdups surj_scons)
proof -
  assume a1: "s \<noteq> \<epsilon>"
  assume a2: "Fin 1 < #(srcdups\<cdot>s)"
  have f1:"Fin 0 = 0"
    using Fin_02bot bot_is_0 by presburger
  then have "lnsuc\<cdot>0 = Fin (Suc 0)"
    by (metis Fin_Suc)
  then show "srcdups\<cdot> (sdropwhile (\<lambda>a. a = shd s)\<cdot>(srt\<cdot>s)) \<noteq> \<epsilon>"
    using a2 a1 f1
    by (metis Suc_leI less2nat not_le not_one_le_zero srcdups_srt2 srt_decrements_length slen_zero zero_le_one)
qed

lemma srcdups_imposs:"srcdups\<cdot>(\<up>a \<Zcat> s) \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> y"
  apply(cases "#(srcdups\<cdot>(\<up>a \<Zcat>s)) < Fin 1 ")  
  apply (metis One_nat_def bot_is_0 lnat.con_rews neq02Suclnle not_less slen_scons)
  apply(insert srcdups_imposs_h[of "\<up>a\<Zcat> s"])
  by (metis Fin_02bot Fin_Suc One_nat_def lnat.con_rews lnat.sel_rews(2) lscons_conv neq_iff shd1 
      slen_scons stream.sel_rews(5) up_defined)  
  
lemma srcdupsimposs: "srcdups\<cdot>(\<up>a \<Zcat> s) \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> srcdups\<cdot>s"
  by (simp add: srcdups_imposs)
   
lemma srcdupsimposs2_h2:"\<forall>x. srcdups\<cdot>(\<up>a \<Zcat> s)\<noteq> \<up>a \<Zcat> \<up>a \<Zcat> x"
  by (simp add: srcdups_imposs)
 
lemma srcdupsimposs2: "srcdups\<cdot>(\<up>a \<Zcat> s) \<noteq> \<up>a \<Zcat> \<up>a \<Zcat> s"
  by(simp add: srcdups_imposs) 
    
lemma srcdups_anotb_h:"srcdups\<cdot>(\<up>a\<Zcat>\<up>b) = \<up>a \<Zcat> \<up>b \<Longrightarrow> a \<noteq> b"
  by (metis sconc_snd_empty srcdups_imposs)
  
lemma srcdups_anotb:"srcdups\<cdot>(\<up>a \<Zcat> \<up>b \<Zcat> s) = \<up>a \<Zcat> \<up>b \<Zcat> s \<Longrightarrow> a\<noteq> b"
  using srcdupsimposs2_h2 by auto

lemma srcdups2srcdups: "srcdups\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>s"
proof(induction rule: ind [of _ s])
  case 1
  then show ?case 
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 a s)
  have f1:"a = shd s \<Longrightarrow> s\<noteq>\<epsilon>\<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = srcdups\<cdot>s"
    using srcdups_eq[of "shd s" "srt\<cdot>s"] surj_scons[of s] by auto
  have f2:"a=shd s \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s)) = srcdups\<cdot>(\<up>a \<Zcat> s)"
    using f1 "3.IH" by auto
  moreover have"a\<noteq>shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a\<Zcat>srcdups\<cdot>s"
    by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
  ultimately have f3:"a\<noteq> shd s \<Longrightarrow>srcdups\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s)) = srcdups\<cdot>(\<up>a \<Zcat> s)"
  proof -
    assume a1: "a \<noteq> shd s"
    then have f2: "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s"
      by (metis \<open>a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s\<close>)
    obtain ss :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      f3: "\<forall>a s. srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> ss s a"
      by (meson srcdups_ex)
    then have f4: "\<up>(shd s) \<Zcat> srt\<cdot>s = s \<longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> \<up>(shd s) \<Zcat> ss (srt\<cdot>s) (shd s)"
      using f2 by metis
    have f5: "\<up>(shd s) \<Zcat> srt\<cdot>s = s \<longrightarrow> srcdups\<cdot>(\<up>(shd s) \<Zcat> ss (srt\<cdot>s) (shd s)) = srcdups\<cdot>s"
      using f3 by (metis "3.IH")
    { assume "\<up>a \<Zcat> s \<noteq> srcdups\<cdot>(\<up>a \<Zcat> s)"
      then have "s \<noteq> \<epsilon>"
        by force
      then have ?thesis
        using f5 f4 f2 a1 by (simp add: surj_scons) }
    then show ?thesis
      by fastforce
  qed
  then show ?case
    using f2 by fastforce
qed


lemma srcdups_prefix_neq_h:assumes"s1 \<noteq> s2"
  shows "\<up>a \<Zcat>s1 \<noteq> \<up>b \<Zcat> s2"
  using assms inject_scons by auto

lemma srcdups_prefix_neq:"x \<sqsubseteq> y \<Longrightarrow> srcdups\<cdot>x \<noteq>x \<Longrightarrow> srcdups\<cdot>y \<noteq> y"
proof(induction arbitrary: y rule: ind [of _ x])
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case
      by simp
  next
    case (3 a s)
    have f1:"\<And>a s. s\<noteq>\<epsilon> \<Longrightarrow>  a=shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = srcdups\<cdot>s"
      by (metis srcdups_eq surj_scons)
    have f2:"\<And>a s. a\<noteq>shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s"
      by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    then have f3:"a\<noteq>shd s\<Longrightarrow> srcdups\<cdot>s \<noteq> s"
      using "3.prems" by metis
    have f4:"s \<sqsubseteq> srt\<cdot>y \<and> shd y = a"
      using less_all_sconsD
      by (metis "3.prems"(1) "3.prems"(2) bottomI strict_srcdups surj_scons)
    then show ?case
      apply(cases y rule: scases;simp)
      using "3.prems"(1) apply auto[1]
      apply(case_tac "shd sa = a")
      apply (metis "3.prems"(2) minimal po_eq_conv srcdups_anotb surj_scons)
      apply(simp add: f2) 
      apply(rule srcdups_prefix_neq_h)
      apply(rule "3.IH")
      apply blast
      apply(case_tac s rule:scases;simp)
      apply(case_tac "a \<noteq> shd s")
      using "3.prems"(2) apply simp_all
      using below_shd by fastforce
qed

lemma srcdups_smap_adm [simp]: 
  "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>a)) = smap f\<cdot>(srcdups\<cdot>a) 
    \<longrightarrow> srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
  apply (rule adm_imp, auto)
  apply(rule adm_upward; rule ccontr)
  using srcdups_prefix_neq
  by (metis monofun_cfun_arg)
    
lemma srcdups_smap_com_h:"s\<noteq>\<epsilon> \<Longrightarrow> a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s)) \<Longrightarrow>f (shd s) \<noteq> f a"
  apply(cases "shd(srt\<cdot>s) \<noteq> shd s")
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply (metis smap_scons srcdups_ex srcdupsimposs2_h2)
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply(insert srcdups_ex[of "shd s" "srt\<cdot>s"],auto)
  by (simp add: srcdupsimposs2_h2)

lemma srcdups_smap_com:
  shows "srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>s)) = smap f\<cdot>(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>s)= smap f\<cdot>(srcdups\<cdot>s)"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    have s_eps: "s = \<bottom> \<Longrightarrow>  srcdups\<cdot>(\<up>(f a) \<Zcat> smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s))" by simp
    hence f1: "shd s = a \<Longrightarrow> ?case"  
      by (metis "3.IH" "3.prems" smap_scons srcdups_eq surj_scons)
    have h1: "s\<noteq>\<bottom> \<Longrightarrow> s = (\<up>(shd s) \<Zcat> srt\<cdot>s)" by (simp add: surj_scons)
    have h2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(\<up>a \<Zcat> (\<up>(shd s) \<Zcat> srt\<cdot>s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat>  (\<up>(shd s) \<Zcat> srt\<cdot>s)))"
    proof -
      assume a1: "f (shd s) \<noteq> f a"
      assume a2: "s \<noteq> \<epsilon>"
      assume a3: "shd s \<noteq> a"
      have f4: "s = \<up>(shd s) \<Zcat> srt\<cdot>s"
        using a2 by (metis h1)
      obtain ss :: "'b stream \<Rightarrow> 'b \<Rightarrow> 'b stream" where
        f5: "\<forall>b s. srcdups\<cdot>(\<up>b \<Zcat> s) = \<up>b \<Zcat> ss s b"
        by (meson srcdups_ex)
      then have f6: "\<up>(shd s) \<Zcat> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>s"
        using f4 by metis
      have f7: "srcdups\<cdot> (\<up>(f a) \<Zcat> \<up>(f (shd s)) \<Zcat> smap f\<cdot> (ss (srt\<cdot>s) (shd s))) = \<up>(f a) \<Zcat> srcdups\<cdot> (\<up>(f (shd s)) \<Zcat> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using a1 by auto
      have f8: "\<up>a \<Zcat> \<up>(shd s) \<Zcat> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>(\<up>a \<Zcat> \<up>(shd s) \<Zcat> srt\<cdot>s)"
        using f5 a3 by (metis (no_types) srcdups_neq)
      then have f9: "\<up>(f a) \<Zcat> \<up>(f (shd s)) \<Zcat> smap f\<cdot> (ss (srt\<cdot>s) (shd s)) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s))"
        using f4 by (metis (no_types) smap_scons)
      then obtain ssa :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
        f10: "\<up>(f a) \<Zcat> ssa (\<up>(f (shd s)) \<Zcat> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s)))"
        by (simp add: "3.prems")
      then have f11: "\<up>(f a) \<Zcat> ssa (\<up>(f (shd s)) \<Zcat> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot> (\<up>(f a) \<Zcat> \<up>(f (shd s)) \<Zcat> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using f9 by presburger
      have "\<up>(f a) \<Zcat> ssa (\<up>(f (shd s)) \<Zcat> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = \<up>(f a) \<Zcat> smap f\<cdot>(srcdups\<cdot>s)"
        using f10 f8 f6 f4 by (metis (no_types) "3.prems" smap_scons)
      then have "srcdups\<cdot>(smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>s)"
        using f11 f7 f6 by (metis (no_types) "3.IH" inject_scons smap_scons)
      then have "srcdups\<cdot> (smap f\<cdot>(\<up>a \<Zcat> \<up>(shd s) \<Zcat> srt\<cdot>s)) = smap f\<cdot> (\<up>a \<Zcat> \<up>(shd s) \<Zcat> ss (srt\<cdot>s) (shd s))"
        using f6 f4 a1 by (metis (no_types) smap_scons srcdups_neq)
      then show ?thesis
        using f8 by presburger
    qed
    have f2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> ?case"
      using h1 h2 by auto
    have f3: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) = f a \<Longrightarrow> ?case"
      by (simp add: "3.prems" srcdups_smap_com_h)
    then show ?case using f1 f2 by fastforce
  qed

lemma srcdups_nbot: "s\<noteq>\<bottom>\<Longrightarrow>srcdups\<cdot>s \<noteq> \<bottom>"
  by (metis lscons_conv srcdups_ex stream.con_rews(2) surj_scons)
  
lemma srcdups_fin: assumes "#(srcdups\<cdot>s)<\<infinity>" and "#s=\<infinity>"
  obtains x where "srcdups\<cdot>x = srcdups\<cdot>s" and "x\<sqsubseteq>s" and "#x < \<infinity>"
proof -
  obtain n where "srcdups\<cdot>(stake n\<cdot>s) = srcdups\<cdot>s"
    by (metis assms(1) fun_approxl2 len_stream_def lnat_well_h2)
  thus ?thesis
    using lnless_def that by auto 
qed

lemma srcdups_step: "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x=a)\<cdot>s)"
  apply(rule ind [of _ s], simp_all)
  by (metis lscons_conv srcdups_ex srcdups_srt stream.sel_rews(5) up_defined) 

lemma snprefix: "\<not>x\<sqsubseteq>y \<Longrightarrow> lshd\<cdot>x=lshd\<cdot>y \<Longrightarrow> \<not>(srt\<cdot>x)\<sqsubseteq>(srt\<cdot>y)"
  apply auto[1]
  by (metis lshd_updis monofun_cfun_arg stream.sel_rews(2) stream.sel_rews(3) sup'_def surj_scons)

lemma srcdups_consec_noteq: "Fin (Suc n) < #(srcdups\<cdot>xs) \<Longrightarrow> snth n (srcdups\<cdot>xs) \<noteq> snth (Suc n) (srcdups\<cdot>xs)"
proof
  fix n :: nat
  assume "Fin (Suc n) < #(srcdups\<cdot>xs)" and "snth n (srcdups\<cdot>xs) = snth (Suc n) (srcdups\<cdot>xs)"
  then obtain a s where "sdrop n\<cdot>(srcdups\<cdot>xs) = \<up>a \<Zcat> \<up>a \<Zcat> s"
    by (metis convert_inductive_asm drop_not_all sdrop_back_rt snth_def surj_scons)
  then have p: "srcdups\<cdot>(sdrop n\<cdot>(srcdups\<cdot>xs)) \<noteq> sdrop n\<cdot>(srcdups\<cdot>xs)"
    by (simp add: srcdupsimposs2_h2)
  have not_p: "srcdups\<cdot>(sdrop n\<cdot>(srcdups\<cdot>xs)) = sdrop n\<cdot>(srcdups\<cdot>xs)"
  proof -
    have "srcdups\<cdot>(sdrop n\<cdot>(srcdups\<cdot>xs)) = sdrop n\<cdot>(srcdups\<cdot>(srcdups\<cdot>xs))"
    proof (induction n)
      case 0
      then show ?case
        by simp
    next
      case (Suc n)
      then show ?case
        by (metis sdrop_back_rt srcdups2srcdups srcdups_srt2 stream.sel_rews(2))
    qed
    thus "srcdups\<cdot>(sdrop n\<cdot>(srcdups\<cdot>xs)) = sdrop n\<cdot>(srcdups\<cdot>xs)"
      by (simp add: srcdups2srcdups)
  qed
  thus "False"
    using p by auto
qed

lemma bool_stream_snth:
  fixes s t :: "bool stream" and n :: nat and a :: bool
  shows "s = \<up>a \<Zcat> t \<longrightarrow> Fin n < #(srcdups\<cdot>s) \<longrightarrow> snth n (srcdups\<cdot>s) = (even n = a)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    using convert_inductive_asm even_Suc srcdups_consec_noteq by blast
qed

lemma srcdups_snth_stake_fin: "\<And>s n. #s = Fin k \<Longrightarrow> k > (Suc n) \<Longrightarrow> snth n s \<noteq> snth (Suc n) s \<Longrightarrow> srcdups\<cdot>(stake (Suc n)\<cdot>s) \<noteq> srcdups\<cdot>s"
proof (induction k rule: less_induct)
  case (less k)
  then show ?case
  proof (cases "k \<le> Suc 0")
    case True
    then show ?thesis
      using less.prems(2) by linarith
  next
    case False
    then obtain a b t where "s = \<up>a \<Zcat> \<up>b \<Zcat> t"
      by (metis drop_not_all leI le_SucI less.prems(1) less2nat_lemma sdrop_0 sdrop_back_rt surj_scons)
    obtain l where "k = Suc l"
      using Suc_less_eq2 less.prems(2) by blast
    then have "l < k"
      by simp
    moreover have "#(\<up>b \<Zcat> t) = Fin l"
      using \<open>k = Suc l\<close> \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> less.prems(1) by auto
    then show ?thesis
    proof (cases n)
      case 0
      then have "srcdups\<cdot>(stake (Suc n)\<cdot>s) = \<up>a"
        by (simp add: \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close>)
      moreover have "srcdups\<cdot>s \<noteq> \<up>a"
      proof -
        have "snth 0 s \<noteq> snth (Suc 0) s"
          using "0" less.prems(3) by blast
        then have "a \<noteq> b"
          by (simp add: \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close>)
        then have "srcdups\<cdot>s = \<up>a \<Zcat> srcdups\<cdot>(\<up>b \<Zcat> t)"
          using \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> srcdups_neq by blast
        then show ?thesis
          using srcdups_nbot by force
      qed
      ultimately show ?thesis
        by auto
    next
      case (Suc m)
      have "Suc m < l"
        using Suc \<open>k = Suc l\<close> less.prems(2) by blast
      moreover have "snth m (\<up>b \<Zcat> t) \<noteq> snth (Suc m) (\<up>b \<Zcat> t)"
      proof -
        have "\<up>b \<Zcat> t = srt\<cdot>s"
          by (simp add: \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close>)
        then show ?thesis
          by (metis (no_types) Suc less.prems(3) sdrop_forw_rt snth_def)
      qed
      ultimately have "srcdups\<cdot>(stake (Suc m)\<cdot>(\<up>b \<Zcat> t)) \<noteq> srcdups\<cdot>(\<up>b \<Zcat> t)"
        using \<open>#(\<up>b \<Zcat> t) = Fin l\<close> \<open>l < k\<close> less.IH by blast
      then have "srcdups\<cdot>(\<up>b \<Zcat> (stake m\<cdot>t)) \<noteq> srcdups\<cdot>(\<up>b \<Zcat> t)"
        by simp
      then have "srcdups\<cdot>s \<noteq> \<up>a \<Zcat> (srcdups\<cdot>(\<up>b \<Zcat> (stake m\<cdot>t)))"
        by (metis (no_types, lifting) \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> inject_scons srcdups2srcdups srcdups_eq srcdups_neq srcdups_step)
      then show ?thesis
      proof -
        { assume "a \<noteq> b"
          then have "srcdups\<cdot>(\<up>a \<Zcat> \<up>b \<Zcat> stake m\<cdot>t) \<noteq> srcdups\<cdot>s"
            using \<open>srcdups\<cdot>s \<noteq> \<up>a \<Zcat> srcdups\<cdot>(\<up>b \<Zcat> stake m\<cdot>t)\<close> by auto
          then have ?thesis
            using Suc \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> by force }
        then show ?thesis
          using Suc \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> \<open>srcdups\<cdot>(\<up>b \<Zcat> stake m\<cdot>t) \<noteq> srcdups\<cdot>(\<up>b \<Zcat> t)\<close> by fastforce
      qed
    qed
  qed
qed

lemma srcdups_end_neq: "#s < \<infinity> \<Longrightarrow> a \<noteq> b \<Longrightarrow> srcdups\<cdot>(s \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>(s \<Zcat> \<up>a) \<Zcat> \<up>b"
proof (rule finind3 [of s], simp+)
  assume "#s < \<infinity>" and "a \<noteq> b"
  then show "srcdups\<cdot>(\<up>a \<Zcat> \<up>b) = \<up>a \<Zcat> \<up>b"
    by (metis lscons_conv srcdups_neq srcdups_step strict_sdropwhile strict_srcdups sup'_def)
next
  fix t :: "'a stream" and c :: 'a
  assume "#t < \<infinity>" and "srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>(t \<Zcat> \<up>a) \<Zcat> \<up>b"
  then have "srcdups\<cdot>(\<up>c \<Zcat> (t \<Zcat> \<up>a)) \<Zcat> \<up>b = srcdups\<cdot>(\<up>c \<Zcat> (t \<Zcat> \<up>a \<Zcat> \<up>b))"
  proof (cases "t = \<epsilon>")
    case True
    then show ?thesis
      by (metis (no_types, lifting) \<open>srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>(t \<Zcat> \<up>a) \<Zcat> \<up>b\<close> assoc_sconc inject_scons sconc_snd_empty srcdups_eq srcdups_neq)
  next
    case False
    then have not_empty: "t \<noteq> \<epsilon>"
      by simp
    then show ?thesis
    proof (cases "c = shd t")
      case True
      then show ?thesis
        by (metis False \<open>srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>(t \<Zcat> \<up>a) \<Zcat> \<up>b\<close> sconc_scons srcdups_eq surj_scons)
    next
      case False
      then have "srcdups\<cdot>(\<up>c \<Zcat> (t \<Zcat> \<up>a \<Zcat> \<up>b)) = \<up>c \<Zcat> srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>b)"
      proof -
        have "\<up>(shd t) \<Zcat> srt\<cdot>t = t"
          using not_empty surj_scons by blast
        then show ?thesis
          by (metis (no_types) False assoc_sconc srcdups_neq)
      qed
      then show ?thesis
      proof -
        have "\<up>(shd t) \<Zcat> srt\<cdot>t = t"
          by (meson not_empty surj_scons)
        then show ?thesis
          by (metis (no_types) False \<open>srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>(t \<Zcat> \<up>a) \<Zcat> \<up>b\<close> assoc_sconc srcdups_neq)
      qed
    qed
  qed
  thus "srcdups\<cdot>((\<up>c \<Zcat> t) \<Zcat> \<up>a \<Zcat> \<up>b) = srcdups\<cdot>((\<up>c \<Zcat> t) \<Zcat> \<up>a) \<Zcat> \<up>b"
    by simp
qed

lemma srcdups_end_eq: "srcdups\<cdot>(s \<Zcat> \<up>a \<Zcat> \<up>a) = srcdups\<cdot>(s \<Zcat> \<up>a)"
proof (cases "#s < \<infinity>")
  case True
  then show ?thesis
  proof (rule finind3, simp)
    show "srcdups\<cdot>(\<up>a \<Zcat> \<up>a) = \<up>a"
      by (simp add: srcdups_step)
  next
    fix t :: "'a stream" and b :: 'a
    assume "#t < \<infinity>" and "srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>a) = srcdups\<cdot>(t \<Zcat> \<up>a)"
    then show "srcdups\<cdot>((\<up>b \<Zcat> t) \<Zcat> \<up>a \<Zcat> \<up>a) = srcdups\<cdot>((\<up>b \<Zcat> t) \<Zcat> \<up>a)"
    proof (cases "t = \<epsilon>")
      case True
      then show ?thesis
        by (metis sconc_snd_empty srcdups_eq srcdups_neq)
    next
      case False
      then have 1: "t \<noteq> \<epsilon>"
        by simp
      then show ?thesis
      proof(cases "shd t = b")
        case True
        then show ?thesis
          by (metis False \<open>srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>a) = srcdups\<cdot>(t \<Zcat> \<up>a)\<close> assoc_sconc srcdups_eq surj_scons)
      next
        case False
        have "t \<noteq> \<epsilon>"
          by (simp add: "1")
        then have "srcdups\<cdot>(\<up>b \<Zcat> t \<Zcat> \<up>a \<Zcat> \<up>a) = \<up>b \<Zcat> srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>a)"
          by (metis (no_types, lifting) False assoc_sconc srcdups_neq surj_scons)
        then show ?thesis
          by (metis (no_types, lifting) "1" False \<open>srcdups\<cdot>(t \<Zcat> \<up>a \<Zcat> \<up>a) = srcdups\<cdot>(t \<Zcat> \<up>a)\<close> sconc_scons srcdups_neq surj_scons)
      qed
    qed
  qed
next
  case False
  then show ?thesis
    by (simp add: less_le)
qed

lemma srcdups_sntimes: "n > 0 \<Longrightarrow> srcdups\<cdot>(sntimes n (\<up>a)) = \<up>a"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n > 0")
    case True
    then show ?thesis
      by (metis Suc.IH gr0_implies_Suc sntimes.simps(2) srcdups_eq)
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma srcdups_sntimes_prefix: "n > 0 \<Longrightarrow> srcdups\<cdot>((sntimes n (\<up>a)) \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x=a)\<cdot>s)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n > 1")
    case True
    then obtain m where "n = Suc m" and "m > 0"
      by (metis One_nat_def Suc_lessE)
    then have "srcdups\<cdot>((sntimes (Suc n) (\<up>a)) \<Zcat> s) = srcdups\<cdot>((sntimes n (\<up>a)) \<Zcat> s)"
      by (simp add: \<open>n = Suc m\<close>)
    then show ?thesis
      using Suc.IH \<open>n = Suc m\<close> zero_less_Suc by auto 
  next
    case False
    have "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x=a)\<cdot>s)"
      using srcdups_step by blast
    moreover have "sntimes 1 (\<up>a) = \<up>a"
      by (simp add: One_nat_def)
    ultimately show ?thesis
      by (metis (no_types, lifting) False One_nat_def Suc_lessI assoc_sconc neq0_conv sntimes.simps(2) srcdups_eq)
  qed
qed



lemma srcdups_split_fin: "#s = Fin k \<Longrightarrow> Suc n < k \<Longrightarrow> snth n s \<noteq> snth (Suc n) s \<Longrightarrow> srcdups\<cdot>s = srcdups\<cdot>(stake (Suc n)\<cdot>s) \<Zcat> (srcdups\<cdot>(sdrop (Suc n)\<cdot>s))"
proof (induction k arbitrary: n s)
  case 0
  then show ?case
    by auto
next
  case (Suc k)
  then obtain a t where "s = \<up>a \<Zcat> t"
    by (metis Fin_0 Suc_neq_Zero slen_zero surj_scons)
  assume "snth n s \<noteq> snth (Suc n) s"
  then have "Suc n < Suc k"
    using Suc.prems(2) by blast
  then show ?case
  proof (cases "k > 1")
    case True
    then obtain a b t where "s = \<up>a \<Zcat> \<up>b \<Zcat> t"
    proof -
      assume a1: "\<And>a b t. s = \<up>a \<Zcat> \<up>b \<Zcat> t \<Longrightarrow> thesis"
      have "#(\<epsilon>::'a stream) = \<bottom>"
        using bot_is_0 by auto
      then show ?thesis
        using a1 by (metis Fin_Suc Suc.prems(1) True inject_lnsuc less2nat_lemma lnat.con_rews lnle_def minimal not_le srt_decrements_length surj_scons)
    qed
    then have "t \<noteq> \<epsilon>"
      using Suc.prems(1) True by force
    then show ?thesis
    proof (cases "n = 0")
      case True
      then have "a \<noteq> b"
        using Suc.prems(3) \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> by auto
      then show ?thesis
        using True \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> by auto
    next
      case False
      then obtain m where "n = Suc m"
        using not0_implies_Suc by blast
      have "#(\<up>b \<Zcat> t) = Fin k"
        using Suc.prems(1) \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> by auto
      moreover have "snth n s = snth m (\<up>b \<Zcat> t)"
        by (simp add: \<open>n = Suc m\<close> \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close>)
      ultimately have "srcdups\<cdot>(\<up>b \<Zcat> t) = srcdups\<cdot>(stake n\<cdot>(\<up>b \<Zcat> t)) \<Zcat> (srcdups\<cdot>(sdrop n\<cdot>(\<up>b \<Zcat> t)))"
        by (metis Suc.IH Suc.prems(2) Suc.prems(3) Suc_less_SucD \<open>n = Suc m\<close> \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> snth_scons)
      then show ?thesis
      proof (cases "srcdups\<cdot>s = srcdups\<cdot>(\<up>b \<Zcat> t)")
        case True
        then show ?thesis
        proof -
          have "a = b"
            by (metis (no_types) True \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> srcdups_shd)
          then show ?thesis
            by (simp add: \<open>n = Suc m\<close> \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> \<open>srcdups\<cdot>(\<up>b \<Zcat> t) = srcdups\<cdot> (stake n\<cdot> (\<up>b \<Zcat> t)) \<Zcat> srcdups\<cdot> (sdrop n\<cdot>(\<up>b \<Zcat> t))\<close>)
        qed
      next
        case False
        then show ?thesis
        proof -
          have "a \<noteq> b"
            using False \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> srcdups_eq2 by blast
          then show ?thesis
            by (simp add: \<open>n = Suc m\<close> \<open>s = \<up>a \<Zcat> \<up>b \<Zcat> t\<close> \<open>srcdups\<cdot>(\<up>b \<Zcat> t) = srcdups\<cdot> (stake n\<cdot> (\<up>b \<Zcat> t)) \<Zcat> srcdups\<cdot> (sdrop n\<cdot>(\<up>b \<Zcat> t))\<close>)
        qed
      qed
    qed
  next
    case False
    then have "k \<le> 1"
      by auto
    then show ?thesis
    proof (cases "k = 0")
      case True
      then show ?thesis
        using Suc.prems(2) by blast
    next
      case False
      then have "k = 1"
        using \<open>k \<le> 1\<close> by auto
      then obtain a b where "s = \<up>a \<Zcat> \<up>b" 
        by (metis One_nat_def Rep_cfun_strict1 Suc.prems(1) \<open>\<And>thesis. (\<And>a t. s = \<up>a \<Zcat> t \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> sconc_snd_empty sfood_id stake_Suc stream.take_0)
      then have "a \<noteq> b"
        using Suc.prems(2) Suc.prems(3) \<open>k = 1\<close> by auto
      then have "srcdups\<cdot>s = \<up>a \<Zcat> \<up>b"
        by (metis \<open>s = \<up>a \<Zcat> \<up>b\<close> lscons_conv srcdups_neq srcdups_step strict_sdropwhile strict_srcdups sup'_def)
      then show ?thesis
        using Suc.prems(2) \<open>k = 1\<close> \<open>s = \<up>a \<Zcat> \<up>b\<close> by auto
    qed
  qed
qed

lemma srcdups_split_inf: "#s = \<infinity> \<Longrightarrow> snth n s \<noteq> snth (Suc n) s \<Longrightarrow> srcdups\<cdot>s = srcdups\<cdot>(stake (Suc n)\<cdot>s) \<Zcat> (srcdups\<cdot>(sdrop (Suc n)\<cdot>s))"
proof (induction n arbitrary: s)
  case 0
  then obtain a b t where "s = \<up>a \<Zcat> \<up>b \<Zcat> t" and "a \<noteq> b"
    by (metis inf_scase shd1 snth_scons snth_shd)
  then show ?case
    by auto
next
  case (Suc n)
  obtain a t where "s = \<up>a \<Zcat> t"
    using Suc.prems(1) inf_scase by blast
  then have "#t = \<infinity>"
    using Suc.prems(1) by auto
  moreover have "snth n t \<noteq> snth (Suc n) t"
    using Suc.prems(2) \<open>s = \<up>a \<Zcat> t\<close> by auto
  ultimately have "srcdups\<cdot>t = srcdups\<cdot>(stake (Suc n)\<cdot>t) \<Zcat> (srcdups\<cdot>(sdrop (Suc n)\<cdot>t))"
    using Suc.IH by blast
  then show ?case
  proof (cases "a = shd t")
    case True
    then have "srcdups\<cdot>s = srcdups\<cdot>t"
      by (metis Inf'_neq_0 \<open>#t = \<infinity>\<close> \<open>s = \<up>a \<Zcat> t\<close> slen_empty_eq srcdups_eq surj_scons)
    then show ?thesis
      using True \<open>#t = \<infinity>\<close> \<open>s = \<up>a \<Zcat> t\<close> \<open>srcdups\<cdot>t = srcdups\<cdot> (stake (Suc n)\<cdot>t) \<Zcat> srcdups\<cdot>(sdrop (Suc n)\<cdot>t)\<close> inf_scase by fastforce
  next
    case False
    then have "srcdups\<cdot>s = \<up>a \<Zcat> srcdups\<cdot>t"
      by (metis Inf'_neq_0 \<open>#t = \<infinity>\<close> \<open>s = \<up>a \<Zcat> t\<close> slen_empty_eq srcdups_neq surj_scons)
    then show ?thesis
      using False \<open>#t = \<infinity>\<close> \<open>s = \<up>a \<Zcat> t\<close> \<open>srcdups\<cdot>t = srcdups\<cdot> (stake (Suc n)\<cdot>t) \<Zcat> srcdups\<cdot>(sdrop (Suc n)\<cdot>t)\<close> inf_scase by fastforce
  qed
qed

lemma srcdups_split2: "Fin (Suc n) < #s \<Longrightarrow> snth n s \<noteq> snth (Suc n) s \<Longrightarrow> srcdups\<cdot>s = srcdups\<cdot>(stake (Suc n)\<cdot>s) \<Zcat> (srcdups\<cdot>(sdrop (Suc n)\<cdot>s))"
  by (metis less2nat ninf2Fin not_le srcdups_split_fin srcdups_split_inf)



lemma srcdups_sconc: 
  "#xs < \<infinity> \<Longrightarrow> xs \<noteq> \<epsilon> \<Longrightarrow> 
    srcdups\<cdot>(xs \<Zcat> ys) = (srcdups\<cdot>xs) \<Zcat> (srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys))"
proof -
  assume "#xs < \<infinity>" and "xs \<noteq> \<epsilon>"
  then obtain t n where "xs = t \<Zcat> (sntimes n (\<up>(sfoot xs)))" and "t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs"
    using sfoot_end by fastforce
  then show ?thesis
  proof (cases "t = \<epsilon>")
    case True
    then have "xs \<Zcat> ys = (sntimes n (\<up>(sfoot xs))) \<Zcat> ys"
      using \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> by auto
    then have "srcdups\<cdot>(xs \<Zcat> ys) = (\<up>(sfoot xs)) \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys)"
      by (metis Fin_02bot True \<open>xs = t \<Zcat>( n\<star>\<up>(sfoot xs))\<close> \<open>xs \<noteq> \<epsilon>\<close> lnzero_def neq0_conv sconc_fst_empty slen_empty_eq sntimes_len srcdups_sntimes_prefix)
    then show ?thesis
      by (metis Fin_02bot True \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> \<open>xs \<noteq> \<epsilon>\<close> lnzero_def neq0_conv sconc_fst_empty slen_empty_eq sntimes_len srcdups_sntimes)
  next
    case False
    then obtain k where "#t = Fin (Suc k)"
      by (metis Fin_02bot \<open>t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> bot_is_0 ninf2Fin not0_implies_Suc sconc_fst_inf slen_empty_eq)
    then show ?thesis
    proof (cases "ys = \<epsilon>")
      case True
      then show ?thesis
        by simp
    next
      case False
      have "snth k (xs \<Zcat> ys) \<noteq> snth (Suc k) (xs \<Zcat> ys)"
      proof
        assume "snth k (xs \<Zcat> ys) = snth (Suc k) (xs \<Zcat> ys)"
        then have "snth k xs = snth (Suc k) xs"
          by (metis Fin_02bot Fin_Suc len_stream_def Suc_neq_Zero \<open>#t = Fin (Suc k)\<close> \<open>#xs < \<infinity>\<close> \<open>t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> stake_prefix slen_snth_prefix inject_Fin le2lnle leI less_le lnless_def lnzero_def monofun_cfun_arg notinfI3 sfoot_exists2 stream.take_below slen_zero)
        then show "False"
          by (metis Fin_02bot Fin_Suc Suc_neq_Zero \<open>#t = Fin (Suc k)\<close> \<open>t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> slen_snth_prefix inject_Fin leI ln_less lnzero_def neq0_conv notinfI3 sconc_snd_empty sdropl6 sfoot_exists2 shd_sntime slen_empty_eq snth_def sntimes_len)
      qed
      moreover have "Fin (Suc k) < #(xs \<Zcat> ys)"
        by (metis False \<open>#t = Fin (Suc k)\<close> \<open>#xs < \<infinity>\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> minimal mono_slen monofun_cfun_arg sconc_snd_empty slen_conc)
      ultimately have "srcdups\<cdot>(xs \<Zcat> ys) = srcdups\<cdot>(stake (Suc k)\<cdot>(xs \<Zcat> ys)) \<Zcat> srcdups\<cdot>(sdrop (Suc k)\<cdot>(xs \<Zcat> ys))"
        using srcdups_split2 by blast
      then have "srcdups\<cdot>(xs \<Zcat> ys) = srcdups\<cdot>t \<Zcat> srcdups\<cdot>((sntimes n (\<up>(sfoot xs))) \<Zcat> ys)"
        by (metis \<open>#t = Fin (Suc k)\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> assoc_sconc stake_prefix2 sdropl6)
      then have "srcdups\<cdot>(xs \<Zcat> ys) = srcdups\<cdot>t \<Zcat> \<up>(sfoot xs) \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys)"
        by (metis \<open>t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> \<open>xs \<noteq> \<epsilon>\<close> neq0_conv sconc_snd_empty sntimes.simps(1) srcdups_sntimes_prefix)
      moreover have "srcdups\<cdot>xs = srcdups\<cdot>t \<Zcat> \<up>(sfoot xs)"
      proof -
        have "srcdups\<cdot>xs = srcdups\<cdot>t \<Zcat> srcdups\<cdot>(sntimes n (\<up>(sfoot xs)))"
          by (metis \<open>#t = Fin (Suc k)\<close> \<open>snth k (xs \<Zcat> ys) \<noteq> snth (Suc k) (xs \<Zcat> ys)\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> convert_inductive_asm slen_snth_prefix stake_prefix2 not_less notinfI3 sconc_snd_empty sdropl6 slen_conc srcdups_split2 strict_srcdups ub_slen_stake)
        then show ?thesis
          by (metis \<open>t = \<epsilon> \<or> sfoot t \<noteq> sfoot xs\<close> \<open>xs = t \<Zcat> (n\<star>\<up>(sfoot xs))\<close> \<open>xs \<noteq> \<epsilon>\<close> neq0_conv sconc_snd_empty sntimes.simps(1) srcdups_sntimes)
      qed
      ultimately show ?thesis
        by simp
    qed
  qed
qed


lemma srcdups_bool_prefix:
  fixes xs :: "bool stream" and ys :: "bool stream"
  assumes "lshd\<cdot>(srcdups\<cdot>xs) = lshd\<cdot>(srcdups\<cdot>ys)" and "#(srcdups\<cdot>xs) \<le> #(srcdups\<cdot>ys)"
  shows "(srcdups\<cdot>xs) \<sqsubseteq> (srcdups\<cdot>ys)"
proof (rule scases [of xs])
  assume "xs = \<epsilon>"
  then have "srcdups\<cdot>xs = \<epsilon>"
    by simp
  thus "srcdups\<cdot>xs \<sqsubseteq> srcdups\<cdot>ys"
    by simp
next
  fix a :: bool and s :: "bool stream"
  assume "xs = \<up>a \<Zcat> s"
  have "lshd\<cdot>(srcdups\<cdot>ys) = updis a"
    by (metis \<open>xs = \<up>a \<Zcat> s\<close> assms(1) lshd_updis srcdups_step)
  then have "lshd\<cdot>ys = updis a"
    by (metis lshd_updis srcdups_shd2 stream.sel_rews(3) strict_srcdups surj_scons up_defined)
  then have "\<forall>n. Fin n < #(srcdups\<cdot>ys) \<longrightarrow> snth n (srcdups\<cdot>ys) = (even n = a)"
    by (metis (no_types, lifting) bool_stream_snth lshd_updis stream.sel_rews(3) sup'_def surj_scons)
  then have ys_expr: "\<forall>n. Fin n < #(srcdups\<cdot>xs) \<longrightarrow> snth n (srcdups\<cdot>ys) = (even n = a)"
    using assms(2) less_le_trans by blast
  then have first_n_eq: "\<forall>n. Fin n < #(srcdups\<cdot>xs) \<longrightarrow> snth n (srcdups\<cdot>xs) = snth n (srcdups\<cdot>ys)"
    using \<open>xs = \<up>a \<Zcat> s\<close> bool_stream_snth by blast
  then show "srcdups\<cdot>xs \<sqsubseteq> srcdups\<cdot>ys"
  proof (cases "#(srcdups\<cdot>xs) < \<infinity>")
    case False
    then have "#(srcdups\<cdot>xs) = #(srcdups\<cdot>ys)"
      using assms(2) less_le by fastforce
    then have "\<forall>k. snth k (srcdups\<cdot>xs) = snth k (srcdups\<cdot>ys)"
      by (metis False Fin_neq_inf first_n_eq inf_ub order.not_eq_order_implies_strict)
    then have "srcdups\<cdot>xs = srcdups\<cdot>ys"
      by (simp add: \<open>\<forall>k. snth k (srcdups\<cdot>xs) = snth k (srcdups\<cdot>ys)\<close> \<open>#(srcdups\<cdot>xs) = #(srcdups\<cdot>ys)\<close> snths_eq)
    thus "srcdups\<cdot>xs \<sqsubseteq> srcdups\<cdot>ys"
      by simp
  next
    case True
    then obtain k where "#(srcdups\<cdot>xs) = Fin k"
      using lnat_well_h2 by blast
    then have eq_len: "#(srcdups\<cdot>xs) = #(stake k\<cdot>(srcdups\<cdot>ys))"
      using assms(2) slen_stake by force
    have "\<forall>n. Fin n < #(srcdups\<cdot>xs) \<longrightarrow> snth n (srcdups\<cdot>xs) = snth n (stake k\<cdot>(srcdups\<cdot>ys))"
      by (metis eq_len first_n_eq snth_less stream.take_below)
    then have "srcdups\<cdot>xs = stake k\<cdot>(srcdups\<cdot>ys)"
      by (simp add: \<open>\<forall>n. Fin n < #(srcdups\<cdot>xs) \<longrightarrow> snth n (srcdups\<cdot>xs) = snth n (stake k\<cdot>(srcdups\<cdot>ys))\<close> eq_len snths_eq)
    thus ?thesis
      by simp
  qed
qed

lemma srcdups_snth_stake_inf: "#s = \<infinity> \<Longrightarrow> snth n s \<noteq> snth (Suc n) s \<Longrightarrow> srcdups\<cdot>(stake (Suc n)\<cdot>s) \<noteq> srcdups\<cdot>s"
proof
  assume "#s = \<infinity>" and "snth n s \<noteq> snth (Suc n) s" and "srcdups\<cdot>(stake (Suc n)\<cdot>s) = srcdups\<cdot>s"
  have "#(stake (Suc (Suc n))\<cdot>s) = Fin (Suc (Suc n))"
    by (simp add: \<open>#s = \<infinity>\<close> slen_stake_fst_inf)
  moreover have "Suc (Suc n) > Suc n"
    by simp
  moreover have "snth n (stake (Suc (Suc n))\<cdot>s) \<noteq> snth (Suc n) (stake (Suc (Suc n))\<cdot>s)"
    by (metis Fin_leq_Suc_leq Suc_n_not_le_n \<open>snth n s \<noteq> snth (Suc n) s\<close> calculation(1) less2nat_lemma not_le snth_less stream.take_below)
  ultimately have "srcdups\<cdot>(stake (Suc n)\<cdot>(stake (Suc (Suc n))\<cdot>s)) \<noteq> srcdups\<cdot>(stake (Suc (Suc n))\<cdot>s)"
    using srcdups_snth_stake_fin by blast
  then have "srcdups\<cdot>(stake (Suc n)\<cdot>s) \<noteq> srcdups\<cdot>(stake (Suc (Suc n))\<cdot>s)"
    by (simp add: min_def)
  moreover have "srcdups\<cdot>(stake (Suc (Suc n))\<cdot>s) = srcdups\<cdot>s"
  proof (rule ccontr)
    assume "srcdups\<cdot>(stake (Suc (Suc n))\<cdot>s) \<noteq> srcdups\<cdot>s"
    moreover have "srcdups\<cdot>(stake (Suc n)\<cdot>s) \<sqsubseteq> srcdups\<cdot>(stake (Suc (Suc n))\<cdot>s)"
      by (simp add: less_imp_le_nat monofun_cfun_arg stake_mono)
    ultimately have "srcdups\<cdot>(stake (Suc n)\<cdot>s) \<noteq> srcdups\<cdot>s"
      by (metis below_antisym monofun_cfun_arg stream.take_below)
    then show "False"
      by (simp add: \<open>srcdups\<cdot>(stake (Suc n)\<cdot>s) = srcdups\<cdot>s\<close>)
  qed
  ultimately show "False"
    by (simp add: \<open>srcdups\<cdot>(stake (Suc n)\<cdot>s) = srcdups\<cdot>s\<close>)
qed


lemma srcdups_dom_h: assumes "sValues\<cdot>(srcdups\<cdot>s) = sValues\<cdot>s"
  shows "sValues\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> s)) = insert a (sValues\<cdot>s)"
proof (cases "shd s = a")
  case True
  have "srcdups\<cdot>(\<up>a \<Zcat> \<up>a \<Zcat> srt\<cdot>s) = srcdups\<cdot>(\<up>a \<Zcat> srt\<cdot>s)"
    using srcdups_eq by blast
  hence "a \<in> sValues\<cdot>(srcdups\<cdot>(\<up>a \<Zcat> srt\<cdot>s))"
    by (simp add: srcdups_step) 
  then show ?thesis
    by (metis True Un_insert_left assms insert_absorb2 sValues2un srcdups_eq srcdups_step strict_sdropwhile sup_bot.left_neutral surj_scons)
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) assms insert_is_Un sValues2un srcdups_neq srcdups_step strict_sdropwhile surj_scons)
qed
  
lemma srcdups_dom [simp]: "sValues\<cdot>(srcdups\<cdot>xs) = sValues\<cdot>xs"
apply(rule ind, simp_all)
  by (simp add: srcdups_dom_h)  


lemma srcdups_sconc_duplicates:
  assumes "#xs < \<infinity>" and "xs \<noteq> \<epsilon>" and "srcdups\<cdot>xs = srcdups\<cdot>(xs \<Zcat> ys)"
  shows "sValues\<cdot>ys \<subseteq> {sfoot xs}"
proof -
  have "srcdups\<cdot>(xs \<Zcat> ys) = (srcdups\<cdot>xs) \<Zcat> (srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys))"
    using assms(1) assms(2) srcdups_sconc by blast
  then have "srcdups\<cdot>xs = srcdups\<cdot>xs \<Zcat> (srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys))"
    using assms(3) by presburger
  moreover have "#(srcdups\<cdot>xs) < \<infinity>"
    by (meson assms(1) leD leI srcdups_slen trans_lnle)
  ultimately have "srcdups\<cdot>(sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys) = \<epsilon>"
    using sconc_neq_h by fastforce
  then have "sdropwhile (\<lambda>x. x=sfoot xs)\<cdot>ys = \<epsilon>"
    using srcdups_nbot by blast
  then show ?thesis
    by (metis (full_types) insertI1 sconc_snd_empty stakewhileDropwhile stakewhile_dom subsetI)
qed

lemma srcdups_sfoot:
  "s \<noteq> \<epsilon> \<Longrightarrow> #s < \<infinity> \<Longrightarrow> sfoot (srcdups\<cdot>s) = sfoot s"
proof (rule footind2, simp+)
  fix t :: "'a stream" and a :: 'a
  assume "#t < \<infinity>" and "sfoot (srcdups\<cdot>t) = sfoot t"
  show "sfoot (srcdups\<cdot>(t \<Zcat> \<up>a)) = a"
  proof (rule footind2 [of t], auto, simp add: \<open>#t < \<infinity>\<close>)
    fix t :: "'a stream" and b :: 'a
    assume "#t < \<infinity>" and "sfoot (srcdups\<cdot>(t \<Zcat> \<up>a)) = a"
    then show "sfoot (srcdups\<cdot>(t \<Zcat> \<up>b \<Zcat> \<up>a)) = a"
    proof -
      have "\<And>l. l < \<infinity> \<or> l = \<infinity>"
        by (meson inf_less_eq le_less_linear)
      then show ?thesis
        by (metis (no_types) Fin_Suc \<open>#t < \<infinity>\<close> \<open>sfoot (srcdups\<cdot>(t \<Zcat> \<up>a)) = a\<close> lnat_well_h2 notinfI3 sfoot12 slen_lnsuc srcdups_end_eq srcdups_end_neq srcdups_slen)
    qed
  qed
qed


lemma inf_srcdups_stake_snth_sdrop:
  assumes "#s = \<infinity>" and "srcdups\<cdot>s = srcdups\<cdot>(stake k\<cdot>s)"
  shows "snth n (sdrop k\<cdot>s) = snth k s"
proof (induction n)
  case 0
  then show ?case
    by (simp add: snth_def)
next
  case (Suc n)
  then have "snth (Suc n) (sdrop k\<cdot>s) \<noteq> snth k s \<Longrightarrow> False"
  proof -
    assume "snth (Suc n) (sdrop k\<cdot>s) \<noteq> snth k s"
    have "#s = \<infinity>"
      by (simp add: assms(1))
    moreover have "snth (n + k) s \<noteq> snth (n + k + 1) s"
      by (metis Suc.IH Suc.prems Suc_eq_plus1 \<open>snth (Suc n) (sdrop k\<cdot>s) \<noteq> snth k s\<close> semiring_normalization_rules(23) snth_sdrop)
    ultimately have "srcdups\<cdot>(stake (n + k + 1)\<cdot>s) \<noteq> srcdups\<cdot>s"
      by (metis Suc_eq_plus1 srcdups_snth_stake_inf)
    moreover have "srcdups\<cdot>(stake (n + k + 1)\<cdot>s) = srcdups\<cdot>(stake k\<cdot>s)"
    proof -
      have "srcdups\<cdot>(stake k\<cdot>s) \<sqsubseteq> srcdups\<cdot>(stake (n + k + 1)\<cdot>s)"
      proof -
        have "k + (1 + n) = n + k + 1"
          by simp
        then show ?thesis
          by (metis (no_types) minimal monofun_cfun_arg sconc_snd_empty stake_add)
      qed
      then show ?thesis
        by (metis assms(2) below_antisym monofun_cfun_arg stream.take_below)
    qed
    ultimately show "False"
      by (simp add: assms(2))
  qed
  then show ?case
    by blast
qed

lemma srcdups_split:
  assumes "#(srcdups\<cdot>s) < \<infinity>" and "#s = \<infinity>"
  obtains n where "s = (stake n\<cdot>s) \<Zcat> ((\<up>(snth n s))\<^sup>\<infinity>)"
proof -
  obtain k where "srcdups\<cdot>s = srcdups\<cdot>(stake k\<cdot>s)"
    by (metis len_stream_def assms(1) fun_approxl2 lnat_well_h2)
  then have "sdrop k\<cdot>s \<noteq> srt\<cdot>(sdrop k\<cdot>s) \<Longrightarrow> False"
  proof -
    assume "sdrop k\<cdot>s \<noteq> srt\<cdot>(sdrop k\<cdot>s)"
    moreover have "#(sdrop k\<cdot>s) = #(srt\<cdot>(sdrop k\<cdot>s))"
      by (metis assms(2) fair_sdrop sdrop_back_rt)
    ultimately obtain n where "snth n (sdrop k\<cdot>s) \<noteq> snth n (srt\<cdot>(sdrop k\<cdot>s))"
      using snths_eq by blast
    moreover have "snth n (srt\<cdot>(sdrop k\<cdot>s)) = snth k s"
      by (metis \<open>srcdups\<cdot>s = srcdups\<cdot>(stake k\<cdot>s)\<close> assms(2) inf_srcdups_stake_snth_sdrop snth_rt)
    then show "False"
      by (metis (no_types) \<open>snth n (srt\<cdot>(sdrop k\<cdot>s)) = snth k s\<close> \<open>srcdups\<cdot>s = srcdups\<cdot>(stake k\<cdot>s)\<close> assms(2) calculation inf_srcdups_stake_snth_sdrop)
  qed
  then have "sdrop k\<cdot>s = \<up>(snth k s) \<Zcat> (sdrop k\<cdot>s)"
    by (metis Inf'_neq_0 assms(2) fair_sdrop snth_def slen_zero surj_scons)
  then have "sdrop k\<cdot>s = ((\<up>(snth k s))\<^sup>\<infinity>)"
    using s2sinftimes by blast
  then have "s = (stake k\<cdot>s) \<Zcat> ((\<up>(snth k s))\<^sup>\<infinity>)"
    by (metis split_streaml1)
  thus ?thesis
    by (metis that)
qed

lemma slen_srcdups_f_cont[simp]: "cont (\<lambda>s. #(srcdups\<cdot>(f\<cdot>s)))"
  apply (rule cont_compose [where f="\<lambda>x.(srcdups\<cdot>(f\<cdot>x))"])
  by simp+

lemma slen_srcdups_adm_eq[simp]: "adm (\<lambda>s. #(srcdups\<cdot>s) = #(srcdups\<cdot>(f\<cdot>s)))"
  by (rule adm_eq, simp_all add: cont_compose_mix)

lemma
  srcdups_smap_inj_eq:
  assumes "inj f"
  shows "#(srcdups\<cdot>(smap f\<cdot>s)) = #(srcdups\<cdot>s)"
  apply(induct s)
  using len_stream_cont_2
  apply (simp_all add: cont_compose_mix)
  apply(case_tac s, simp_all)
  apply(case_tac "a = aa", simp_all)
  by (simp add: assms inj_eq)

lemma srcdups_slen_mono: "#(srcdups\<cdot>s) \<le> #(srcdups\<cdot>(\<up>a \<Zcat>s))"
  apply (cases s, simp_all)
  apply (rename_tac x y)
  by (case_tac "a=x", simp_all)

lemma srcdups_slen_leq: " #(srcdups\<cdot>(\<up>a \<Zcat> s)) \<le>  lnsuc\<cdot>(#(srcdups\<cdot>s))"
  using srcdups_eq[of "shd s" "srt\<cdot>s"] srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s] by fastforce

lemma slen_srcdups_adm: "adm (\<lambda>a. #(srcdups\<cdot>a) \<ge> #(srcdups\<cdot>(f\<cdot>a)))" 
  apply (subst lnle_def)
  apply (rule adm_below) 
  apply (rule cont_compose [where f="\<lambda>x.(srcdups\<cdot>(f\<cdot>x))"])
  apply simp_all
  apply (rule cont_compose [where f="\<lambda>x. srcdups\<cdot>x"])
  by simp_all

lemma srcdups_sprojsnd_swap_len_le: "#(srcdups\<cdot>(sprojsnd\<cdot>y)) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>y))"
  apply (simp add: slen_sprojsnd)
  apply (induct y, simp_all) 
   apply (simp add: slen_srcdups_adm)
  apply (case_tac a; simp)
  apply (case_tac y; simp)
  apply (case_tac ab; simp)
  apply (case_tac "b\<noteq>ba"; simp)
  apply (case_tac "aa\<noteq>ac"; simp)
  by (meson dual_order.trans less_lnsuc)

lemma srcdups_smap_leq: "#(srcdups\<cdot>(smap f\<cdot>s)) \<le> #(srcdups\<cdot>s)"
  apply(induct s, simp_all add: slen_srcdups_adm)
  apply(case_tac s, simp_all)
  apply(case_tac "a = aa", simp_all)
  by (meson Orderings.preorder_class.order.trans lnsuc_lnle_emb srcdups_slen_leq)


lemma s2list_conc[simp]: assumes "#rest < \<infinity>"
  shows "s2list (\<up>msg \<Zcat> rest) = msg # (s2list rest)"
  apply(rule l2s_eqI)
  unfolding s2list_def
  apply(auto)[1]
  apply (metis (mono_tags) assms inf_less_eq inf_ub s2list_def s2list_id sconc_fst_inf sconc_slen sconc_snd_empty srcdups_step srcdupsimposs strict_sdropwhile strict_srcdups verit_comp_simplify1(3))
  using assms by simp

lemma s2list_conc2[simp]: assumes "#as < \<infinity>" and "#bs < \<infinity>"
  shows "s2list (as \<Zcat> bs) = (s2list as) @ (s2list bs)"
  by (metis assms(1) assms(2) list2s_inj listConcat s2list_id sconc_slen)

lemma s2list_conc3[simp]: assumes "#as < \<infinity>" and "#bs < \<infinity>"
  shows "<(s2list as)> \<Zcat> bs = <((s2list as) @ (s2list bs))>"
  by (metis assms(2) listConcat s2list_id)


end