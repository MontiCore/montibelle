theory PredAutRefine

imports stream.Stream automaton.Automaton sps.InvRefinement
      stream.StreamAutomaton

begin

fun greaterThanTrans::"nat \<Rightarrow> unit \<Rightarrow> nat \<Rightarrow> (unit \<times> bool stream) set" where
"greaterThanTrans n _ msg = {((), \<up>(msg \<ge> n))}"

lift_definition greaterThanAut::"nat \<Rightarrow> (unit, nat, bool stream) automaton" is
"\<lambda>n. (greaterThanTrans n, {((), \<epsilon>)})"
  by auto



fun onceGreaterTrans::"nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> (bool \<times> bool stream) set" where
"onceGreaterTrans n lock msg = (if lock \<and> msg < n then UNIV
                                  else {(lock \<or> n\<le>msg, \<up>(lock \<or> n\<le>msg))})"

lift_definition onceGreaterAut::"nat \<Rightarrow> (bool, nat, bool stream) automaton" is
"\<lambda>n. (onceGreaterTrans n, {(False, \<epsilon>)})"
  by auto


definition hdGreaterEqPre::"nat \<Rightarrow> nat stream \<Rightarrow> bool" where
"hdGreaterEqPre n xs \<equiv> if xs \<noteq> \<bottom> then n \<le> (shd xs) else False"

definition ascendingPred::"nat stream \<Rightarrow> bool" where
"ascendingPred xs \<equiv> \<forall>n. Fin (Suc n) < #xs \<longrightarrow> snth n xs \<le> snth (Suc n) xs"

lemma "ascendingPred (<[1,2,3,4::nat]>)"
  oops


lemma ascpred_adm: "adm ascendingPred" 
  unfolding ascendingPred_def
  apply(rule admI)
  apply auto
  oops


lemma admI2: "(\<And>Y. \<lbrakk>chain Y; \<forall>i. P (Y i); \<forall>i. #(Y i) < \<infinity>;#(\<Squnion>i. Y i) = \<infinity>\<rbrakk> \<Longrightarrow> P (\<Squnion>i. Y i)) \<Longrightarrow> adm P"
  oops


lemma len_chain: "chain Y \<Longrightarrow> #(Y i) \<le> #(Lub Y)"
  apply(subst lnle_def)
  apply(rule monofunE [where f="len"])
  using len_class.len_mono apply auto[1]
  by (simp add: is_ub_thelub)


lemma ascpred_not_adm: "adm (\<lambda>x. \<not>ascendingPred x)"
  unfolding ascendingPred_def
proof(rule admI, simp)
  fix Y::"nat \<Rightarrow> nat stream"
       assume "chain Y"
         and as: "\<forall>i::nat. \<exists>n::nat. Fin (Suc n) < #(Y i) \<and> \<not> snth n (Y i) \<le> snth (Suc n) (Y i)"
       obtain n where len: "Fin (Suc n) < #(Y 0)" and le:"\<not> snth n (Y 0) \<le> snth (Suc n) (Y 0)"
         using as by blast
       have h1: "Fin (Suc n) < #(Lub Y)" using len \<open>chain Y\<close> len_chain 
         using dual_order.strict_trans1 by blast
       have h2: "\<And>m. m \<le> Suc n \<Longrightarrow>  snth m (Y 0) = snth m (Lub Y)"
         apply(rule snth_less) 
          apply (simp add: len order_le_less_subst2)
         apply(rule is_lub_rangeD1 [where S="Y"])
         using \<open>chain (Y::nat \<Rightarrow> nat stream)\<close> cpo is_lub_lub by auto

       have h3: "\<not> snth n (Lub Y) \<le> snth (Suc n) (Lub Y)" 
         by (auto simp add: le h2[symmetric])
         
       show " \<exists>n::nat. Fin (Suc n) < #(Lub Y) \<and> \<not> snth n (Lub Y) \<le> snth (Suc n) (Lub Y)"
         using h1 h3 by blast
     qed

lemma ascpred_srt: "ascendingPred xs \<Longrightarrow> ascendingPred (srt\<cdot>xs)"
  unfolding ascendingPred_def
  apply auto
  by (metis less2eq linorder_le_less_linear nless_le slen_rt_ile_eq snth_rt)


lemma ascend2greater: "ascendingPred (\<up>msg \<Zcat>\<Zcat> input) \<Longrightarrow> input\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre msg input"
  unfolding hdGreaterEqPre_def ascendingPred_def
  apply auto 
  by (metis Fin_02bot Stream.slen_empty_eq lnless_def lnzero_def minimal shd1 snth_shd)

lemma invrev_statesem:
  assumes "ascendingPred input" and "(input\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre prev input)"
          and "f \<in> stateSem stream_step (onceGreaterAut n) (state)"
          and "prev < n \<longleftrightarrow> \<not>state"
  shows "f\<cdot>input = daStateSem stream_step (aut2da  (greaterThanAut n)) ()\<cdot>input"
  using assms proof (induction input arbitrary: state f prev rule: ind)
  case 1
  then show ?case 
        apply(rule adm_imp, simp add: ascpred_not_adm)
        apply((rule adm_all)+, rule adm_imp)
         apply(rule admI, auto simp add: hdGreaterEqPre_def lub_eq_bottom_iff)
    by (metis below_shd is_ub_thelub)
next
  case 2
  then show ?case by simp
next
  case (3 msg s)
  have "prev \<le> msg" 
    using "3.prems"(2) hdGreaterEqPre_def by auto
  have "ascendingPred s"
    by (metis "3.prems"(1) ascpred_srt inject_scons strictI surj_scons)
  have "s\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre msg s"
    by(rule ascend2greater; simp add: "3.prems"(1))

  obtain f' out nextState where f_step: "f\<cdot>(\<up>msg \<Zcat> s) = out \<Zcat>\<Zcat> f'\<cdot>s"
      and in_trans:"(nextState,out) \<in> (autTransition\<cdot>(onceGreaterAut n)) state msg"
      and f'_in:"f' \<in> (stateSem stream_step (onceGreaterAut n)) nextState" 
    by (metis (no_types, opaque_lifting) "3.prems"(3) conc_stream_def stateSemf_def stream_steps_sbe)

  have nstate: "(msg < n) \<Longrightarrow> \<not>state" 
    using "3.prems"(4) \<open>(prev::nat) \<le> (msg::nat)\<close> by auto
  have step_eq: "f'\<cdot>s = daStateSem stream_step (aut2da (greaterThanAut n)) ()\<cdot>s"
    apply(rule "3.IH" [where prev="msg" and state="nextState"])
       apply(simp_all add: \<open>ascendingPred s\<close> \<open>s\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre msg s\<close> f'_in)
    apply(insert in_trans; auto simp add: autTransition.rep_eq onceGreaterAut.rep_eq nstate)
    by (metis Pair_inject leI singletonD)
  have "state \<Longrightarrow> n \<le> msg"
    using "3.prems"(4) \<open>(prev::nat) \<le> (msg::nat)\<close> by fastforce
  hence "out = \<up>(state \<or> n\<le>msg)"
    by(insert in_trans "3.prems"(4), auto simp add: autTransition.rep_eq onceGreaterAut.rep_eq)
    

  then show ?case 
    unfolding f_step 
    apply(subst dastatesem_step) 
    apply(simp add: Let_def case_prod_beta)
    apply(subst aut2da_def)
    apply(simp add: autTransition.rep_eq greaterThanAut.rep_eq)
    apply(rule arg_cong2 [where f="\<lambda>s. (Rep_cfun (sconc s))"])
    using \<open>state::bool \<Longrightarrow> (n::nat) \<le> (msg::nat)\<close> apply auto[1]
    by(simp add: step_eq)
qed

theorem assumes "0<n"
  shows "invRefined ascendingPred (sem stream_step (onceGreaterAut n)) (sem stream_step (greaterThanAut n))"
proof(rule invRefinedI)
  fix f
  assume f_in: "f \<in> sem stream_step (onceGreaterAut n)"
  hence f_in2:  "f \<in> stateSem stream_step (onceGreaterAut n) False"
    by(subst(asm) sem_def_weak; simp add: onceGreaterAut.rep_eq autInitConfig.rep_eq)
  have f_bot: "f\<cdot>\<bottom> \<in> (snd ` (autInitConfig\<cdot>(onceGreaterAut n)))"
    by(rule sem_bot [of "stream_step"]; simp add: f_in)


  let ?g = "daSem stream_step (aut2da  (greaterThanAut n))"
  have g_in: "?g \<in>sem stream_step (greaterThanAut n)" 
    using sem_upper by auto
  have g_statesem: "?g = daStateSem stream_step (aut2da  (greaterThanAut n)) ()"
    by(simp add: daSem_def aut2da_def autInitConfig.rep_eq greaterThanAut.rep_eq)
  moreover have "\<And>sb prev. ascendingPred sb \<Longrightarrow> (sb\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre prev sb) \<Longrightarrow> f\<cdot>sb = ?g\<cdot>sb"
    apply(subst g_statesem)
    by(rule invrev_statesem [where prev="0" and state="False"]; (simp add: hdGreaterEqPre_def f_in2 assms)?)

  moreover have "\<And>sb. (sb\<noteq>\<bottom> \<Longrightarrow> hdGreaterEqPre 0 sb)"
    by(auto simp add: hdGreaterEqPre_def)
  ultimately show "\<exists>g. g \<in> sem stream_step (greaterThanAut n) \<and> (\<forall>sb::nat stream. ascendingPred sb \<longrightarrow> f\<cdot>sb = g\<cdot>sb)"
    apply(rule_tac x="?g" in exI) 
    using g_in by auto
qed

end