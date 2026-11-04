theory PruneInvariant
  imports Automaton
begin

definition pruneAut::"('state \<Rightarrow> bool) \<Rightarrow> ('state::type, 'message::type, 'out::conc) automaton
  \<Rightarrow> ('state::type, 'message::type, 'out::conc) automaton" where
"pruneAut Inv aut = Abs_automaton(
  \<lambda>state msg. if Inv state then Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) 
                            else (autTransition\<cdot>aut) state msg, 
                Set.filter (Inv o fst) (autInitConfig\<cdot>aut))"

lemma pruneaut_insert:
  assumes "\<And>msg state. Inv state \<Longrightarrow> Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) \<noteq> {}"
    and "Set.filter (Inv o fst) (autInitConfig\<cdot>aut) \<noteq> {}"
  shows "Rep_automaton (pruneAut Inv aut) = (
  \<lambda>state msg. if Inv state then Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) 
                            else (autTransition\<cdot>aut) state msg, 
                Set.filter (Inv o fst) (autInitConfig\<cdot>aut))"
  apply(simp add: pruneAut_def)
  by(subst Abs_automaton_inverse; simp add: assms)  
  
lemma pruneAut_below:
  assumes "\<And>msg state. Inv state \<Longrightarrow> Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) \<noteq> {}"
    and "Set.filter (Inv o fst) (autInitConfig\<cdot>aut) \<noteq> {}"
  shows "pruneAut Inv aut \<sqsubseteq> aut"
  apply(rule automaton_belowI)
   apply(simp add: autTransition.rep_eq)
   apply(subst pruneaut_insert; simp add: assms autTransition.rep_eq)
  apply (metis assms(1) autTransition.rep_eq)
   apply fastforce
   apply(simp add: autInitConfig.rep_eq)
  apply(subst pruneaut_insert; simp add: assms autInitConfig.rep_eq)
   apply (metis assms(2) autInitConfig.rep_eq)
  by fastforce

lemma pruneaut_statesemeq_h:
    assumes invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut) state msg
                   \<Longrightarrow> Inv nextState"
        and init_invariant: "\<And>state. state \<in> fst ` (autInitConfig\<cdot>aut) \<Longrightarrow> Inv state"
        and "Inv s"
      shows "stateSem step aut s \<subseteq> stateSem step (pruneAut Inv aut) s"
  apply(rule statesem_refine_rule [where Inv=Inv])
    apply(subst autTransition.rep_eq, subst pruneaut_insert)
      apply (metis (mono_tags, lifting) auttrans_nempty ball_imageD comp_apply empty_iff invariant member_filter neq_emptyD)
     apply (metis all_not_in_conv autinit_nempty comp_def init_invariant member_filter rev_image_eqI)
  using assms by fastforce+

lemma pruneaut_statesemeq:
    assumes invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut) state msg
                   \<Longrightarrow> Inv nextState"
        and init_invariant: "\<And>state. state \<in> fst ` (autInitConfig\<cdot>aut) \<Longrightarrow> Inv state"
        and "Inv s"
      shows "stateSem step aut s = stateSem step (pruneAut Inv aut) s"
  apply(rule antisym)
   apply(rule pruneaut_statesemeq_h; simp add: assms)
  apply(rule le_funD, rule statesem_mono_h)
    apply(subst autTransition.rep_eq, subst pruneaut_insert)
      apply (metis (mono_tags, lifting) auttrans_nempty ball_imageD comp_apply empty_iff invariant member_filter neq_emptyD)
   apply (metis all_not_in_conv autinit_nempty comp_def init_invariant member_filter rev_image_eqI)
  by (simp add: Set.filter_def)


theorem pruneAut_sem_below:
  assumes "\<And>msg state. Inv state \<Longrightarrow> Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) \<noteq> {}"
    and "Set.filter (Inv o fst) (autInitConfig\<cdot>aut) \<noteq> {}"
  shows "sem step (pruneAut Inv aut) \<subseteq> sem step aut"
  apply(rule sem_mono2)
  by(insert pruneAut_below [OF assms], simp)


definition isPruneable:: "('state \<Rightarrow> bool) \<Rightarrow> ('state, 'message, 'out::conc) automaton \<Rightarrow> bool" where
"isPruneable Inv aut \<equiv> 
            (\<forall>msg state. Inv state 
                  \<longrightarrow> Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) \<noteq> {})
            \<and> Set.filter (Inv o fst) (autInitConfig\<cdot>aut) \<noteq> {}"

theorem pruneAut_sem_below':
  assumes "isPruneable Inv aut"
  shows "sem step (pruneAut Inv aut) \<subseteq> sem step aut"
  apply(rule pruneAut_sem_below; insert assms)
  by(auto simp add: isPruneable_def)

theorem pruneAut_inv_trans: 
  assumes "\<And>msg state. Inv state \<Longrightarrow> Set.filter (Inv o fst) ((autTransition\<cdot>aut) state msg) \<noteq> {}"
    and "Set.filter (Inv o fst) (autInitConfig\<cdot>aut) \<noteq> {}"
    and "Inv state"
    and nextState: "nextState \<in> fst ` (autTransition\<cdot>(pruneAut Inv aut)) state msg"
  shows "Inv nextState"
  apply(insert nextState, simp add: autTransition_def)
  apply(subst(asm) pruneaut_insert; simp add: assms)
  by fastforce

end