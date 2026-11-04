theory StreamReachability
  imports stream.StreamOther  
      "../../00.inc/DEPRECATED/Reachability"

begin

(*
(* ----------------------------------------------------------------------- *)
subsection \<open>Reachability\<close>
(* ----------------------------------------------------------------------- *)
lemma freach_ext_dom:
  assumes "b \<in> freach f i (sValues\<cdot>(srt\<cdot>s))"
  shows "b \<in> freach f i (sValues\<cdot>s)"
  using assms
  apply (subgoal_tac "freach f i (sValues\<cdot>(srt\<cdot>s)) \<sqsubseteq> freach f i (sValues\<cdot>s)")
  apply (metis SetPcpo.less_set_def contra_subsetD)
  apply (subgoal_tac "(sValues\<cdot>(srt\<cdot>s)) \<sqsubseteq> (sValues\<cdot>s)")
  apply (rule monofunE [of "freach f i"], auto) 
  apply (simp add: freach_mono)
  by (metis (full_types) SetPcpo.less_set_def sdrop_0 sdrop_forw_rt sdrop_sValues)

lemma freach_ext_dom2:
  assumes "s \<noteq> \<epsilon>"
  shows "freach f i (sValues\<cdot>(srt\<cdot>s)) \<sqsubseteq> freach f i (sValues\<cdot>s)"
  using assms
  by (simp add: SetPcpo.less_set_def freach_ext_dom subset_iff)

lemma freach_step_ext:
  assumes "s \<noteq> \<epsilon>"
  shows "freach f (fst (f i (shd s))) (sValues\<cdot>s) \<sqsubseteq> freach f i (sValues\<cdot>s)"
  using assms
  apply (simp add: SetPcpo.less_set_def)
  apply (subst freach_def)
  apply (rule fix_ind)
  apply (rule admI)
  apply (simp add: SUP_least lub_eq_Union)
  apply (metis UU_eq_empty freach_initial_in freach_suc_in sfilter_ne_resup sfilter_sValuesl4 
         singletonD subsetI sup_bot.right_neutral)
  apply (auto simp add: freach_h_def)
  apply (simp add: freach_suc_in)
  by (meson contra_subsetD freach_suc_in)

lemma freach_step:
  assumes "s \<noteq> \<epsilon>"
  shows "freach f (fst (f i (shd s))) (sValues\<cdot>(srt\<cdot>s)) \<sqsubseteq> freach f i (sValues\<cdot>s)"
  using assms
  by (meson freach_ext_dom2 freach_step_ext rev_below_trans)

lemma f2snth_sscanlasnd_freach:
  assumes "Fin j < #s"
    and "\<And>b e. e \<in> sValues\<cdot>s \<Longrightarrow> b \<in> freach f i (sValues\<cdot>s) \<Longrightarrow> P e (snd (f b e))"
  shows "P (snth j s) (snth j (sscanlAsnd f i\<cdot>s))"
  using assms
  proof (induction j arbitrary: s f i)
    case 0
    then show ?case
      by (metis Fin_02bot freach_initial_in lnless_def lnzero_def slen_empty_eq snth2sValues 
          snth_shd sscanlasnd_shd)
    next
    case (Suc j)
    then show ?case
      apply (simp add: snth_rt sscanlasnd_srt)
      apply (rule Suc.IH)
      apply (meson not_le slen_rt_ile_eq)
      apply (rule Suc.prems)
      apply (metis (no_types, opaque_lifting) contra_subsetD empty_iff lscons_conv sValues_subset 
             sfilterEq2sValues sfilter_ne_resup snth2sValues stream.con_rews(2) surj_scons)
      by (metis (no_types, lifting) SetPcpo.less_set_def contra_subsetD empty_is_shortest 
          freach_step)
  qed

lemma freach_initial_transfer:
  assumes "P i"
    and "\<forall>e \<in> sValues\<cdot>s. \<forall>b. P b \<longrightarrow> P (fst (f b e))"
  shows "\<forall>b \<in> freach f i (sValues\<cdot>s). P b"
  using assms
  apply (subst freach_def)
  apply (rule fix_ind)
  apply simp_all
  apply (simp add: lub_eq_Union)
  apply (simp add: UU_eq_empty)
  by (auto simp add: freach_h_def)
*)

end