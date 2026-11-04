theory Automatons_all

imports ndaRefine ExecutableAut

begin

lemma ndastaterefine2_h:
   assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
shows "\<forall>s. (ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) s \<subseteq>
         (ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) (f s)"
  apply(rule ndastaterefine[where f=f])
  apply(simp add: assms)
  by simp

lemma ndastaterefine2:
   assumes "\<And>s sbe t out. (t, out) \<in> ((ndaTransition\<cdot>nda1) s sbe) \<Longrightarrow>
    (f t, out)  \<in> ((ndaTransition\<cdot>nda2) (f s) sbe)"
shows "(ndaStateSem (nda1::('s::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) s \<subseteq>
         (ndaStateSem (nda2::('a::type, 'in::{chan, finite}, 'out::chan) ndAutomaton)) (f s)"
  by (simp add: assms ndastaterefine2_h)


lemma dastaterefine_ndagen:
  fixes trans1::"'param1::type \<Rightarrow> 'state1::type 
      \<Rightarrow> 'in::countable \<Rightarrow> ('state1 \<times> 'out::countable)"
  fixes trans2::"'param2::type \<Rightarrow> 'state2::type 
      \<Rightarrow> 'in \<Rightarrow> ('state2 \<times> 'out) set"
  fixes mapState ::"'state1 \<Rightarrow> 'state2"
  fixes mapParam::"'param1 \<Rightarrow> 'param2"
  assumes "\<And>s i t out. (t,out) = (trans1 p s i) \<Longrightarrow> (mapState t,out) \<in> trans2 (mapParam p) (mapState s) i \<or> trans2 (mapParam p) (mapState s) i = {}"
  and "daGen fin fout"
shows "{daGen.stateSem trans1 initstate initout fin fout p s} \<subseteq>
       ndaGen.StateSem trans2 init2 fin fout (mapParam p) (mapState s)"
  apply(subst daGen.stateSem_def,simp add: assms(2))
  apply(subgoal_tac "(\<lbrakk>(da2nda(daGen.da trans1 initstate initout fin fout p))\<rbrakk>\<^sup>p)s \<subseteq> ndaGen.StateSem trans2 init2 fin fout (mapParam p) (mapState s)")
   apply auto[1]
  apply(insert assms(2),subgoal_tac "ndaGen fin fout") defer
  using assms(2) daGen_def ndaGen_def apply auto[1]
  apply(simp add: ndaGen.StateSem_def)
  apply(rule ndastaterefine2 [where f="mapState"],simp_all add: assms)
  apply(simp_all add: ndaTransition.rep_eq da2nda.rep_eq daGen.da_def ndaGen.nda.rep_eq assms(2))
  apply(simp_all add: assms(2) daGen.dtransition_def ndaGen.transition_def daGen.dtransitionH_def ndaGen.transitionH_def case_prod_unfold Let_def,rule)
  using assms(1)
  apply (smt UNIV_I apfst_conv apsnd_apfst_commute fst_apsnd imageI prod.collapse snd_apsnd)
  by (smt Pair_inject assms(1) fst_apsnd image_eqI prod.collapse snd_apsnd)


theorem dagenrefndagen:
  assumes "daGen fin fout"
  and "\<And>s i t out. (t,out) = (trans1 p s i) \<Longrightarrow> (mapState t,out) \<in> trans2 (mapParam p) (mapState s) i \<or> trans2 (mapParam p) (mapState s) i = {}"
  and "apfst mapState (init1 p,initout p) \<in> init2 (mapParam p) \<or> init2 (mapParam p) = {}"
shows "daGen.dSem trans1 init1 initout fin fout p \<subseteq> ndaGen.Sem trans2 init2 fin fout (mapParam p)"
  apply(subst daGen.dSem_def,simp add: assms, subst  daGen.sem_def,simp add: assms)
  apply(subgoal_tac "(\<lbrakk>(da2nda(daGen.da trans1 init1 initout fin fout p))\<rbrakk>\<^sup>c) \<subseteq> ndaGen.Sem trans2 init2 fin fout (mapParam p)")
  using dseminndsem apply blast
  apply(insert assms(1),subgoal_tac "ndaGen fin fout") defer
  using assms(1) daGen_def ndaGen_def apply auto[1]
  apply(simp add: ndaGen.Sem_def)
  apply(rule ndastateref[where f= mapState])
  apply(simp_all add: ndaTransition.rep_eq da2nda.rep_eq daGen.da_def ndaGen.nda.rep_eq)
  apply(simp_all add: daGen.dtransition_def ndaGen.transition_def daGen.dtransitionH_def ndaGen.transitionH_def case_prod_unfold Let_def,rule)
  using assms(2)
  apply (smt UNIV_I apfst_conv apsnd_apfst_commute fst_apsnd imageI prod.collapse snd_apsnd)
  apply (smt apsnd_apfst_commute assms(2) fst_apfst fst_apsnd imageI old.prod.inject prod.collapse snd_apfst snd_apsnd)
  apply(simp add: ndaInitConfig.rep_eq ndaGen.nda.rep_eq) 
  using assms(3) by auto

theorem dagenrefndagen:
  assumes "daGen fin fout"
  and "\<And>s. {daGen.stateSem trans1 init1 initout fin fout p s} \<subseteq>
           ndaGen.StateSem trans2 init2 fin fout (mapParam p) (mapState s)"
  and "apfst f (init1 p,initout p) \<in> init2 (g p) \<or> init2 (g p) = {}"
shows "daGen.dSem trans1 init1 initout fin fout p \<subseteq> ndaGen.Sem trans2 init2 fin fout (g p)"
    apply(subst daGen.dSem_def,simp add: assms, subst  daGen.sem_def,simp add: assms)
  apply(subgoal_tac "(\<lbrakk>(da2nda(daGen.da trans1 init1 initout fin fout p))\<rbrakk>\<^sup>c) \<subseteq> ndaGen.Sem trans2 init2 fin fout (g p)")
  using dseminndsem apply blast
  apply(insert assms(1),subgoal_tac "ndaGen fin fout") defer
  using assms(1) daGen_def ndaGen_def apply auto[1]
  apply(simp add: ndaGen.Sem_def)
  apply(rule ndarefine[where f= f])
  oops

end
