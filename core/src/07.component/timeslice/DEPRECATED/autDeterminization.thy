theory autDeterminization
imports automaton_timeslice dAutomaton
begin
default_sort %invisible "chan"


lemma %invisible some_inI: "A \<noteq> {} \<Longrightarrow> (SOME x. x\<in>A) \<in> A"
  by (simp add: some_in_eq)



definition nda2da:: "('state::type,'in,'out\<^sup>\<Omega>) ndAutomaton \<Rightarrow>
                        ('state::type,'in,'out) dAutomaton" where
"nda2da nda \<equiv> let (initState, initOut) =
                       SOME x. x\<in>autInitConfig\<cdot>nda in
  (| daTransition = (\<lambda> s sbe. SOME x. x\<in>(autTransition\<cdot>nda) s sbe),
     daInitState  = initState, 
     daInitOut    = initOut |)"





lift_definition da2nda::"('state::type, 'in, 'out) dAutomaton 
                           \<Rightarrow> ('state::type, 'in, 'out\<^sup>\<Omega>) ndAutomaton " is
              "\<lambda>da. ((\<lambda>s sbe. {daTransition da s sbe}),
                             {(daInitState da, daInitOut da)})"
  by simp


lemma initconfigda_def [simp]:"(autInitConfig\<cdot>(da2nda da)) = 
                                {(daInitState da, daInitOut da)}"
  apply(simp add: autInitConfig.rep_eq)
  by(simp add: da2nda.rep_eq)

lemma %invisible initconfig_single [simp]:
  shows "is_singleton(autInitConfig\<cdot>(da2nda da))"
  by(simp) 
(*
text\<open>The following definition converts a underspecified, non-deterministic automaton to an non-deterministic automaton with deterministic behavior. It corresponds to a refined NDA by reducing the transition set and the set of initial states to a singleton. The difference has been reduced to the fact that the NDA now obtained represents the transitions and configurations as singleton sets instead of the (unique) element from them.\<close>

lift_definition ndaOne::"('state::type,'in,'out) ndAutomaton \<Rightarrow> 
                            ('state::type,'in,'out) ndAutomaton" is
"\<lambda>nda. ( (\<lambda>s sbe. {SOME x. x\<in>(ndaTransition\<cdot>nda) s sbe},
                               {SOME x. x\<in>ndaInitConfig\<cdot>nda}))"
  by simp


text\<open>Applying \<open>ndaOne\<close> at any automaton refines this automaton.\<close>

lemma ndaone_refined [simp]:  
  shows "ndaOne nda \<sqsubseteq> nda"
  apply(rule nda_belowI)
   apply(auto simp add: ndaOne.rep_eq ndaTransition.rep_eq)
   apply(rule some_inI)
  apply (metis fst_conv repnda_exists)
     apply(auto simp add: ndaOne.rep_eq ndaInitConfig.rep_eq)
   apply(rule some_inI)
  by (metis repnda_exists snd_conv)

text\<open>Transforming the non-deterministic automaton into a deterministic one is a refinement. This means that the transition function of the DA must be taken from the set of transition functions of the NDA.\<close>

lemma nda2da_trans [simp]:
  shows "(daTransition (nda2da nda) state sb) \<in> 
                                    ((ndaTransition\<cdot>nda) state sb)"
proof -
  obtain x1 x2 where x_def:"(SOME x::'a \<times> 'b\<^sup>\<Omega>. x \<in> ndaInitConfig\<cdot>nda) = (x1,x2)"
    by (meson eq_snd_iff)
  show ?thesis
    apply(simp add: nda2da_def ndaTransition.rep_eq case_prod_def x_def)
    by (metis ndaTransition.rep_eq ndatrans_nempty some_in_eq)
qed

lemma %invisible da2nda_trans_eq:
  shows "{(daTransition (da) state sb)} = 
                                    ((ndaTransition\<cdot>(da2nda da)) state sb)"
  by (simp add: da2nda.rep_eq ndaTransition.rep_eq)

text\<open>The same applies to the initial state. Here the different representation leads to the fact that on the deterministic side, two record accesses are necessary, while on the other side (hidden in \<open>ndaInitConfig\<close>), there is only one.\<close>

text\<open>\<close>

text\<open>\<close>

text\<open>\<close>

lemma nda2da_initconfig [simp]:
  shows "(daInitState (nda2da nda), daInitOut (nda2da nda)) \<in> 
                                                  ndaInitConfig\<cdot>nda"
proof-
  obtain x1 x2 where x_def:"(SOME x::'a \<times> 'b\<^sup>\<Omega>. x \<in> snd (Rep_ndAutomaton nda)) =(x1,x2)"
    by (meson eq_snd_iff)
  show ?thesis
  apply(simp add: ndaInitConfig.rep_eq nda2da_def case_prod_def x_def)
    by (metis all_not_in_conv eq_snd_iff repnda_exists verit_sko_ex' x_def)
qed

lemma %invisible da2nda_conf_eq:
  shows "{(daInitState (da), daInitOut (da))} = 
                                                  ndaInitConfig\<cdot>(da2nda da)"
  by simp

text\<open>With this knowledge, two central conclusions can now be drawn: First, the transformation of a DA to an NDA is lossless. This means that after the two transformation (DA \<open>>\<close> NDA \<open>>\<close> DA), the resulting automaton is exactly the original one (see \Cref{fig:da2nda}).\<close>
theorem da2nda2da : 
  shows "nda2da (da2nda da) = da"
    apply(simp add: nda2da_def case_prod_def da2nda_def ndaInitConfig.rep_eq Abs_ndAutomaton_inverse ndaTransition.rep_eq)
    by(simp add: Abs_ndAutomaton_inverse)
   

theorem nda2da2nda : 
  shows "da2nda (nda2da nda) \<sqsubseteq> nda"
  apply(rule nda_belowI)
  apply (metis da2nda.rep_eq fst_conv nda2da_trans ndaTransition.rep_eq singletonD subrelI)
  by (metis da2nda.rep_eq nda2da_initconfig ndaInitConfig.rep_eq singletonD snd_conv subrelI)

text\<open>If an NDA is an automaton with an deterministic behavior (consisting of one transition and a one initial configuration), then each refinement of that automaton is the identity. This is due to the definition of the automaton as CPO, which only allows complete automata.\<close>

text \<open>Later this will also be important because this information ensures that the refinement of the automaton is not merely empty.\<close>

theorem ndasingleton_eq:
  assumes "\<And>s sbe. is_singleton ((ndaTransition\<cdot>nda)s sbe)"
        and "is_singleton (ndaInitConfig\<cdot>nda)"
        and "nda2 \<sqsubseteq> nda"
  shows "nda2 = nda"
proof - 
  obtain a b where ndainit: "ndaInitConfig\<cdot>nda = {(a, b)}"
    using assms(2) is_singletonE by fastforce
  from nothing show ?thesis
     apply(rule nda_eqI)
     apply(insert assms(1))
     apply(simp add: is_singleton_def)
     apply (metis assms(3) nda_trans_mono ndatrans_nempty subset_singletonD)
     apply(insert assms(2))[1]
     using assms(3) nda_init_mono ndainit ndainit_nempty by fastforce
qed

text\<open>With the significant findings from the previous lemma, it can now be concluded in particular that an NDA with deterministic behavior can also be transformed loss-free in the reverse direction.\<close>

theorem nda2da2nda_eq:
  assumes "\<And>s sbe. is_singleton ((ndaTransition\<cdot>nda)s sbe)"
  and "is_singleton (ndaInitConfig\<cdot>nda)"
  shows "da2nda(nda2da nda) = nda"
  by (simp add: nda2da2nda ndasingleton_eq assms)


lemma %invisible ndaut_slower[simp]:
  assumes "pspf \<le>  (\<lambda> state. {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)
  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
             \<and>  fst (f sbe) \<in> pspf (fst (snd (f sbe)))})"
  shows "pspf \<le> (\<lbrakk>nda\<rbrakk>\<^sup>p)"
  apply(simp add: ndaStateSem_def)
  apply(rule gfp_upperbound) 
  using assms by auto

lemma %invisible ndaut_subsetss:
  assumes "spf \<le>  (\<lambda> state. {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)
  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
             \<and>  fst (f sbe) \<in> spf (fst (snd (f sbe)))})"
  shows "spf s \<subseteq> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  apply(rule le_funD[of spf])
  by(insert assms,simp)


lemma %invisible ndaut_subsetsstest:
  assumes "SF \<le>  (\<lambda> state. {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)
  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
             \<and>  fst (f sbe) \<in> SF (fst (snd (f sbe)))})"
  and "spf \<in> SF s"
  shows "spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  using ndaut_subsetss assms
  by fastforce

text\<open>As introduced earlier, the set that covers all behavior of an NDA is the greatest fixpoint of all possible behaviors. Therefore, the greatest fixpoint contains, in particular, the behavior which results in using only one possible behavior.\<close>

text\<open>Before proving this for the semantic of the automaton itself, an intermediate step is taken, and the proof is done trough the state semantics. This is a generalization since if a proof applies for a state semantic for an arbitrary state; it applies in particular for the semantics of an automaton with a fixed state.\<close>

text\<open>To use this lemma later for backtracking a transformed DA to an NDA, it is shown that the state semantics of the converted NDA (an DA, \<open>nda2da nda\<close>) is a subset of the state semantics of the origin automaton.\<close>

text\<open>In this case, note that the operator \<open>\<le>\<close> was used instead of \<open>\<sqsubseteq>\<close>. The meaning, especially for the reader, is the same, but a different theory is used within the program. This allows the use of additional lemmas in the proof process itself. The operator here defines an order over the power-set of all possible I/O histories and the known \<open>\<sqsubseteq>\<close> order from the introduction chapter. \<close>

lemma %invisible dasemssndasem_lattice[simp]:
  shows "(\<lambda>s. {daStateSem (nda2da nda) s}) \<le> \<lbrakk>nda\<rbrakk>\<^sup>p"
  apply(simp add: ndaStateSem_def case_prod_unfold Let_def)
  apply(rule gfp_upperbound)
  apply simp
proof(rule le_funI,auto)
  fix x::'a
  obtain f where f_def:"f =(\<lambda>sbe. (daStateSem (nda2da nda) (fst (snd (f sbe))),(daTransition (nda2da nda)) x sbe))"
    by fastforce
  then have helper:"\<And>sbe. fst (f sbe) = daStateSem (nda2da nda) (fst (snd (f sbe)))"
    by(subst f_def,simp)
  have "(\<forall>sbe::'b\<^sup>\<surd>. snd (f sbe) \<in> (ndaTransition\<cdot>nda) x sbe \<and> fst (f sbe) = daStateSem (nda2da nda) (fst (snd (f sbe))))"
    apply auto
    by(subst f_def,simp)+
  moreover have "daStateSem (nda2da nda) x = sb_step\<cdot>(\<lambda>sbe::'b\<^sup>\<surd>. \<Lambda> (sb::'b\<^sup>\<Omega>). snd (snd (f sbe)) \<Zcat>\<^sup>\<Omega> fst (f sbe)\<cdot>sb)"
    apply(rule sbsplit_eqI,simp_all)
    apply(subst f_def,simp add: helper)
    by(subst f_def,simp)
  ultimately show "\<exists>f::'b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>.
          daStateSem (nda2da nda) x = sb_step\<cdot>(\<lambda>sbe::'b\<^sup>\<surd>. \<Lambda> (sb::'b\<^sup>\<Omega>). snd (snd (f sbe)) \<Zcat>\<^sup>\<Omega> fst (f sbe)\<cdot>sb) \<and>
          (\<forall>sbe::'b\<^sup>\<surd>. snd (f sbe) \<in> (ndaTransition\<cdot>nda) x sbe \<and> fst (f sbe) = daStateSem (nda2da nda) (fst (snd (f sbe))))"
    by(subst exI [where x="f"],simp+)
qed

lemma dasemssndasem[simp]:
  shows "(\<lambda>s. {daStateSem (nda2da nda) s}) \<sqsubseteq> \<lbrakk>nda\<rbrakk>\<^sup>p"
  by (metis SetPcpo.less_set_def dasemssndasem_lattice fun_belowI le_fun_def)

text\<open>Using the set-theoretical relationship, it can now be derived that the state semantics of the transformed NDA is an element of the set of state semantics of the original NDA.\<close>

theorem ndadsseminndssem [simp]:
  shows "daStateSem (nda2da nda) state \<in> ((\<lbrakk>nda\<rbrakk>\<^sup>p) state)"
  by (metis dasemssndasem_lattice insert_subset le_fun_def)



theorem ndassem_nempty[simp]:
  shows "(\<lbrakk>nda\<rbrakk>\<^sup>p) state \<noteq> {}"
  using ndadsseminndssem by fastforce

text\<open>An important finding, which will be relevant, is that the semantics of a \verb|complete| automaton is never empty, meaning there is at least one mapping of input to output.\<close>

theorem ndasem_nempty [simp]:
  shows "\<lbrakk>nda\<rbrakk>\<^sup>c \<noteq> {}"
proof-
  obtain iniS iniOut where ini_def:"(iniS,iniOut) \<in> ndaInitConfig\<cdot>nda"
    using ndainit_nempty by fastforce
  obtain spf where spf_def:"spf \<in> ndaStateSem nda iniS"
    using ndassem_nempty by fastforce
  show ?thesis
    apply(simp add: ndaSem_def)
    using ini_def spf_def by auto
qed

text\<open>The theorem \<open>ndadseminndsem\<close> proves that the semantics of a transformed NDA lies in the set of the semantics of the original NDA, which can be derived from the lemma \<open>ndadsseminndassem\<close>. This lemma shows the proof for an arbitrary state; because the semantics is an abbreviation of the state semantic with a fixed state, this can be deducted easily.\<close>

theorem ndadseminndsem [simp]:
  shows "\<lbrakk>(nda2da nda)\<rbrakk>\<^sup>d \<in> \<lbrakk>nda\<rbrakk>\<^sup>c"
  apply(simp add: ndaSem_def daSem_def)
  apply(rule exI [where x="daInitOut (nda2da nda)"])
  apply(rule exI [where x="daInitState (nda2da nda)"])
  apply(rule exI [where x="daStateSem (nda2da nda) (daInitState (nda2da nda))"])
  by simp 


                  

(* da2nda *) 

text\<open>After the straight direction was shown, the reverse direction now follows. The deterministic semantics of a DA is, in particular, a subset of the semantics of the transforming DA.\<close>

lemma dsseminndssem [simp]:
  shows "daStateSem da s \<in> ((\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) s)"
  by (metis da2nda2da ndadsseminndssem)

lemma %invisible dsseminndssem2 [simp]:
  shows "daStateSem da s \<in> (ndaStateSem2 (da2nda da) s)"
  by (metis da2nda2da ndadsseminndssem ndastatesem_eq)

text\<open>And if it applies regardless of the transferred state, then it follows that it also applies when the state is fixed.\<close>

theorem dseminndsem [simp]: 
  shows "\<lbrakk>da\<rbrakk>\<^sup>d \<in> \<lbrakk>(da2nda da)\<rbrakk>\<^sup>c"
  apply(simp add: daSem_def ndaSem_def ndastatesem_eq)
  apply(rule exI [where x="daStateSem da (daInitState da)"])
  by(simp)


theorem %invisible dasingleton_h_somechan[simp]:
  fixes 
       da::"('state::type, 'in::{chan,finite}, 'out) dAutomaton"
  assumes "\<not> chDomEmpty TYPE('in)"
  shows "is_singleton ((\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) state)"
  apply(rule is_singletonI')
  using ndadsseminndssem apply fastforce
proof(rule ccontr)
  fix x y::"'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>"
  assume a1:"x \<in> (\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) state"
  assume a2:"y \<in> (\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) state"
  assume in_eq:"x \<noteq> y"
  then obtain sb where sb_def:"x\<cdot>sb \<noteq> y\<cdot>sb"
    using cfun_eqI by blast
  then have sbLen : "0 < #sb"
    by (metis Inf'_neq_0 a1 a2 le_less_linear lnmin_eqasmthmin ndastatesem_bottom sblen_empty sbnleast_len strict_lnmin_snd)
  then have "\<And>(Y::nat \<Rightarrow> 'in\<^sup>\<Omega>).  \<forall> i. 0 < #(Y i) \<Longrightarrow> \<exists> i. (Y i) \<noteq> \<bottom>"
    apply(subgoal_tac "\<not> chDomEmpty TYPE('in)")
    using botlen apply fastforce
    using assms by blast
  then have "x\<cdot>sb = y\<cdot>sb"
    using a1 a2
  proof(induction sb arbitrary: state x y rule: sb_ind)
    case adm
    then show ?case
      by(simp)
  next
    case (empty sb)
    then show ?case
      using assms by blast
  next
    case (least sb)
    then show ?case
      by (metis assms ndastatesem_bottom sbnleast_len)
  next
    case (sbeCons sbe sb)
    from sbeCons show ?case 
      apply simp
      using ndastatesem_step[of x "da2nda da" state sbe]
      using ndastatesem_step[of y "da2nda da" state sbe]
      apply(simp add: ndaTransition.rep_eq da2nda.rep_eq)
      by (metis fst_conv snd_conv)
  qed
  then show "False"
    using sb_def by blast
qed

text\<open>Another theorem consists of the fact that the transformed, deterministic automaton forms a NDA with deterministic behavior.  This is rather intuitive to understand, but to prove it in Isabelle, it has to be shown that the greatest fixpoint of all behaviors does not contain any other behavior.\<close>

theorem dasingleton [simp]:
  fixes 
      da::"('state::type, 'in::{somechan,finite}, 'out) dAutomaton"
  shows "is_singleton (\<lbrakk>(da2nda da)\<rbrakk>\<^sup>c)"
  apply(rule is_singletonI')
  using dseminndsem apply blast
  apply(simp add: ndaSem_def)
proof(rule cfun_eqI,auto)
  obtain spf where spf_def:"(\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) (daInitState da) = spf"
    using dasingleton_h_somechan by fastforce
  thus "\<And>(xa::'in\<^sup>\<Omega>) (spf::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) spfa::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
       spf \<in> (\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) (daInitState da) \<Longrightarrow> spfa \<in> (\<lbrakk>(da2nda da)\<rbrakk>\<^sup>p) (daInitState da) \<Longrightarrow> daInitOut da \<Zcat>\<^sup>\<Omega> spf\<cdot>xa = daInitOut da \<Zcat>\<^sup>\<Omega> spfa\<cdot>xa"
    by (metis dasingleton_h_somechan is_singleton_def singletonD somechannotempty)
qed

text\<open>If the facts are combined that the semantics of DA is a (non-empty) subset of the transformed DA and that the superset is a singleton, an equality relationship can be proven.\<close>

theorem dsemeqndsem [simp]:
  fixes 
      da::"('state::type, 'in::{somechan,finite}, 'out) dAutomaton"
  shows "\<lbrakk>(da2nda da)\<rbrakk>\<^sup>c = {\<lbrakk>da\<rbrakk>\<^sup>d}"
  using dasingleton dseminndsem
  by (metis is_singletonE singletonD)

text\<open>\<close>

text\<open>The previous lemmas are generally applicable, if the automaton has 
  at least one input. The following are the specializations that are used to 
  apply an existing property proof of DAs to specific NDA.\<close>


text\<open>The first lemma shows that a property that fulfills to the deterministic case also fulfills the SPF from the DA converted to the NDA.\<close>
theorem det2ndetpred:
  fixes 
      da::"('state::type, 'in::{somechan,finite}, 'out) dAutomaton"
  assumes"P (\<lbrakk>da\<rbrakk>\<^sup>d)"
  and "spf\<in> \<lbrakk>(da2nda da)\<rbrakk>\<^sup>c"
  shows "P spf"
  using assms by simp



text\<open>The second lemma will be used in the following context: The user defines his automaton as MontiArc Automaton and specifies the intended transition functions. Nevertheless, he does not want to define if the automaton is already deterministic. Therefore he omits the keyword, and the transformer generates a non-deterministic automaton. It can now be checked whether the preconditions for this lemma apply. If the generated NDA is a NDA with deterministic behavior, the first two assumptions are fulfilled, because the initial configuration and transition function are singleton sets. Besides, it is assumed that the properties for the converted, deterministic automata are proven. This is realistic since this framework is optimized to prove properties on DAs.\<close>


text\<open>It follows that the property is thus also valid for all SPFs from the NDA.\<close>

theorem ndet2detpred:  
  fixes 
      nda::"('state::type, 'in::{somechan,finite}, 'out) ndAutomaton"
  assumes "\<And>state sbe. is_singleton ((ndaTransition\<cdot>nda) state sbe)"
  and "is_singleton (ndaInitConfig\<cdot>nda)"  
  and "P (\<lbrakk>(nda2da nda)\<rbrakk>\<^sup>d)"
shows "\<forall>spf\<in>\<lbrakk>nda\<rbrakk>\<^sup>c. P spf"
proof - 
  have expand_nda : "nda = da2nda (nda2da nda)"
    by (simp add: assms(1) assms(2) nda2da2nda_eq)
  show ?thesis                        
    apply(subst expand_nda)
    using assms(3) by auto
qed

theorem ndet2detpred2:  
  fixes 
      nda::"('state::type, 'in::{somechan,finite}, 'out) ndAutomaton"
  assumes "\<And>state sbe. is_singleton ((ndaTransition\<cdot>nda) state sbe)"
  and "is_singleton (ndaInitConfig\<cdot>nda)"  
  and "P (\<lbrakk>(nda2da nda)\<rbrakk>\<^sup>d)"
shows "\<And>spf. spf \<in> \<lbrakk>nda\<rbrakk>\<^sup>c \<Longrightarrow> P spf"
  using ndet2detpred
  using assms(1) assms(2) assms(3) by auto

text\<open>With the help of the previous theorem, the last theorem in this library can now be shown. Here it is assumed that the property applies to all SPFs from the semantics of an NDA (previous lemma). It follows that the property applies in particular to the transformation of the NDA to the DA (and therefore especially for the DA).\<close>

theorem ndet2detpred_final:
  assumes "\<forall>spf\<in>(\<lbrakk>nda\<rbrakk>\<^sup>c). P spf"
  shows "P (\<lbrakk>(nda2da nda)\<rbrakk>\<^sup>d)"
  by(simp add: assms)
         
*)
end