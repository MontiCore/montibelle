theory TsAutomaton

imports stream.StreamAutomaton automaton.Automaton 
  automaton.AutomatonCausality bundle.SBFin
begin
default_sort "type"



lemma fixes f::"'m::{tschan,finite}\<^sup>\<surd> \<Rightarrow> 'm\<^sup>\<Omega> \<rightarrow> 'n::tschan\<^sup>\<Omega>"
  assumes "\<And>input msg.  #\<^sub>\<surd>(sbe2sb msg) + #\<^sub>\<surd> input \<le> #\<^sub>\<surd>((f msg)\<cdot>input)"
  shows " #\<^sub>\<surd>input \<le> #\<^sub>\<surd>(sb_step\<cdot>f\<cdot>input)"
  using assms
  apply(cases input; simp add: assms)
  using assms
  apply(simp_all)
  apply (metis add.commute lnat_plus_suc)
  by(subst sb_steps_sbe_empty,simp_all)
 

type_synonym ('state,'In,'Out) ndAutomaton = 
             "('state, 'In sbElem, 'Out) automaton"

text\<open>As a splitting operator the @{const sb_step} function is 
adequate because it splits the input bundle in its first time slices
and the rest.\<close>
abbreviation ndaStateSem::
"('state,'In::{finite,tschan},'Out::{conc})ndAutomaton \<Rightarrow> 'state \<Rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out) set"where
"ndaStateSem \<equiv> stateSem sb_step"


abbreviation %invisible ndastatesem_abbrev::
"('s::type, 'I::{finite,tschan},'O::{conc}) ndAutomaton \<Rightarrow>'s\<Rightarrow>('I\<^sup>\<Omega> \<rightarrow> 'O) set" 
("\<lbrakk>_\<rbrakk>\<^sup>p" [1000] 999) where "\<lbrakk>aut\<rbrakk>\<^sup>p \<equiv> ndaStateSem aut"
abbreviation ndaSem::
"('state,'In::{finite,tschan},'Out::{conc}) ndAutomaton \<Rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out) set"where
"ndaSem \<equiv> sem sb_step"



abbreviation %invisible ndasem_abbrev::
"('s::type, 'I::{finite,tschan},'O::{conc}) ndAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O) set" 
("\<lbrakk>_\<rbrakk>\<^sup>c" [1000] 999) where "\<lbrakk>aut\<rbrakk>\<^sup>c \<equiv> ndaSem aut"

lemma statesem_unfold_pred:
  assumes"(\<And>spf out nstate. (nstate,out)\<in> (autTransition\<cdot>aut) s sbe 
               \<Longrightarrow> spf \<in> ndaStateSem aut nstate 
               \<Longrightarrow> P(out \<Zcat>\<^sup>\<Omega> (spf\<cdot>sb)))"
  and "spf\<in>ndaStateSem aut s"
  shows "P (spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))"
proof-
  obtain spf2 out ns where spf2_def:"spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb) \<and> spf2\<in>ndaStateSem aut ns 
                                     \<and> (ns,out)\<in>(autTransition\<cdot>aut) s sbe"
    by (metis assms(2) conc_sb_def sb_steps_sbe stateSemf_def)
  thus ?thesis
    by(auto simp add: assms)
qed

lemma ndastatesem_step: assumes "spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  shows "\<exists>spf2 output nextState. ((\<forall>sb. spf\<cdot>(sbe\<Zcat>\<^sup>\<surd>sb) = output \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb)) 
    \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) nextState
    \<and> (nextState,output) \<in> (autTransition\<cdot>nda) s sbe)"
proof-
  have spf_in_step: "spf\<in>stateSem_step sb_step nda (ndaStateSem nda) s"
    by (simp add: assms stateSem_stepI)
  thus ?thesis
    apply(auto simp add: assms stateSem_step_def)[1]
    by (metis conc_sb_def)
qed

lemma stateSemOutLen_empty:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaStateSem aut s"
  and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"
  and "chDom TYPE ('In) = {}"  
shows "#\<^sub>\<surd>(spf\<cdot>\<bottom>) = \<infinity>"
proof(rule contrapos_pp,simp+)
  assume a1:"#(spf\<cdot>\<bottom>) \<noteq> \<infinity>"
  have "\<forall>k. Fin k < #(spf\<cdot>\<bottom>)"
  proof(auto)
    fix k::nat
    show "Fin k < #(spf\<cdot>\<bottom>)"
    using assms(1,3)
    proof(induction k arbitrary: spf s)
      case 0                                                                       
      then obtain spf2 ns out where spf2_def:"((spf\<cdot>\<bottom> = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>\<bottom>)) 
      \<and> spf2 \<in> (ndaStateSem aut) ns
      \<and> (ns,out) \<in> (autTransition\<cdot>aut) s (Abs_sbElem None))"
        apply(subgoal_tac "spf\<cdot>(\<bottom>) = spf\<cdot>(Abs_sbElem None \<Zcat>\<^sup>\<surd> \<bottom>)",simp)
        using stateSem_nextspf_def[of spf sb_step aut s]
        apply(simp add: conc_sb_def)
        apply (metis sb_steps_sbe_empty)
        by (metis sb_empty_unfold)
      then have "1\<le>#\<^sub>\<surd>out"
        using assms(2) spf2_def by blast
      then show ?case
        apply(simp add: spf2_def)
        by (metis Fin_02bot gr_0 less2nat_lemma lnzero_def not_one_le_zero 
         one_lnat_def sbHdElem sbHd_reduce sbconctakedrop sbecons_len spf2_def)
    next
      case (Suc k)
      obtain spf2 ns out where spf2_def:"((spf\<cdot>\<bottom> = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>\<bottom>)) 
      \<and> spf2 \<in> (ndaStateSem aut) ns
      \<and> (ns,out) \<in> (autTransition\<cdot>aut) s (Abs_sbElem None))"
        apply(subgoal_tac "spf\<cdot>(\<bottom>) = spf\<cdot>(Abs_sbElem None \<Zcat>\<^sup>\<surd> \<bottom>)",simp)
        using stateSem_nextspf_def[of spf sb_step aut s]
        apply(simp add: conc_sb_def)
        apply (metis Suc.prems(1) sb_steps_sbe sbconc_bot_r)
        by(subst sb_empty_unfold[of \<bottom>],simp_all add: assms)
      then have "1\<le>#\<^sub>\<surd>out"
        using assms(2) spf2_def by blast
      then show ?case
        apply(simp add: spf2_def)
        apply(subgoal_tac "#\<^sub>\<surd>(spf2\<cdot>\<bottom>)+1 \<le> #\<^sub>\<surd>(out \<Zcat>\<^sup>\<Omega> spf2\<cdot>\<bottom>)")
        apply(insert Suc.IH[of spf2 ns],simp_all add: assms spf2_def)
        apply (metis (mono_tags, lifting) Fin_Suc lnat_plus_suc lnsuc_lnle_emb not_less trans_lnle)
        by (metis (no_types, opaque_lifting) add.commute dual_order.trans lessequal_addition order_refl sblen_sbconc)
    qed
  qed
  hence "#\<^sub>\<surd>(spf\<cdot>\<bottom>) = \<infinity>"
    apply(subst lncases[of "#\<^sub>\<surd>(spf\<cdot>\<bottom>)"],simp_all)
    by blast
  thus "False"
    using a1 by simp
qed


declare tlen_len_eq[simp del]
lemma statesem_weak_sb:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaStateSem aut s"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"  
      shows "(#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(spf\<cdot>(input)))"
  apply(cases "chDom TYPE('In) = {}")
  apply simp_all
  apply(subst sbtypeepmpty_sbbot,simp_all add: assms)
  apply(subst stateSemOutLen_empty[where aut= aut and s= s],simp_all add: assms)
  apply(rule statesem_weak_ind [where aut="aut" and step="sb_step" and conv="sbe2sb" and s=s])
  apply(rule sb_ind2,simp_all add: conc_sb_def)
  using assms apply(auto simp add: tlen_len_eq)[4]
  by (metis add.commute lnat_plus_suc refl_lnle)

theorem statesem_weak:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaStateSem aut s"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"  
      shows "weak spf"
  apply(rule weakI)
  apply(rule statesem_weak_sb[where aut=aut and s=s])
  by(simp_all add: assms)

lemma sem_weak_sblen:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaSem aut"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out" 
      shows "#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(spf\<cdot>(input))"
proof(insert assms(1),auto simp add: sem_def)
  fix io::"'Out\<^sup>\<Omega>" and inits::'state and spfa::"'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>"
  assume a0:"spf = (\<Lambda> (sb::'In\<^sup>\<Omega>). io\<Zcat>\<Zcat>spfa\<cdot>sb)"
  assume a1:"spfa \<in> ndaStateSem aut inits"
  hence "#\<^sub>\<surd> input \<le> #\<^sub>\<surd>(spfa\<cdot>input)"
    by(rule statesem_weak_sb[where aut=aut and s=inits],simp add: assms)
  moreover have "#\<^sub>\<surd> (spfa\<cdot>input) \<le> #\<^sub>\<surd> (io\<Zcat>\<Zcat>spfa\<cdot>input)"
    apply(subgoal_tac "spf\<cdot>(input) = io\<Zcat>\<Zcat>spfa\<cdot>input")
    using tlen_conc[of io "spfa\<cdot>input"] apply (simp add: tlen_len_eq)
      apply (metis add.commute add.right_neutral dual_order.trans lessequal_addition
             lnmin_smaller_addition order_refl strict_lnmin_snd)
    by(simp add: a0)
  ultimately show "#\<^sub>\<surd> input \<le> #\<^sub>\<surd> (io\<Zcat>\<Zcat>spfa\<cdot>input)"
    by simp
qed

lemma sem_strong_sblen:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaSem aut"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"
        and "\<And>initOut. initOut \<in> snd ` (autInitConfig\<cdot>aut) \<Longrightarrow> 1 \<le> #\<^sub>\<surd>initOut"
      shows "(lnsuc\<cdot>(#\<^sub>\<surd>input) \<le> #\<^sub>\<surd>(spf\<cdot>input))"
proof(insert assms(1),auto simp add: sem_def)
  fix io::"'Out\<^sup>\<Omega>" and inits::'state and spfa::"'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>"
  assume a1:"spfa \<in> ndaStateSem aut inits"
  assume a2:"(inits, io) \<in> autInitConfig\<cdot>aut"
  have "#\<^sub>\<surd> input \<le> #\<^sub>\<surd>(spfa\<cdot>input)"
    by(rule statesem_weak_sb[where aut=aut and s=inits],simp_all add: a1 assms)
  moreover have " 1 \<le> #\<^sub>\<surd>io"
    using a2 assms(3) by fastforce
  moreover have "lnsuc\<cdot>(#\<^sub>\<surd> (spfa\<cdot>input)) \<le> #\<^sub>\<surd> (io\<Zcat>\<Zcat>spfa\<cdot>input)"
    using tlen_conc[of io "spfa\<cdot>input"] apply (simp add: tlen_len_eq)
    by (metis (no_types, lifting) add.commute calculation(2) dual_order.trans lessequal_addition 
        lnat_plus_suc order_refl tlen_len_eq)
  ultimately show "#\<^sub>\<surd> input <\<^sup>l #\<^sub>\<surd> (io\<Zcat>\<Zcat>spfa\<cdot>input)"
    using lnsuc_lnle_emb trans_lnle by blast
qed

theorem sem_weak:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaSem aut"
    and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"  
      shows "weak spf"
  apply(rule weakI)
  apply(rule sem_weak_sblen[where aut=aut])
  by(simp_all add: assms)
theorem sem_strong:
  fixes aut :: "('state::type, 'In::{tschan,finite} sbElem, 'Out::{tschan,finite} sb) automaton"
  assumes "spf \<in> ndaSem aut"
    and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> 1 \<le> #\<^sub>\<surd>out"  
    and "\<And>initOut. initOut \<in> snd ` (autInitConfig\<cdot>aut) \<Longrightarrow> 1 \<le> #\<^sub>\<surd>initOut"
  shows "strong spf"
  apply(rule strongI)
  apply(rule sem_strong_sblen[where aut=aut])
  by(simp_all add: assms)

declare tlen_len_eq[simp]

end