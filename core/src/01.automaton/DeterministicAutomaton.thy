theory DeterministicAutomaton
imports Automaton

begin



paragraph \<open>The deterministic automaton\<close>
text\<open>is a special case of automaton. Instead of having transition 
and configuration options, it has a definitive configuration and 
transition. Thus, it represents a completely specified component and
its code. A record very similar to the @{type iAutomaton} record 
describes this perfectly by just not offering the set of possible 
options for transition and configuration.\<close>

record ('state::type,'message::type,'out::conc)
  dAutomaton =
    dautTransition :: "'state \<Rightarrow> 'message \<Rightarrow> 'state\<times>'out"
    dautInitConfig :: "'state \<times> 'out"

definition daStateSem::"
  (('msg::type \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type, 'msg,'out::{conc, pcpo}) dAutomaton 
  \<Rightarrow> 'state \<Rightarrow> ('in \<rightarrow> 'out)" where
"daStateSem step da =
 fix\<cdot>(\<Lambda> h. (\<lambda> state. step\<cdot>
        (\<lambda>sbe. \<Lambda> sb.
           let (nextState, output) = (dautTransition da) state sbe in
                output \<Zcat>\<Zcat> h nextState\<cdot>sb)))"

lemma dastatesem_step: "daStateSem step aut state = step\<cdot>(\<lambda>sbe. \<Lambda> sb.
           let (nextState, output) = (dautTransition aut) state sbe in
                output \<Zcat>\<Zcat> (daStateSem step aut) nextState\<cdot>sb)" 
  apply(subst daStateSem_def)
  apply(subst fix_eq, simp)
  apply(rule cfun_arg_cong, rule fun_eqI, rule cfun_eqI)
  by(simp add: daStateSem_def case_prod_beta' Let_def)

lemma dastatesem_bot [simp]:
  assumes "\<And>f. step\<cdot>f\<cdot>\<bottom>=\<bottom>"
    shows "daStateSem step da s\<cdot>\<bottom> = \<bottom>"
  by(subst dastatesem_step, simp add: case_prod_beta assms)

lemma dastatesem_bot2 [simp]:
  assumes "\<And>f. step\<cdot>f\<cdot>input=\<bottom>"
    shows "daStateSem step da s\<cdot>input = \<bottom>"
  by(subst dastatesem_step, simp add: case_prod_beta assms)

definition daSem::"
  (('msg::type \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type, 'msg,'out::{conc, pcpo}) dAutomaton 
  \<Rightarrow> ('in \<rightarrow> 'out)" where
"daSem step da \<equiv> let (state,out) =dautInitConfig da in
                  (\<Lambda> sb. out \<Zcat>\<Zcat> (daStateSem step da state)\<cdot>sb)"

lemma dasem_unfold:
  shows "daSem step da\<cdot>sb = snd(dautInitConfig da) \<Zcat>\<Zcat> daStateSem step da (fst (dautInitConfig da))\<cdot>sb"
  by(simp add: daSem_def case_prod_unfold Let_def )

lemma dasem_unfold2:
  shows "daSem step da = conc (snd(dautInitConfig da)) oo daStateSem step da (fst (dautInitConfig da))"
  apply(rule cfun_eqI)
  by(simp add: dasem_unfold)

lemma dasem_insert:
  assumes "(state,out) = dautInitConfig da"
  shows "daSem step da\<cdot>sb = out \<Zcat>\<Zcat> daStateSem step da state\<cdot>sb"
  apply(simp add: daSem_def case_prod_unfold Let_def )
  using assms
  by (metis fst_conv snd_conv)

lemma dasem_bot [simp]:
  assumes "\<And>f. step\<cdot>f\<cdot>\<bottom>=\<bottom>"
    shows "daSem step da\<cdot>\<bottom> = snd (dautInitConfig da)"
  unfolding daSem_def 
  by(subst dastatesem_step, simp add: case_prod_beta assms)

lift_definition da2aut::"('state::type,'message::type,'out::conc) dAutomaton 
  \<Rightarrow> ('state::type,'message::type,'out::conc) automaton" is 
"\<lambda>da. (\<lambda>s m. {dautTransition da s m}, {dautInitConfig da}) "
  by simp
definition aut2da::"('state::type,'message::type,'out::conc) automaton
  \<Rightarrow> ('state::type,'message::type,'out::conc) dAutomaton" where 
"aut2da aut = (| dautTransition = (\<lambda>state msg. SOME x. x \<in> (autTransition\<cdot>aut) state msg),
                 dautInitConfig = SOME x. x\<in>autInitConfig\<cdot>aut |)" 

lemma auttransition_nempty[simp]: "(autTransition\<cdot>aut) x msg \<noteq> {}"
  apply(simp add: autTransition.rep_eq)
  using fstI repaut_exists by fastforce

lemma statesem_upper:
  "(\<lambda>s. {daStateSem step (aut2da aut) s}) \<le> stateSem step aut"
  apply(subst stateSem_def)
  apply(rule gfp_upperbound)
  apply(auto simp add: stateSem_step_def image_def le_fun_def less_set_def)[1]
  apply(subst (2) dastatesem_step)
  apply(rule_tac x="(\<lambda>sbe. \<Lambda> sb. let (nextState, output) = dautTransition (aut2da aut) x sbe in output\<Zcat>\<Zcat>daStateSem step (aut2da aut) nextState\<cdot>sb)" in exI)
  apply(auto simp add: Let_def case_prod_beta')[1]
  apply(rule_tac x="snd (dautTransition (aut2da aut) x msg)" in exI)
  apply(rule_tac x="fst (dautTransition (aut2da aut) x msg)" in exI)
  by(simp add: aut2da_def some_in_eq)


theorem statesem_notempty: "stateSem step aut s \<noteq> {}"
proof %visible - 
  have "daStateSem step (aut2da aut) s \<in> stateSem step aut s"
    using statesem_upper le_fun_def by (metis in_mono singletonI)
  thus ?thesis
    by blast
qed

lemma sem_upper:
  "({daSem step (aut2da aut)}) \<le> sem step aut"
  apply(auto simp add: daSem_def sem_def case_prod_unfold Let_def)[1]
  apply(subst aut2da_def,simp)
  apply(subst aut2da_def,simp)
  apply(rule_tac x="snd (SOME x. x\<in> autInitConfig\<cdot>aut)" in exI)
  apply(rule_tac x="fst (SOME x. x\<in> autInitConfig\<cdot>aut)" in exI)
  apply(rule_tac x="daStateSem step (aut2da aut) (fst (SOME x. x \<in> autInitConfig\<cdot>aut))" in exI)
  apply auto[1]
  apply(subst some_in_eq,simp; fail)
  apply(insert statesem_upper[of step aut])
  by (simp add: le_fun_def)

theorem sem_notempty:"sem step aut \<noteq> {}"
  using sem_upper by auto

lemma daseminsem:"(\<lambda>s. {daStateSem step da s}) \<le> stateSem step (da2aut da)"
  apply(subst stateSem_def)
  apply(rule gfp_upperbound)
  apply(auto simp add: stateSem_step_def image_def le_fun_def less_set_def)[1]
  apply(subst (2) dastatesem_step)
  apply(rule_tac x="(\<lambda>sbe. \<Lambda> sb. let (nextState, output) = dautTransition da x sbe in output\<Zcat>\<Zcat>daStateSem step da nextState\<cdot>sb)" in exI)
  apply(auto simp add: Let_def case_prod_beta')[1]
  apply(rule_tac x="snd (dautTransition da x msg)" in exI)
  apply(rule_tac x="fst (dautTransition da x msg)" in exI)
  by(simp add: da2aut.rep_eq autTransition.rep_eq)

lemma autinit_set [simp]:"(autInitConfig\<cdot>(da2aut da)) = {dautInitConfig da}"
  by(simp add: autInitConfig.rep_eq da2aut.rep_eq)

lemma auttrans_set [simp]:"(autTransition\<cdot>(da2aut da)) s i = {dautTransition da s i}"
  by(simp add: autTransition.rep_eq da2aut.rep_eq)

lemma dasseminssem_rule:assumes "\<And>s i. let (ns,out) = (dautTransition da) s i in  (g ns,out) \<in>(autTransition\<cdot>nda) (g s) i"
  shows "daStateSem step da s \<in> stateSem step nda (g s)"
  apply(subgoal_tac "stateSem step (da2aut da) s \<subseteq> stateSem step nda (g s)")
  using daseminsem[of step da] le_funD apply fastforce
  apply(rule statesem_refine_rule[where Inv="\<lambda>s. True"],simp_all)
  using assms
  by (metis case_prodD)

lemma daseminsem_rule:assumes "let (ns,out) = (dautInitConfig da) in  (g ns,out) \<in>(autInitConfig\<cdot>nda)"
  and "let s= fst (dautInitConfig da) in daStateSem step da s \<in> stateSem step nda (g s)"
  shows "daSem step da \<in> sem step nda"
  apply(auto simp add: daSem_def sem_def case_prod_beta' Let_def)[1]
  apply(rule_tac x="snd (dautInitConfig da)" in exI)
  apply(rule_tac x="g (fst (dautInitConfig da))" in exI)
  apply(rule_tac x="daStateSem step da (fst (dautInitConfig da))" in exI)
  using assms by auto

lemma stateSem_eqI:
  assumes "autTransition\<cdot>aut' = autTransition\<cdot>aut"
  shows"stateSem step aut = stateSem step aut'"
  apply(simp add: stateSem_def)
  apply(rule gfp_eqI,simp_all)
  apply (metis (no_types, lifting) antisym assms le_fun_def order_refl stateSem_def stateSem_unfold statesem_mono_h) 
  by (metis assms gfp_upperbound order_class.order_eq_iff stateSem_def statesem_mono_h)

lemma da2autaut2daeq[simp]:
  assumes "\<And>msg state. is_singleton ((autTransition\<cdot>aut) msg state )"
  and "is_singleton (autInitConfig\<cdot>aut)"
  shows"da2aut (aut2da aut) = aut"
  apply(rule below_antisym)
  apply(rule automaton_belowI)
  apply(simp add: aut2da_def autTransition.rep_eq da2aut.rep_eq)
  apply (metis autTransition.rep_eq auttrans_nempty some_in_eq)
  apply(simp add: aut2da_def autInitConfig.rep_eq da2aut.rep_eq)
  apply (metis autInitConfig.rep_eq autinit_nempty some_in_eq)
  apply(rule automaton_belowI)
  using assms
  by(simp add: aut2da_def autInitConfig.rep_eq autTransition.rep_eq da2aut.rep_eq is_singleton_the_elem the_elem_some_eq)+

lemma statesem_da2aut2da[simp]:
  assumes "\<And>msg state. is_singleton ((autTransition\<cdot>aut) msg state)"
  shows "stateSem step (da2aut (aut2da aut)) = stateSem step aut"
  apply(rule stateSem_eqI)
  apply(subst fun_eq_iff)+
  apply auto[1]
   apply(simp_all add: aut2da_def da2aut.rep_eq)
  using assms is_singleton_the_elem the_elem_some_eq 
  apply (metis singletonD) using assms is_singleton_the_elem the_elem_some_eq
  by (simp add: some_in_eq)

lemma sem_da2aut2da[simp]:
  assumes "\<And>msg state. is_singleton ((autTransition\<cdot>aut) msg state )"
  and "is_singleton (autInitConfig\<cdot>aut)"
shows "sem step (da2aut (aut2da aut)) = sem step aut"
  by(simp_all add: assms)


lemma statesem_singleton_h:assumes my_ind:  "\<And>P x::'input::{conc,len}. adm P \<Longrightarrow> (\<And>input. # input = 0 \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
  and step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
  and dumb:"\<And>s input::'input. \<exists>out. \<forall>spf\<in>stateSem step (da2aut da) s. # input = 0 \<longrightarrow> spf\<cdot>input = out"
  shows"is_singleton ((stateSem step (da2aut da) s)::('input\<rightarrow>'output::{conc}) set)"
proof(rule ccontr)
  assume "\<not> is_singleton (stateSem step (da2aut da) s)"
  hence a1:"\<forall>x. stateSem step (da2aut da) s \<noteq> {x}"
    by (auto simp add: is_singleton_def)
  then obtain x y where x_def:"{x,y} \<subseteq> (stateSem step (da2aut da) s)" and xneqy:"x\<noteq>y"
    by (metis empty_subsetI insert_subset is_singletonI' is_singleton_the_elem statesem_notempty)
  then obtain i where i_def:"x\<cdot>i \<noteq>y\<cdot>i"
    using cfun_eqI by auto
  have "x\<cdot>i = y\<cdot>i"
using x_def
proof(induction i arbitrary: x y s rule: my_ind)
  case 1
  then show ?case 
    by auto
next
  case (2 input)
  then obtain out where out_def:"x\<cdot>input = out" and "y\<cdot>input = out"
    using dumb[where input = input and s=s] by fastforce
  then show ?case
    by auto
next
  case (3 msg input)
  hence xspf_in_step: "x\<in>stateSem_step step (da2aut da) (stateSem step (da2aut da)) s"
    by (simp add: stateSem_stepI)
  moreover have yspf_in_step:"y\<in>stateSem_step step (da2aut da) (stateSem step (da2aut da)) s"
    using stateSem_stepI "3.prems" by fastforce
  ultimately obtain f g where f_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(da2aut da)) s msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step (da2aut da)) nextState 
        \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))"
       and x_def: "x= step\<cdot>f"
                             and   g_def: "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>(da2aut da)) s msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step (da2aut da)) nextState 
        \<and>  (\<forall>sb. g msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))"
      and y_def: "y = step\<cdot>g"
    by(auto simp add:stateSem_step_def)
  from this obtain xout xnextState xnextSPF ynextSPF where 
    nextstate_out_def: "(xnextState,xout) \<in> (autTransition\<cdot>(da2aut da)) s msg"
    and nextSPF_in: "xnextSPF \<in> (stateSem step (da2aut da)) xnextState"
    and f_def2: "(\<And> input. f msg\<cdot>input = xout \<Zcat>\<Zcat> xnextSPF\<cdot>input)"
    and nextstate_out_def: "(xnextState,xout) \<in> (autTransition\<cdot>(da2aut da)) s msg"
    and nextSPF_in: "ynextSPF \<in> (stateSem step (da2aut da)) xnextState"
    and g_def2: "(\<And> input. g msg\<cdot>input = xout \<Zcat>\<Zcat> ynextSPF\<cdot>input)"
    apply auto[1] by (metis prod.inject)
  then show ?case
    apply(simp add: x_def y_def step_unfold)
    apply(subst "3.IH"[where y=ynextSPF and s=xnextState])
    by simp+
qed
  show False
    using \<open>x\<cdot>i = y\<cdot>i\<close> i_def by auto
qed


lemma stateSem_lower:assumes "\<And>msg state. is_singleton ((autTransition\<cdot>aut) msg state )"
  and "is_singleton (autInitConfig\<cdot>aut)"
assumes my_ind:  "\<And>P x::'input::{conc,len}. adm P \<Longrightarrow> (\<And>input. # input = 0 \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
  and step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
  and dumb:"\<And>s input::'input. \<exists>out. \<forall>spf\<in>stateSem step (da2aut (aut2da aut)) s. # input = 0 \<longrightarrow> spf\<cdot>input = out"
shows"stateSem step aut \<le> (\<lambda>s. {daStateSem step (aut2da aut) s})"
  apply(subst da2autaut2daeq[symmetric])
  using assms apply(simp,simp)
  apply(insert statesem_singleton_h[of conv step "aut2da aut"])
  apply auto[1]
  apply(simp add: assms(4,5))
  apply(insert assms(3))
  apply(simp add: le_fun_def,auto)
proof -
 fix xa::"'input \<rightarrow> 'c" and x::'a
  assume H1:"\<And>s. (\<And>P x. adm P \<Longrightarrow>
                    (\<And>input. #input = 0 \<Longrightarrow> P input) \<Longrightarrow>
                    (\<And>msg input. P input \<Longrightarrow> P (conv msg\<Zcat>\<Zcat>input)) \<Longrightarrow>
                    P x) \<Longrightarrow>
             (\<And>s input.
                 #input = 0 \<longrightarrow>
                 (\<exists>out. \<forall>spf\<in>stateSem step (da2aut (aut2da aut)) s.
                           spf\<cdot>input = out)) \<Longrightarrow>
             is_singleton (stateSem step (da2aut (aut2da aut)) s)"
  assume H2:"(\<And>P x. adm P \<Longrightarrow>
               (\<And>input. #input = 0 \<Longrightarrow> P input) \<Longrightarrow>
               (\<And>msg input. P input \<Longrightarrow> P (conv msg\<Zcat>\<Zcat>input)) \<Longrightarrow> P x)"
  assume H3:"xa \<in> stateSem step (da2aut (aut2da aut)) x"
  have h1: "\<And>x. is_singleton (stateSem step (da2aut (aut2da aut)) x)"
    using H1 H2 dumb by blast
  have "xa = the_elem (stateSem step (da2aut (aut2da aut)) x)"
    using H3 by (metis h1 is_singleton_the_elem singletonD)
  thus "xa = daStateSem step (aut2da aut) x"
    by (metis (no_types, lifting) H3 assms(1) assms(2) da2autaut2daeq h1 insert_not_empty is_singleton_the_elem le_fun_def singletonD statesem_upper subset_singleton_iff)
qed

lemma stateSem2daStateSem_da:
  assumes my_ind:  "\<And>P x::'input::{conc,len}. adm P \<Longrightarrow> (\<And>input. # input = 0 \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
  and step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
  and dumb:"\<And>s input::'input. \<exists>out. \<forall>spf\<in>stateSem step (da2aut da) s. # input = 0 \<longrightarrow> spf\<cdot>input = out"
shows"stateSem step (da2aut da) s = {daStateSem step da s}"
  apply auto[1]
  apply(insert stateSem_lower[of "da2aut da" conv step])
  apply (simp_all add: assms(2,3) autInitConfig.rep_eq da2aut.rep_eq)
  using assms(1)
  apply (simp add: daseminsem le_fun_def)
proof-
  fix x input
  assume H1: "x \<in> stateSem step (da2aut da) s"
  assume H2: "(\<And>P x. adm P \<Longrightarrow>
               (\<And>input. #input = 0 \<Longrightarrow> P input) \<Longrightarrow>
               (\<And>msg input. P input \<Longrightarrow> P (conv msg\<Zcat>\<Zcat>input)) \<Longrightarrow> P x) \<Longrightarrow>
               (\<And>s input.
                   #input = 0 \<longrightarrow>
                   (\<exists>out. \<forall>spf\<in>stateSem step (da2aut da) s. spf\<cdot>input = out)) \<Longrightarrow>
               \<forall>x. stateSem step (da2aut da) x
                   \<subseteq> {daStateSem step (aut2da (da2aut da)) x}"
  have H3: "\<forall>x. stateSem step (da2aut da) x \<subseteq> {daStateSem step (aut2da (da2aut da)) x}"
      using H2 dumb my_ind by blast
  then have H4: "x \<in> {daStateSem step (aut2da (da2aut da)) s}"
      using H1 by blast
  then have "x = daStateSem step (aut2da (da2aut da)) s"
      by (simp add: singletonD)
  then show  "x = daStateSem step da s"
      by (metis H3 H4 daseminsem insert_not_empty le_fun_def singletonD statesem_notempty subset_singletonD)
next
  show "daStateSem step da s \<in> stateSem step (da2aut da) s"
  apply (metis daseminsem insert_subset le_fun_def)
  done
qed

lemma stateSem2daStateSem_aut:
  assumes my_ind:  "\<And>P x::'input::{conc,len}. adm P \<Longrightarrow> (\<And>input. # input = 0 \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
  and step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
  and dumb:"\<And>s input::'input. \<exists>out. \<forall>spf\<in>stateSem step aut s. # input = 0 \<longrightarrow> spf\<cdot>input = out"
assumes "\<And>msg state. is_singleton ((autTransition\<cdot>aut) msg state )"
  and "is_singleton (autInitConfig\<cdot>aut)"
shows"stateSem step aut s = {daStateSem step (aut2da aut) s}"
  apply(subst da2autaut2daeq[symmetric])
  apply(simp add: assms,simp add: assms)
  apply(rule stateSem2daStateSem_da[where conv=conv])
  apply(simp_all add: assms(2,3))
  using my_ind apply blast
  using assms(4) dumb by fastforce

lemma sem2daSem_aut:
  assumes "is_singleton (autInitConfig\<cdot>aut)"
  and "\<And>s. stateSem step aut s = {daStateSem step (aut2da aut) s}"
shows"sem step aut = {daSem step (aut2da aut)}"
proof-
  obtain inits initout where init_def: "autInitConfig\<cdot>aut = {(inits,initout)}"
    using assms(1) is_singletonE by fastforce
  thus ?thesis
  apply(simp add: sem_def assms daSem_def case_prod_unfold Let_def)
  by(subst(2) aut2da_def,subst(3) aut2da_def, simp)
qed


lemma da2aut_statesem_in[simp]: "daStateSem step da s \<in> stateSem step (da2aut da) s"
proof -
  have "daStateSem step da s \<in> stateSem step (da2aut da) (id s)"
    by(rule dasseminssem_rule [where g=id], simp)
  thus ?thesis by simp
qed

lemma da2aut_sem_in[simp]: "daSem step da \<in> sem step (da2aut da)"
  apply(rule daseminsem_rule [where g=id])
  by(simp add: Let_def)+

lemma da_in_nda:
  fixes da::"('daState, 'msg, 'out::conc) dAutomaton"
    and nda::"('ndaState, 'msg, 'out::conc) automaton"
    and f::"'daState \<Rightarrow> 'ndaState"
  assumes "apfst f (dautInitConfig da) \<in> autInitConfig\<cdot>nda"
      and "\<And>state msg. Inv state \<Longrightarrow> 
        apfst f (dautTransition da state msg) \<in> (autTransition\<cdot>nda) (f state) msg"


      and "Inv (fst (dautInitConfig da))"
      and "\<And>state msg. Inv state \<Longrightarrow> Inv (fst (dautTransition da state msg))"
    shows "daSem step da \<in> sem step nda"
proof - 
  have "sem step (da2aut da) \<subseteq> sem step nda"
    apply(rule sem_refine_rule [where f=f])
     apply simp
     apply (metis apfst_conv assms(1))
    apply(rule statesem_refine_rule [where f=f and Inv=Inv]; simp add: assms)
    by (metis apfst_conv assms(2))
  thus ?thesis
    by (simp add: in_mono) 
qed



fun multTransitionsInOne::"('state, 'msg, 'out::conc) dAutomaton \<Rightarrow> 'state \<Rightarrow> 'msg list \<Rightarrow> ('state \<times> 'out)" where
"multTransitionsInOne da s [] = (s,\<bottom>)" | 
"multTransitionsInOne da s (x#xs) = apsnd (\<lambda> out. snd (dautTransition da s x) \<Zcat>\<Zcat> out) 
                                        (multTransitionsInOne da (fst (dautTransition da s x)) xs)" 

lemma multtransition_split:"multTransitionsInOne da s (ls1 @ ls2) 
  = (let (s1, out1) = multTransitionsInOne da s ls1;
        (s2, out2) = multTransitionsInOne da s1 ls2 in
      (s2, out1 \<Zcat>\<Zcat> out2))"
  by(induction ls1 arbitrary: s ls2; simp add: case_prod_beta Let_def assoc)
  

end