
theory Automaton

imports inc.Prelude inc.Gfp inc.SetPcpo inc.Classes

begin

default_sort type
declare[[show_consts]]
                                     text\<open>\label{sub:ndaut}\<close>


record ('state::type,'message::type,'out::conc) 
  iAutomaton =
    iautTransition :: "'state \<Rightarrow> 'message \<Rightarrow> (('state \<times> 'out) set)"
    iautInitConfig :: "('state \<times> 'out) set"

cpodef ('state::type,'message::type,'out::conc) automaton =
  "{( autTransition    ::'state \<Rightarrow> 'message \<Rightarrow> (('state \<times> 'out) set)
    , initialConfig ::('state \<times> 'out) set)
      | autTransition initialConfig.
          (\<forall>state sbe. autTransition state sbe \<noteq> {})
        \<and> initialConfig \<noteq> {}}"
  apply auto[1]
  apply (subst UU_eq_empty[symmetric])+
  apply (rule admI)
  apply (simp add: lub_prod)
  apply(intro allI conjI)
  apply (simp_all add: lub_eq_bottom_iff mem_Times_iff)
proof -
  fix Y :: "nat \<Rightarrow> 
  ('state \<Rightarrow> 'message \<Rightarrow> ('state \<times> 'out) set) \<times> ('state \<times> 'out) set" 
  and state :: 'state and sbe :: "'message"
  assume a1: "\<forall>i. (\<forall>state sbe. fst (Y i) state sbe \<noteq> \<bottom>) \<and> 
                               snd (Y i)           \<noteq> \<bottom>"
  assume "chain Y"
  then have "chain (\<lambda>n. fst (Y n))"
    using ch2ch_fst by blast
  then show "(\<Squnion>n. fst (Y n)) state sbe \<noteq> \<bottom>"
    using a1 by (simp add: fun_chain_iff lub_eq_bottom_iff lub_fun)
qed

setup_lifting %invisible type_definition_automaton

lemma repaut_exists:
 "\<exists>f P. Rep_automaton nda = (f, P) \<and> (\<forall>a s. f a s \<noteq> {}) \<and> P \<noteq> {}"
  using Rep_automaton by blast

lemma g_rep_cont[simp, cont2cont]: "cont Rep_automaton"
  using cont_Rep_automaton cont_id by blast
lift_definition autInitConfig::
"('state::type, 'message::type, 'out::conc) automaton \<rightarrow> ('state \<times>'out) set" is
"\<lambda> aut. snd(Rep_automaton aut)"
  by(intro cont2cont)
lemma autinit_nempty [simp]:"autInitConfig\<cdot>aut \<noteq>{}"
  apply(simp add:autInitConfig.rep_eq)
  by (metis repaut_exists snd_conv)

lemma autinit_mono: assumes "aut' \<sqsubseteq> aut"
  shows "(autInitConfig\<cdot>aut') \<subseteq> (autInitConfig\<cdot>aut)"
  by (metis (full_types) SetPcpo.less_set_def assms monofun_cfun_arg)


lift_definition autTransition::
"('state::type, 'message::type, 'out::conc) automaton \<rightarrow> 
    'state \<Rightarrow> 'message \<Rightarrow> (('state \<times> 'out) set)" is
"\<lambda> aut. fst(Rep_automaton aut)"
  by(intro cont2cont)

lemma auttrans_mono: assumes "aut' \<sqsubseteq> aut"
  shows "(autTransition\<cdot>aut') state msg \<subseteq> (autTransition\<cdot>aut) state msg"
  by (metis (full_types) SetPcpo.less_set_def assms fun_below_iff monofun_cfun_arg)

lemma auttrans_nempty[simp]: "(autTransition\<cdot>aut) state sbe \<noteq> {}"
  apply(simp add:autTransition.rep_eq)
  by (metis repaut_exists fst_conv)

lemma automaton_belowI: 
  assumes "\<And>state input. (autTransition\<cdot>aut') state input  
                     \<subseteq> (autTransition\<cdot>aut) state input"
      and "autInitConfig\<cdot>aut' \<subseteq> autInitConfig\<cdot>aut"
    shows "aut' \<sqsubseteq> aut"
  apply(subst below_automaton_def)
  apply(rule prod_belowI)
  apply (metis SetPcpo.less_set_def assms(1) fun_belowI autTransition.rep_eq)
  by (metis SetPcpo.less_set_def assms(2) autInitConfig.rep_eq)


definition chaosComplete::"'a set \<Rightarrow> 'a set" where 
"chaosComplete A \<equiv> if A = {} then UNIV else A"

lift_definition autiChaosComplete::
"('state::type,'message::type, 'out::conc) iAutomaton
  \<Rightarrow>('state::type,'message::type, 'out) automaton " is
"\<lambda>auti. (\<lambda>s m. chaosComplete (iautTransition auti s m), 
        chaosComplete (iautInitConfig auti))"
  by(simp add: chaosComplete_def)



definition defaultComplete::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
"defaultComplete Default A \<equiv> if A = {} then Default else A"

lift_definition autiDefaultComplete::
"('state\<times>'out) \<Rightarrow> ('state::type,'message::type, 'out::conc) iAutomaton
  \<Rightarrow>('state::type,'message::type, 'out) automaton " is
"\<lambda>Default auti. (\<lambda>s m. defaultComplete {Default} (iautTransition auti s m), 
        defaultComplete {Default} (iautInitConfig auti))"
  by(simp add: defaultComplete_def)

lemma "autiDefaultComplete a auti \<sqsubseteq> autiChaosComplete auti"
  apply(rule automaton_belowI)
   apply(simp add: autiDefaultComplete.rep_eq autTransition.rep_eq 
      autiChaosComplete.rep_eq autInitConfig.rep_eq chaosComplete_def defaultComplete_def)+
  done


text\<open>Now that we have a rough overview over the calculation process,
the state-depended semantics can be defined as a greatest fixed point.
For this, the process above is implemented as a @{const gfp} step.\<close>
definition stateSem_step::"(('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type,'msg::type,'out::{conc, pcpo}) automaton
  \<Rightarrow> ('state \<Rightarrow> ('in \<rightarrow> 'out) set) \<Rightarrow> 'state \<Rightarrow> ('in \<rightarrow> 'out) set" where
"stateSem_step step aut h state = 
  (Rep_cfun step) ` {f | f. \<forall>msg. \<exists>output nextState. 
     (nextState,output) \<in> (autTransition\<cdot>aut) state msg
      \<and>  (\<exists> nextSPF. nextSPF \<in> h nextState 
      \<and>  (\<forall>input. f msg\<cdot>input = output \<Zcat>\<Zcat> nextSPF\<cdot>input))}"
text\<open>Then, applying the @{const gfp} operator to 
@{const stateSem_step} of the automaton, defines a function for the
state semantics.\<close>
definition stateSem::"(('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type,'msg::type,'out::{conc, pcpo}) automaton  
  \<Rightarrow> 'state  \<Rightarrow> ('in \<rightarrow> 'out) set" where
"stateSem step aut = gfp (stateSem_step step aut)"


lemma gstatesem_mono[simp]:"mono (stateSem_step step aut)"
  apply(rule monoI)
  apply(simp add: le_fun_def stateSem_step_def)
  by blast

lemma stateSem_stepI:
  assumes "spf \<in> stateSem step aut s"
    shows "spf \<in> stateSem_step step aut (stateSem step aut) s"
  by (metis assms gfp_unfold gstatesem_mono stateSem_def)

lemma stateSemI:
  assumes "spf \<in> stateSem_step step aut (stateSem step aut) s"
    shows "spf \<in> stateSem step aut s"
  by (metis assms def_gfp_unfold gstatesem_mono stateSem_def)

lemma stateSem_unfold:
  "stateSem step aut s = stateSem_step step aut (stateSem step aut) s"
  by (metis def_gfp_unfold gstatesem_mono stateSem_def)

lemma stateSem_bot[simp]:
  assumes "spf \<in> stateSem step aut s"
  and "\<And>f. step\<cdot>f\<cdot>sb = \<bottom>"
shows "spf\<cdot>sb = \<bottom>"
  using assms stateSem_unfold[of step aut s] 
  by(auto simp add: stateSem_step_def)
definition sem::"(('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type,'msg::type,'out::{conc, pcpo}) automaton
  \<Rightarrow> ('in \<rightarrow> 'out) set" where
"sem step aut = {(\<Lambda> sb. initOut \<Zcat>\<Zcat> spf\<cdot>sb) | initOut initState spf.
                    (initState,initOut) \<in> autInitConfig\<cdot>aut 
                      \<and> spf\<in>stateSem step aut initState}"



theorem sem_def_weak: assumes "\<And>conf. conf\<in>autInitConfig\<cdot>aut \<Longrightarrow> snd conf = \<bottom>"
  shows "sem step aut = (\<Union>s\<in>(fst`autInitConfig\<cdot>aut). stateSem step aut s)"
  apply(auto simp add: assms sem_def)[1]
  apply(rule_tac x="(initState, initOut)" in bexI,simp_all)
  using assms botconc1
  apply(subgoal_tac "initOut = \<bottom>",simp)
  using assms  apply auto[1]
  apply(rule_tac x="b" in exI)
  apply(rule_tac x="a" in exI)
  apply(rule_tac x="x" in exI)
  apply(subgoal_tac "b= \<bottom>",simp)
  using assms by auto[1]

lemma sem_bot [simp]:
  assumes "\<And>f. step\<cdot>f\<cdot>\<bottom>=\<bottom>"
      and "spf\<in>(sem step nda)"
    shows "spf\<cdot>\<bottom> \<in> (snd ` (autInitConfig\<cdot>nda))"
  apply(insert assms(2)) unfolding sem_def
  apply auto[1]
  by (metis (no_types, lifting) assms(1) botconc2 image_iff snd_conv stateSem_bot)


definition iSem:: "(('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in::cpo \<rightarrow> 'out)
  \<Rightarrow> ('state::type,'msg::type,'out::{conc, pcpo}) iAutomaton
  \<Rightarrow> ('in \<rightarrow> 'out) set" where
"iSem step iAut = sem step (autiChaosComplete iAut)"



paragraph \<open>Refinement over same states\<close> text\<open>is given when
the transition functions ranges and the initial 
configurations options are cut. This is equivalent to the @{const below}
relation for automaton. Thus, when an automaton is in a @{const below}
relation to another automaton, their semantics are in a @{const subset}
relation.\<close>

lemma statesem_mono_h:
  assumes "\<And>state msg. (autTransition\<cdot>aut') state msg \<subseteq> (autTransition\<cdot>aut) state msg"
  shows "stateSem step aut' \<le> stateSem step aut"
  unfolding stateSem_def
  apply(rule gfp_mono)
  apply(rule le_funI)
  apply (auto simp add: stateSem_step_def)[1]
  using assms by blast

lemma statesem_mono: "monofun (stateSem step)"
  apply(rule monofunI, rule fun_belowI)
  apply(subst less_set_def)
  by (metis SetPcpo.less_set_def monofun_cfun_arg fun_below_iff le_funE statesem_mono_h)

lemma stateSemf_def: assumes "spf\<in>stateSem step aut s" 
  obtains f where "\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>aut) s msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step aut) nextState 
        \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and "spf = step\<cdot>f"
proof-
  have spf_in_step: "spf\<in>stateSem_step step aut (stateSem step aut) s"
    by (simp add: assms stateSem_stepI)
  thus ?thesis
    by(auto simp add: assms stateSem_step_def that)
qed

lemma sem_mono_h: 
  assumes "\<And>state. stateSem step aut' state 
                 \<subseteq> stateSem step aut state"
    and "autInitConfig\<cdot>aut' \<subseteq> autInitConfig\<cdot>aut"
  shows "sem step aut' \<subseteq> sem step aut"
  unfolding sem_def using assms(1) assms(2) by blast

lemma sem_mono: "monofun (sem step)"
  apply(rule monofunI, subst less_set_def)
  apply(rule sem_mono_h)
  apply (metis le_funE auttrans_mono statesem_mono_h)
  by (simp add: autinit_mono)


theorem sem_mono2[simp]: assumes "aut' \<sqsubseteq> aut"
  shows "sem step aut' \<subseteq> sem step aut"
  using sem_mono less_set_def by (metis assms monofunE)

lemma assumes "\<And>state msg. (autTransition\<cdot>aut') state msg 
                         \<subseteq> (autTransition\<cdot>aut) state msg"
         and "autInitConfig\<cdot>aut' \<subseteq> autInitConfig\<cdot>aut"
  shows "sem step aut' \<subseteq> sem step aut"
  by(intro sem_mono2 automaton_belowI; intro assms)

lemma 
  assumes "\<And>state msg. iautTransition auti state msg \<noteq> {} 
                   \<Longrightarrow> iautTransition auti' state msg \<noteq> {}"
      and "\<And>state msg. iautTransition auti state msg \<noteq> {}
                      \<Longrightarrow> iautTransition auti' state msg 
                       \<subseteq> iautTransition auti state msg"
      and "iautInitConfig auti \<noteq> {} \<Longrightarrow> iautInitConfig auti' \<noteq> {}"
      and "iautInitConfig auti \<noteq> {} 
           \<Longrightarrow> iautInitConfig auti' \<subseteq> iautInitConfig auti"
  shows "sem step (autiChaosComplete auti') 
      \<subseteq> sem step (autiChaosComplete auti)"
  apply(intro sem_mono2 automaton_belowI)
  by(auto simp add: autInitConfig.rep_eq autTransition.rep_eq autiChaosComplete.rep_eq chaosComplete_def assms)
  

paragraph \<open>General Refinement\<close>
context
begin
  private       lemma statesem_refine_step:
    assumes "\<And>state msg nextState out. Inv state 
                \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
                \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
        and invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut') state msg
                   \<Longrightarrow> Inv nextState"
        and "\<And>s. Inv s \<longrightarrow> x s \<subseteq> y (f s)"
        and "Inv s"
      shows "stateSem_step step aut' x s \<subseteq> stateSem_step step aut y (f s)"
    apply (auto simp add: image_def stateSem_step_def)[1]
    apply(rule_tac x="xa" in exI)
    by (metis (no_types, opaque_lifting) assms fst_conv imageI subset_iff)

lemma statesem_refine:
    assumes "\<And>state msg nextState out. Inv state 
                \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
                \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
        and invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut') state msg
                   \<Longrightarrow> Inv nextState"
      shows "\<forall>s. Inv s \<longrightarrow> (stateSem step aut' s \<subseteq> stateSem step aut (f s))"
    apply(subst stateSem_def)+
    apply(rule gfp_parallel_induct 
          [where f="stateSem_step step aut'"
             and g="stateSem_step step aut" ])
       apply simp+
    apply(rule allI, rule impI, rule statesem_refine_step [where Inv=Inv]; simp add: assms)
    by auto

theorem statesem_refine_rule:
    assumes "\<And>state msg nextState out. Inv state 
                \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
                \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
        and invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut') state msg
                   \<Longrightarrow> Inv nextState"
        and "Inv s"
      shows "(stateSem step aut' s \<subseteq> stateSem step aut (f s))"
  using statesem_refine[of Inv aut' f aut step]
  by(simp add: assms)


theorem sem_refine_rule:
   assumes "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut' \<Longrightarrow>
                                (f initState, initOut) \<in> autInitConfig\<cdot>aut"
      and "\<And>s. s \<in> fst` autInitConfig\<cdot>aut' \<Longrightarrow> (stateSem step aut' s \<subseteq> stateSem step aut (f s))"
    shows "(sem step aut' \<subseteq> sem step aut)"
   apply(auto simp add: sem_def)[1]
   apply(rule_tac x="initOut" in exI)
   apply(rule_tac x="f initState" in exI)
   apply(rule_tac x="spf" in exI)
  using assms(1) assms(2) by fastforce

lemma state_sem_refine: 
    assumes "\<And>state msg nextState out. 
            (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
        \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
      and "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut'
        \<Longrightarrow> (f initState, initOut) \<in> autInitConfig\<cdot>aut"
    shows "sem step aut' \<subseteq> sem step aut"
  apply(rule sem_refine_rule[where f=f])
   apply(simp add: assms)
  by(rule statesem_refine_rule; simp add: assms)

lemma invariant_sem_refine: 
    assumes "\<And>state msg nextState out. Inv state 
        \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
        \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
      and "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut'
        \<Longrightarrow> (f initState, initOut) \<in> autInitConfig\<cdot>aut"
      and "\<And>state msg nextState. Inv state
         \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut') state msg
         \<Longrightarrow> Inv nextState"
      and "\<And>initState. initState \<in> fst ` (autInitConfig\<cdot>aut')
          \<Longrightarrow> Inv initState"
    shows "sem step aut' \<subseteq> sem step aut"
  apply(rule sem_refine_rule[where f=f])
   apply(simp add: assms)
  apply(rule statesem_refine_rule[where Inv=Inv]; simp add: assms)
  done

end


end
