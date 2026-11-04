theory RefinementSignatureBetter

imports eventautomaton.automaton_stream stream.streamgen

begin

default_sort type



type_synonym state = "nat"

type_synonym in1 = "nat \<times> nat"

type_synonym in2 = "nat"

type_synonym out = "nat stream"


definition transition1::"state \<Rightarrow> in1 \<Rightarrow> (state\<times>out) set" where
"transition1 state input = {(state,\<up>(fst input)), (Suc state, \<up>(Suc (fst input))), (state,<[fst input, snd input]>), (state,\<epsilon>)}"

definition transition2::"state \<Rightarrow> in2 \<Rightarrow> (state\<times>out) set" where
"transition2 state input = {(state, \<up>input), (Suc state, \<up>(Suc input))}"

definition transition3::"state \<Rightarrow> in2 \<Rightarrow> (state\<times>out) set" where
"transition3 state input = {(state, \<up>input)}"

definition init::"(state\<times>out) set" where
"init = {(0,\<up>0)}"


lift_definition aut1::"(state, in1, out) automaton" is
"(transition1, init)"
  by(simp add: init_def transition1_def)

lift_definition aut2::"(state, in2, out) automaton" is
"(transition2, init)"
  by(simp add: init_def transition2_def)

lift_definition aut3::"(state, in2, out) automaton" is
"(transition3, init)"
  by(simp add: init_def transition3_def)








fun transitionMult::"('state \<Rightarrow> 'msg \<Rightarrow> ('state \<times> 'out::{pcpo,conc}) set) \<Rightarrow> 'state \<Rightarrow> 'msg list \<Rightarrow> ('state \<times> 'out) set" where
"transitionMult _ state [] = {(state,\<bottom>)}" |
"transitionMult f state (m#ms) = {(finalState, nextOut \<Zcat>\<Zcat> finalOut) | finalState finalOut nextState nextOut. 
      (nextState,nextOut) \<in> f state m \<and> (finalState,finalOut) \<in> transitionMult f nextState ms}" 

lemma "transitionMult f s [msg] = f s msg"
  by simp

lemma statesem_change_inouttypes_sps:
  fixes inconv::"('in::{cpo,conc} \<rightarrow> 'in'::{cpo,conc})"
    and msgconv::"'msg \<Rightarrow> 'msg' list"
    and step::"('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in \<rightarrow> 'out::{conc, pcpo}"
    and step'::"('msg' \<Rightarrow> 'in' \<rightarrow> 'out) \<rightarrow> 'in' \<rightarrow> 'out"
    and aut::"('s, 'msg, 'out) automaton"
    and aut'::"('s, 'msg', 'out) automaton"

    and shd' :: "'in' \<Rightarrow> 'msg' option"
    and srt' :: "'in' \<rightarrow> 'out"
  assumes step_unfold: "\<And>f msg input. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat> input) = f msg\<cdot>input"
    and  step'_unfold: "\<And>f' msg' input'. step'\<cdot>f'\<cdot>((conv' msg')\<Zcat>\<Zcat> input') = f' msg'\<cdot>input'"

    and    inconv_def: "\<And>msg input. inconv\<cdot>((conv msg) \<Zcat>\<Zcat> input) = (foldr (\<lambda>x xs. (conv' x) \<Zcat>\<Zcat> xs) (msgconv msg) \<bottom>)   \<Zcat>\<Zcat> inconv\<cdot>input"
    and    inconv_bot: "inconv\<cdot>\<bottom> = \<bottom>"

    and  transition_step: "\<And>state nextState msg out. (nextState,out) \<in> transitionMult (autTransition\<cdot>aut') state (msgconv msg) \<Longrightarrow> 
                (nextState, out) \<in> (autTransition\<cdot>aut) state msg"

  shows "(\<lambda>s. (stateSem step' aut' s) ooo {inconv}) \<le> ( stateSem step aut)"
  apply(auto simp add: stateSem_def)
  apply(rule gfp_upperbound)
  apply(rule le_funI)
  unfolding stateSem_def[symmetric]
  apply(subst  stateSem_unfold)

  apply (auto simp add: image_def stateSem_step_def nondet_comp_def)
  apply(rename_tac s f )
  apply(rule_tac x="(\<lambda>m. \<Lambda> input . (let combined = (((conv m) \<Zcat>\<Zcat> input)) in 
    case (undefined combined) of None \<Rightarrow> \<bottom> 
                          | Some x \<Rightarrow> f x\<cdot>(srt'\<cdot>combined)))" in exI)
  apply auto
  sorry



lemma "(\<lambda>s. eStateSem aut2 s ooo {(smap fst)}) \<le> eStateSem aut1"
  unfolding eStateSem_def
  apply(rule statesem_change_inouttypes_sps [where conv="(\<lambda>s. \<up>s)" and conv'="(\<lambda>s. \<up>s)" and msgconv="\<lambda>s. [fst s]"])
      apply simp+
  apply(simp add: autTransition.rep_eq aut2.rep_eq aut1.rep_eq)
  apply(auto simp add: transition1_def transition2_def)
  done


lemma "(\<lambda>s. eStateSem aut3 s ooo {(sscanlAut (\<lambda>_ (a,b). ((), <[a,b]>)) ())}) \<le> eStateSem aut1"
  unfolding eStateSem_def
  apply(rule statesem_change_inouttypes_sps [where conv="(\<lambda>s. \<up>s)" and conv'="(\<lambda>s. \<up>s)" and msgconv="\<lambda>s. [fst s, snd s]"])
    apply auto
  apply(simp add: autTransition.rep_eq aut3.rep_eq aut1.rep_eq)
  apply(auto simp add: transition1_def transition3_def)
  done


lemma "(\<lambda>s. eStateSem aut1 s ooo ndetsmap (\<lambda>s. {(s,p) | p . p\<in>UNIV})) \<le> eStateSem aut3"
  unfolding eStateSem_def
  apply(rule statesem_change_inouttypes_sps [where conv="(\<lambda>s. \<up>s)" and conv'="(\<lambda>s. \<up>s)" and msgconv="\<lambda>s. [(s,s)]"])
  oops


lemma "(\<lambda>s. eStateSem aut3 s ooo {(smap fst) oo (sfilter {(s,s) | s. True})}) \<le> eStateSem aut1"
  unfolding eStateSem_def
  apply(rule statesem_change_inouttypes_sps [where conv="(\<lambda>s. \<up>s)" and conv'="(\<lambda>s. \<up>s)" and msgconv="\<lambda>(a,b). if a = b then [a] else []"])
    apply auto
  apply(simp add: autTransition.rep_eq aut3.rep_eq aut1.rep_eq)
  apply(case_tac "a=b")
  apply(auto simp add: transition1_def transition3_def)
  done








lemma statesem_change_inouttypes_sps:
  fixes inconv::"('in'::{cpo,conc} \<rightarrow> 'in::{cpo,conc})"
    and msgconv::"'msg \<Rightarrow> 'msg' list"
    and step::"('msg \<Rightarrow> 'in \<rightarrow> 'out) \<rightarrow> 'in \<rightarrow> 'out::{conc, pcpo}"
    and step'::"('msg' \<Rightarrow> 'in' \<rightarrow> 'out) \<rightarrow> 'in' \<rightarrow> 'out"
    and aut::"('s, 'msg, 'out) automaton"
    and aut'::"('s, 'msg', 'out) automaton"
  shows "((stateSem step' aut')) \<le> (\<lambda>s.  ((stateSem step aut s )  ooo {inconv}))"
  apply(auto simp add:  stateSem_def)
  apply(rule gfp_parallel_induct [where f = "(stateSem_step step' aut')" and g="(stateSem_step step aut)"])
     apply auto
   apply(rule le_funI)
   apply (auto simp add: stateSem_step_def)
  defer
  oops

lemma "eSem aut2  \<le> eSem aut1 ooo ndetsmap (\<lambda>s. {(s,p) | p . p\<in>UNIV})"
  oops

end