theory PredAutRefine_AutInv

imports stream.Stream automaton.Automaton sps.InvRefinement
      stream.StreamAutomaton
      automaton_testing.Steps automaton_testing.Nda2DaSet

begin
default_sort type

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





lift_definition contextAut::"(nat, unit, nat stream) automaton" is
"((\<lambda>state _. {(n,\<up>n) | n. state \<le>n}), {(n,\<up>n) | n. True})"
  by auto





lift_definition composedAut::"('stateContext, unit, 'in stream) automaton \<Rightarrow> ('state, 'in::countable, 'out::conc) automaton
                        \<Rightarrow> ('stateContext \<times> 'state, unit, 'out) automaton" is
"\<lambda>contextNda nda. ((\<lambda>(stateContext,state) _ . 
      {((nextStateContext,nextState),out) | nextStateContext outContext nextState out. 
          (nextStateContext,outContext) \<in> (autTransition\<cdot>contextNda) stateContext ()
        \<and> (nextState,       out)        \<in> (autTransition\<cdot>nda) state (shd outContext)}) , 
  {((stateContext, state), output) | stateContext state output. (state,output)\<in>autInitConfig\<cdot>nda
                                                      \<and> stateContext \<in> fst ` autInitConfig\<cdot>contextNda})"
  apply auto
  using auttrans_nempty apply (metis equals0I surj_pair) 
  using autinit_nempty by fastforce
  
lemma "#s = 1 \<Longrightarrow> \<exists>msg. s = \<up>msg"
  by (simp add: len_one_stream one_lnat_def)

lemma step_lnat_eq [simp]: assumes "spf\<cdot>\<bottom>=\<bottom>"
  shows "step_lnat\<cdot>(\<lambda>_.spf oo lnsuc) = spf"
  apply(intro cfun_eqI, rename_tac ln)
  apply(case_tac ln rule: lnat.exhaust)
  using assms by auto

lemma context_ref_statesem:
  assumes "\<And>state out. out \<in> snd ` (autTransition\<cdot>contextNda) state () \<Longrightarrow> #out=1"
  shows "(\<lambda>(cs,s). stateSem step_lnat contextNda cs \<then> stateSem stream_step nda s) \<le> stateSem step_lnat (composedAut contextNda nda)"
  apply(subst(3) stateSem_def)
  apply(rule gfp_upperbound)
  apply(intro le_funI, simp add: case_prod_beta)
  apply auto
proof -
  fix s cs spf
  assume as: "spf \<in> stateSem step_lnat contextNda cs \<then> stateSem stream_step nda s"
  obtain cspf and sspf where 
    cspf_in: "cspf\<in>stateSem step_lnat contextNda cs" 
    and sspf_in: "sspf\<in>stateSem stream_step nda s"
      and spf_def: "spf = sspf oo cspf" 
    by(insert as, auto simp add: seqcomp_insert)
  obtain nextStateContext outContext nextContextSPF where 
    c_trans:"(nextStateContext,outContext) \<in> (autTransition\<cdot>contextNda) cs ()"
    and nextcontextspf_in: "nextContextSPF \<in> stateSem step_lnat contextNda nextStateContext"
    and cspf_step: "\<forall>input. cspf\<cdot>(lnsuc\<cdot>input) = outContext \<Zcat>\<Zcat> (nextContextSPF\<cdot>input)"
    using cspf_in stateSemf_def by (smt(verit) step_lnat_lnsuc)
  have "#outContext = 1"
    apply(rule assms(1) [where state="cs"])
    using c_trans image_iff by fastforce
  hence outcontext_def: "outContext = \<up>(shd outContext)" using len_one_stream one_lnat_def by fastforce
  
  obtain nextState out nextSPF where trans: "(nextState,out) \<in> (autTransition\<cdot>nda) s (shd outContext)"
    and nextspf_in: "nextSPF \<in> stateSem stream_step nda nextState"
    and sspf_step: "\<forall>input. sspf\<cdot>(\<up>(shd outContext) \<Zcat> input) = out \<Zcat>\<Zcat> (nextSPF\<cdot>input)"
    using sspf_in stateSemf_def by (smt stream_steps_sbe)
  show "spf \<in> stateSem_step step_lnat (composedAut contextNda nda) (\<lambda>(cs, s). stateSem step_lnat contextNda cs \<then> stateSem stream_step nda s) (cs, s)"
    apply(auto simp add: stateSem_step_def spf_def image_iff)
    apply(rule_tac exI [where x="\<lambda> _ . (sspf oo cspf) oo lnsuc"], auto)
     apply(rule_tac exI [where x="out"])
     apply(rule_tac exI [where x="nextStateContext"], rule_tac exI [where x="nextState"], auto)
      apply(subst autTransition.rep_eq, simp add: composedAut.rep_eq )
    using trans c_trans apply blast
    apply(rule_tac exI [where x=" nextSPF oo nextContextSPF"], auto)
    using nextcontextspf_in nextspf_in seqcomp_insert apply blast
     apply(simp add: cspf_step sspf_step)
     apply(subst outcontext_def, simp add: sspf_step)
    apply(subst step_lnat_eq; simp?)
    using stateSem_bot[OF cspf_in, OF step_lnat_bot]  stateSem_bot[OF sspf_in, OF stream_step_eps] by simp
qed

lemma context_ref_statesem:
  fixes contextNda::"('stateContext, unit, 'inputComp::countable stream) automaton"
      and  nda::"('state, 'inputComp, 'out::conc) automaton"
  assumes "\<And>state out. out \<in> snd ` (autTransition\<cdot>contextNda) state () \<Longrightarrow> #out=1"
  shows "sem step_lnat (composedAut contextNda nda)  
      \<le> sem step_lnat contextNda \<then> sem stream_step nda" (is "?Composed \<le> ?Context \<then> ?Comp")
proof 
  fix spf
  assume spf_in: "spf\<in>?Composed"
  obtain daComposed::"(('stateContext\<times>'state)\<times>(lnat\<rightarrow>'out), unit, 'out) dAutomaton" where 
                    "daSem step_lnat daComposed \<in> ?Composed"
                 and "daComposed \<in> nda2daset (composedAut contextNda nda)"
    apply(insert spf_in)
    apply(subst(asm)(2) nda2daset [where conv="\<lambda>_ . lnsuc\<cdot>\<bottom>"])
    using spf_in apply auto  
    using lnat.induct step_lnat_bot by blast
  obtain daContext::"(('stateContext)\<times>(lnat\<rightarrow>'out), unit, 'inputComp stream) dAutomaton" where
    "daContext = (| dautTransition = undefined, dautInitConfig=undefined |)"
    by simp
  obtain daComp::"('state\<times>(lnat\<rightarrow>'out)\<times>'stateContext, 'inputComp, 'out) dAutomaton" where
    "daComp = (| dautTransition = (\<lambda>(state, spf, stateContext) msg. 
                    (let (((nextStateContext, nextStateComp), nextSpf),out) =  (dautTransition daComposed undefined undefined) in
                          (if((nextStateComp, out) \<in> (autTransition\<cdot>nda) state msg) 
                            then ((nextStateComp,nextSpf,nextStateContext), out)
                            else undefined))), 
                dautInitConfig=undefined |)"
    by simp
  have "daSem step_lnat daContext \<in> ?Context"
    sorry
  have "daSem stream_step daComp \<in> ?Comp"
    sorry
  have "daSem step_lnat daComposed = daSem stream_step daComp oo daSem step_lnat daContext"
    sorry
  show "spf \<in> sem step_lnat contextNda \<then> sem stream_step nda" 
    oops

lemma   assumes "\<And>state out. out \<in> snd ` (autTransition\<cdot>contextNda) state () \<Longrightarrow> #out=1"
  shows "sem step contextNda \<then> sem stream_step nda \<subseteq> sem step (composedAut contextNda nda)"
  apply(subst sem_def)+
  apply(subst autInitConfig.rep_eq)
  apply(auto simp add:  composedAut.rep_eq autInitConfig.rep_eq)
  using context_ref_statesem 
  oops

lemma assumes "invRefined (\<lambda>s. s\<in>(\<lambda>spf. spf\<cdot>()) ` Context) spsSmall spsGreat"
  shows "Context \<then> spsSmall \<subseteq> Context \<then> spsGreat"
  apply(insert assms) apply(auto simp add: seqcomp_insert invRefined_def)
  oops

lemma assumes "\<And>spf. spf \<in> Context \<Longrightarrow> {spf} \<then> spsSmall \<subseteq> {spf} \<then> spsGreat"
  shows "invRefined (\<lambda>s. s\<in>(\<lambda>spf. spf\<cdot>()) ` Context) spsSmall spsGreat"
  apply(rule invRefinedI)
  apply(insert assms, auto simp add: seqcomp_image oo_def image_def)
  oops


theorem aut_context_ref: assumes "0<n"
  shows "invRefined (\<lambda>s. s\<in>(\<lambda>spf. \<up>n \<Zcat> spf\<cdot>()) ` stateSem step_unit contextAut n) (stateSem stream_step (onceGreaterAut n) s) 
                                                                             (stateSem stream_step (greaterThanAut n) ())"
  apply(rule invRefinedI)
  oops

end