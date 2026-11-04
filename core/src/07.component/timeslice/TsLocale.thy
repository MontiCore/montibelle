theory TsLocale

imports TsAutomaton bundlelocale.SBEGen automaton.RefinementSignature
begin

default_sort chan
declare tlen_len_eq[simp del]


locale tsGen =
  fixes ndaTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable) set"
      and ndaInitConfig:: "'param \<Rightarrow> ('state \<times> 'out::{tschan,finite}\<^sup>\<Omega>) set"
      and fin:: "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenin: "sbeGen fin"
      and sbegenout:"sbeGen fout"
      and completeinit:"\<And>p. ndaInitConfig p \<noteq> {}"
begin

definition transitionC::"'param \<Rightarrow> 'state \<Rightarrow> 'a \<Rightarrow> ('state\<times>'b) set" where
"transitionC p s i \<equiv> if ndaTransition p s i = {} 
                        then UNIV 
                        else ndaTransition p s i"

definition transition::"'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set" where
"transition p state sbe = apsnd (sbe2sb o sbeGen.setter fout)
                              ` transitionC p state (sbeGen.getter fin sbe)"

lift_definition nda::"'param \<Rightarrow> ('state, 'in, 'out\<^sup>\<Omega>) ndAutomaton" is
"\<lambda>param. (transition param, ndaInitConfig param)"
  by(simp add: transition_def transitionC_def completeinit)

abbreviation StateSem:: "'param \<Rightarrow> 'state \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"StateSem param \<equiv> ndaStateSem (nda param)"

abbreviation Sps:: "'param \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"Sps param \<equiv> ndaSem (nda param)"

lift_definition nda_weak_stream::"'param \<Rightarrow> ('state, 'a, 'b stream) automaton" is
"\<lambda>param. ((\<lambda> s m. (apsnd sup') ` (transitionC param s m)), ((\<lambda>(s,_). (s,\<bottom>)) ` ndaInitConfig param))"
  by(simp add: transition_def transitionC_def completeinit)

abbreviation StateSem_weak_stream:: "'param \<Rightarrow> 'state \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"StateSem_weak_stream param \<equiv> stateSem stream_step (nda_weak_stream param)"

lemma completetrans[simp]:"\<And>p s i. transition p s i \<noteq> {}"
  by(simp add: transitionC_def transition_def)

lemma transition[simp]: "autTransition\<cdot>(nda p) = transition p"
  by(simp add: nda.rep_eq autTransition.rep_eq)

lemma trans_fst1: assumes "ndaTransition p state (sbeGen.getter fin msg) \<noteq> {}"
  shows "fst ` (transition p state msg) = fst ` (ndaTransition p state (sbeGen.getter fin msg))"
  by(simp add: transition_def transitionC_def assms image_comp)

lemma trans_fst2: assumes "ndaTransition p state (sbeGen.getter fin msg) = {}"
  shows "fst ` (transition p state msg) = UNIV"
  by(simp add: transition_def transitionC_def assms image_comp)


lemma initconfig[simp]: "autInitConfig\<cdot>(nda p) = ndaInitConfig p"
  by(simp add: autInitConfig.rep_eq nda.rep_eq)


lemma statesem_step: 
  assumes "spf \<in> StateSem p s"
  shows "(\<exists>spf2 output nextState. spf2 \<in> StateSem p nextState 
        \<and> (nextState,output) \<in> transitionC p s a
        \<and> spf\<cdot>((sbeGen.setter fin a) \<Zcat>\<^sup>\<surd> sb) = (sbeGen.setter fout output) \<Zcat>\<^sup>\<surd> spf2\<cdot>sb)"
proof -
  obtain spf2 out nextState where step: "(spf\<cdot>((sbeGen.setter fin a)\<Zcat>\<^sup>\<surd>sb) = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb))" and
      spf2_def: "spf2 \<in> (\<lbrakk>(nda p)\<rbrakk>\<^sup>p) nextState" and
      transition_in: "(nextState,out) \<in> (autTransition\<cdot>(nda p)) s (sbeGen.setter fin a)"
    by (metis assms(1) ndastatesem_step)
  obtain outb where outb_def:"out = sbe2sb (sbeGen.setter fout outb)"
              and transwell:"(nextState,outb) \<in> transitionC p s a"
    using transition_in apply(auto simp add: nda.rep_eq transition_def o_def)[1]
    by (metis sbeGen.get_set sbegenin)
  show ?thesis
    apply(rule_tac x= spf2 in exI)
    apply(rule_tac x= outb in exI)
    apply(rule_tac x= nextState in exI)
    by(simp add: step spf2_def outb_def transwell)
qed

lemma statesem_step_get: 
  assumes "spf \<in> StateSem p s"
  shows "\<exists>spf2 output nextState. spf2 \<in> StateSem p nextState 
      \<and> (nextState,output) \<in> transitionC p s (sbeGen.getter fin sbe)
      \<and> spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = (sbeGen.setter fout output) \<Zcat>\<^sup>\<surd> spf2\<cdot>sb"
  by (metis assms(1) sbeGen.set_get sbegenin statesem_step)

lemma statesem_step_complete: 
  assumes "spf \<in> StateSem p s"
  shows "(\<exists>spf2 output nextState. spf2 \<in> StateSem p nextState 
      \<and> (nextState,output) \<in> transitionC p s a
      \<and> (\<forall>sb. spf\<cdot>((sbeGen.setter fin a) \<Zcat>\<^sup>\<surd> sb) = (sbeGen.setter fout output) \<Zcat>\<^sup>\<surd> spf2\<cdot>sb) )"
proof -
  obtain spf2 out nextState where step: "\<forall>sb. (spf\<cdot>((sbeGen.setter fin a)\<Zcat>\<^sup>\<surd>sb) = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb))" and
      spf2_def: "spf2 \<in> (\<lbrakk>(nda p)\<rbrakk>\<^sup>p) nextState" and
      transition_in: "(nextState,out) \<in> (autTransition\<cdot>(nda p)) s (sbeGen.setter fin a)"
    by (metis assms(1) ndastatesem_step)
  obtain outb where outb_def:"out = sbe2sb (sbeGen.setter fout outb)"
              and transwell:"(nextState,outb) \<in> transitionC p s a"
    using transition_in apply(auto simp add: nda.rep_eq transition_def o_def)[1]
    by (metis sbeGen.get_set sbegenin)
  show ?thesis
    apply(rule_tac x= spf2 in exI)
    apply(rule_tac x= outb in exI)
    apply(rule_tac x= nextState in exI)
    by(simp add: step spf2_def outb_def transwell)
qed


lemma statesem_unfold_pred:
  assumes "\<And>spf out nstate. (nstate,out)\<in> transitionC p s (sbeGen.getter fin sbe) 
               \<Longrightarrow> spf \<in> StateSem p nstate 
               \<Longrightarrow> P((sbeGen.setter fout out) \<Zcat>\<^sup>\<surd> spf\<cdot>sb)"
    and "spf \<in> StateSem p s"
  shows "P (spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))"
proof-
  obtain spf2 out ns where spf2_def:"spf2\<in>StateSem p ns 
                     \<and> (ns,out)\<in>transitionC p s (sbeGen.getter fin sbe)
                     \<and> (spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb)) = (sbeGen.setter fout out) \<Zcat>\<^sup>\<surd> (spf2\<cdot>sb)"
    using assms(2) statesem_step_get  by blast
  thus ?thesis
    by(auto simp add: assms)
qed



lemma ssem_apply_init_step:
  assumes "spf \<in> (Sps p)"
  shows "\<exists>(initState, initOut) \<in> (ndaInitConfig p). \<exists>spf2 \<in> (StateSem p) initState. 
          spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb"
proof-
  obtain spf2 initState initOut  where initstate_initout_def: "(initState, initOut) \<in> (autInitConfig\<cdot>(nda p))"
    and sem2_statesem: "spf2\<in>((\<lbrakk>(nda p)\<rbrakk>\<^sup>p) initState)"
    and sem_apply: "spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb"
    apply(insert ndasem_pred[of spf sb_step "nda p" sb])
    by (metis assms conc_sb_def)
  show "\<exists>(initState::'state, initOut::'out\<^sup>\<Omega>)\<in>ndaInitConfig p. \<exists>spf2::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>\<in>(\<lbrakk>(nda p)\<rbrakk>\<^sup>p) initState. spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb"
    apply(rule_tac x="(initState,initOut)" in bexI,simp)
    apply(rule_tac x="spf2" in bexI)
    apply(simp_all add: sem_apply sem2_statesem)
    by(insert initstate_initout_def,simp)
qed

lemma strongsem_unfold_pred:
  assumes "spf \<in> (Sps p)"
    and "(\<And>spf out nstate. (nstate,out)\<in> (ndaInitConfig p)
               \<Longrightarrow> spf \<in> (StateSem p) nstate        
               \<Longrightarrow> P(out \<Zcat>\<^sup>\<Omega> (spf\<cdot>sb)))"
  shows "P (spf\<cdot>sb)"
proof-
  obtain spf2 initState initOut  where initstate_initout_def: "(initState, initOut) \<in> (autInitConfig\<cdot>(nda p))"
    and sem2_statesem: "spf2\<in>((\<lbrakk>(nda p)\<rbrakk>\<^sup>p) initState)"
    and sem_apply: "spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb"
    apply(insert ndasem_pred[of spf sb_step "nda p" sb])
    by (metis assms(1) conc_sb_def)
  show " P (spf\<cdot>sb)"
    apply(simp add: sem_apply)
    apply(rule assms(2)[of initState])
    apply(insert initstate_initout_def,simp)
    by(simp add: sem2_statesem)
qed

lemma strongsem_unfold_pred2:
  assumes "spf \<in> (Sps p)"
    and "(\<And>spf out nstate. (nstate,out)\<in> (ndaInitConfig p)
               \<Longrightarrow> spf \<in> (StateSem p) nstate        
               \<Longrightarrow> P (\<Lambda> sb. out \<Zcat>\<^sup>\<Omega> (spf\<cdot>sb)))"
  shows "P spf"
proof-
  obtain spf2 initState initOut  where initstate_initout_def: "(initState, initOut) \<in> (autInitConfig\<cdot>(nda p))"
    and sem2_statesem: "spf2\<in>((\<lbrakk>(nda p)\<rbrakk>\<^sup>p) initState)"
    and sem_apply: "spf = (\<Lambda> sb. initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
      using assms(1) apply(simp add: sem_def)
      by (metis conc_sb_def)
  show " P spf"
    apply(simp add: sem_apply)
    apply(rule assms(2)[of initState])
    apply(insert initstate_initout_def,simp)
    by(simp add: sem2_statesem)
qed

lemma weak[simp]:
  assumes "spf \<in> Sps p"
  shows "weak spf"
  apply (rule sem_weak)
  using assms apply simp_all
  apply(auto simp add: transition_def tlen_len_eq)[1]
  by(cases "chDomEmpty TYPE('out)";simp)

lemma weakpred[simp]:
  assumes "spf\<in> Sps p"
  shows "weakpred sb (spf\<cdot>sb)"
  apply(simp add: weakpred_def)
  apply(rule sem_weak_sblen[of _ "nda p"])
  using assms apply simp_all
  apply(auto simp add: transition_def tlen_len_eq)[1]
  by(cases "chDomEmpty TYPE('out)";simp)

(*lemma weakpred_ts[simp]:
  assumes "spf\<in> Sem p"
  shows "weakpred_ts sb (spf\<cdot>sb)"
  apply(simp add: weakpred_ts_def)
  apply(simp add: tlen_len_eq [symmetric])
  by (meson assms weakpred weakpred_def)
*)
lemma weakwell[simp]:
  assumes "spf \<in> Sps p"
  shows "weak spf"
  apply(auto simp add: weak_def)[1]
  apply(rule sem_weak_sblen[of _ "nda p"])
  using assms apply simp_all
  apply(auto simp add: transition_def tlen_len_eq)[1]
  by(cases "chDomEmpty TYPE('out)"; simp)

lemma statesem_weak_len[simp]:
  assumes "\<not>chDomEmpty TYPE('out)"  
      and "spf\<in> StateSem p s"
    shows "#(spf\<cdot>sb) = #sb"
  oops

lemma ndastatesem_bottom_new:
  fixes sb::"'in sb"
  assumes "\<not>sbHdElemWell (sb)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "spf \<in> ndaStateSem (nda param) s \<longrightarrow> spf\<cdot>sb = \<bottom>"
  by (simp add: assms)

(*
proof -
  fix spf and x and m and s
  assume a1:"spf \<in> (stateSem sb_step (nda param)) x"
  then have h1: "ndaTransition param x m \<noteq> {}" 
    apply (simp add: nda_def)
    using assms empty_not_UNIV ndastatesem_bottom_new[where param=param and s=x and spf=spf]
    
    using sbeGen.settersb_strict sbegenin sbeGen.gettersb_realboteps sbegenout
    
    oops

  show "\<exists>(xa::'b) e::'state.
          (e, xa) \<in> ndaTransitionC param x m \<and>
          (\<exists>g::'a stream \<rightarrow> 'b stream.
              (\<exists>spf::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
                  g = sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin \<and> spf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) e) \<and>
              (\<forall>s::'a stream. sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(\<up>m \<Zcat> s))) = \<up>xa \<Zcat> g\<cdot>s))"
   oops
oops
*)
(*
lemma ndastatesem2ndetsscanl_h: 
  assumes "\<not>(chDomEmpty TYPE('in))"
  and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>state. {sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin | spf. spf\<in>(StateSem param) state}) \<le> ndetsscanl (ndaTransition param)"
  apply(subst ndetsscanl_def)
  apply(rule gfp_upperbound)
  apply(rule le_funI,auto)
proof(simp_all add: sbeGen.settersb_strict sbegenin assms ndastatesem_bottom sbeGen.gettersb_realboteps sbegenout StateSem_def)
  fix x spf m s
  assume a1:"spf\<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) x"
  then have h1: "ndaTransition param x m \<noteq> {}" apply (simp add: nda_def)
    by (metis (mono_tags) empty_not_UNIV)
  then obtain out nexts nextf where out_def:"(\<forall>s. (spf\<cdot>(sbeGen.setterSB fin\<cdot>(\<up>m \<Zcat> s))) = out \<Zcat>\<^sup>\<surd> nextf\<cdot>(sbeGen.setterSB fin\<cdot>s)) \<and> 
                                        nextf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) nexts \<and> 
                                        (nexts, sbeGen.getter fout out) \<in> ndaTransitionC param x m"
    using statesem_step_complete
    by (metis StateSem_def a1 sbeGen.get_set sbeGen.settersb_unfold sbegenin sbegenout)
  show "\<exists>(xa::'b) e::'state.
          (e, xa) \<in> ndaTransitionC param x m \<and>
          (\<exists>g::'a stream \<rightarrow> 'b stream.
              (\<exists>spf::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
                  g = sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin \<and> spf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) e) \<and>
              (\<forall>s::'a stream. sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>(\<up>m \<Zcat> s))) = \<up>xa \<Zcat> g\<cdot>s))"
    apply(rule exI [where x="sbeGen.getter fout out"])
    apply(rule exI [where x ="nexts"])
    apply(auto)
    apply(simp add: out_def)
    apply(rule exI [where x="sbeGen.getterSB fout oo nextf oo sbeGen.setterSB fin"],auto)
    apply(rule exI [where x="nextf"], simp add: out_def )
    by (simp add: out_def sbeGen.gettersb_unfold sbegenout)
qed


lemma ndastatesem2ndetsscanl_h2: assumes "spf \<in> (StateSem param) state"
    and "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
  shows "sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin \<in> ndetsscanl (ndaTransitionC param) state"
  apply(insert ndastatesem2ndetsscanl_h[of param],simp add: assms le_fun_def)
  using assms(1) by blast


lemma ndetsscanl_h2ndasem_h: 
  assumes "\<not>(chDomEmpty TYPE('in))"
  and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>state. { sbeGen.setterSB fout oo spf oo sbeGen.getterSB fin| spf. spf \<in>ndetsscanl (ndaTransitionC param) state}) \<le> (StateSem param)"
   apply(simp add: StateSem_def otherStateSem_def)
  apply(rule gfp_upperbound)
  apply simp
proof(rule le_funI,auto)
  fix x::'state and spf::"'a stream \<rightarrow> 'b stream"
  assume a1: "spf \<in>ndetsscanl (ndaTransitionC param) x"
  have h1: "\<And>sbe. \<exists>ns out spf2. (ns,out)\<in>((ndaTransitionC param) x sbe) \<and>
              spf2\<in>(ndetsscanl (ndaTransitionC param) ns) \<and>
              (\<forall>s. spf\<cdot>(\<up>sbe\<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s)"
    proof -
      fix sbe
      show "\<exists>ns out spf2. (ns,out)\<in>((ndaTransitionC param) x sbe) \<and>
              spf2\<in>(ndetsscanl (ndaTransitionC param) ns) \<and>
              (\<forall>s. spf\<cdot>(\<up>sbe\<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s)"
        using ndsscanl_step[of spf "(ndaTransitionC param)" x sbe] a1 by auto
    qed
    obtain fsome where f_def:"fsome = (\<lambda>sbe. SOME prod. (fst prod)\<in>(ndaTransitionC param x sbe) 
                              \<and> (snd prod)\<in> (ndetsscanl (ndaTransitionC param) (fst (fst prod)))
                              \<and> (\<forall>sb. spf\<cdot>(\<up>sbe \<Zcat> sb) = \<up>(snd (fst prod)) \<Zcat> snd(prod)\<cdot>sb))"
    by simp
  have helper:"\<exists>nextstatef outf nextspff .
                 (\<forall>sbe. ((nextstatef sbe, outf sbe) \<in> ndaTransitionC param x sbe) \<and>
                  nextspff sbe \<in> ndetsscanl (ndaTransitionC param) (nextstatef sbe) \<and>
                  (\<forall>sb. spf\<cdot>(\<up>sbe \<Zcat> sb) = \<up>(outf sbe) \<Zcat> (nextspff sbe)\<cdot>sb))"
    apply(rule exI [where x="\<lambda>sbe. fst(fst (fsome sbe))"])
    apply(rule exI [where x="\<lambda>sbe. snd(fst (fsome sbe))"])
    apply(rule exI [where x="\<lambda>sbe. snd(fsome sbe)"],auto simp add:f_def)
    apply(rule p2somep,simp_all)
    using h1 apply blast
    apply(rule p2somep,simp_all)
    using h1 apply blast
    apply(rule p2somep,simp_all)
    using h1 by blast
  then obtain nextstatef outf nextspff where out_def:"
               \<And>sbe. ((nextstatef sbe, outf sbe) \<in> ndaTransitionC param x sbe) \<and>
                nextspff sbe \<in> ndetsscanl (ndaTransitionC param) (nextstatef sbe) \<and>
                (\<forall>sb. spf\<cdot>(\<up>sbe \<Zcat> sb) = \<up>(outf sbe) \<Zcat> (nextspff sbe)\<cdot>sb)"
    by blast
  then obtain f where f_def: "f = (\<lambda>sbe. \<Lambda> sb. sbeGen.setter fout (outf (sbeGen.getter fin sbe)) \<Zcat>\<^sup>\<surd> (sbeGen.setterSB fout\<cdot>(nextspff (sbeGen.getter fin sbe)\<cdot>(sbeGen.getterSB fin\<cdot>sb))))"
    by fastforce
  moreover have h1: "\<And>sbe::'in\<^sup>\<surd>.
       (nextstatef (sbeGen.getter fin sbe), outf (sbeGen.getter fin sbe))
       \<in> ndaTransitionC param x (sbeGen.getter fin sbe)" using out_def by blast
  show "\<exists>f::'in\<^sup>\<surd> \<Rightarrow> 'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
          sbeGen.setterSB fout oo spf oo sbeGen.getterSB fin = sb_step\<cdot>f \<and>
          (\<forall>sbe::'in\<^sup>\<surd>.
              \<exists>(output::'out\<^sup>\<Omega>) (nextSPF::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) nextState::'state.
                 (nextState, output) \<in> (ndAutomaton.ndaTransition\<cdot>(nda param)) x sbe \<and>
                 (\<exists>spf::'a stream \<rightarrow> 'b stream.
                     nextSPF = sbeGen.setterSB fout oo spf oo sbeGen.getterSB fin \<and>
                     spf \<in> ndetsscanl (ndaTransitionC param) nextState) \<and>
                 (\<forall>sb::'in\<^sup>\<Omega>. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb))"
    apply(rule exI[where x="f"],auto)
    apply(rule sbsplit_eqI,simp add: f_def)
    apply (simp add: sbeGen.gettersb_unfold sbegenin out_def)
    using sbeGen.settersb_unfold sbegenout apply blast
    apply(simp)
    apply(subst sbeGen.gettersb_boteps,simp_all add: assms sbegenin)
    using sbnleast_len apply blast
    apply(subst ndsscanl_strict[of spf "ndaTransitionC param" x],simp add: a1)
    apply(simp add: sbegenout sbeGen.settersb_strict)
    apply(rule_tac x="sbe2sb (sbeGen.setter fout (outf (sbeGen.getter fin sbe)))" in exI)
    apply(rule_tac x="sbeGen.setterSB fout oo (nextspff (sbeGen.getter fin sbe)) oo sbeGen.getterSB fin" in exI)
    apply(rule_tac x="nextstatef (sbeGen.getter fin sbe)" in exI)
    apply auto
    apply(simp add: ndaTransition.rep_eq nda.rep_eq transition_def transitionH_def case_prod_unfold)
    apply(subgoal_tac "(nextstatef (sbeGen.getter fin sbe), (outf (sbeGen.getter fin sbe)))
                       \<in>ndaTransitionC param x (sbeGen.getter fin sbe)")
    apply (metis (no_types, lifting) apsnd_conv fst_conv rev_image_eqI snd_conv)
    apply(simp add: h1)
    apply(rule_tac x="nextspff (sbeGen.getter fin sbe)" in exI,auto)
    apply (auto simp add: out_def)
    by(simp add: f_def)  
qed

lemma ndetsscanl_h2ndasem_h2: assumes "spf \<in> ndetsscanl (ndaTransitionC param) state"
    and "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
  shows "sbeGen.setterSB fout oo spf oo sbeGen.getterSB fin \<in> StateSem param state"
  apply(insert ndetsscanl_h2ndasem_h[of param])
  apply(simp add: assms le_fun_def)
  using assms(1) by blast


lemma ndastatesem2ndetsscanl:
  assumes "chDom TYPE('in) \<noteq> {}"
  and "chDom TYPE('out) \<noteq> {}"
  shows"{sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin | spf. spf\<in>(StateSem param state)}
  = ndetsscanl (ndaTransitionC param) state"
 apply auto
   apply (simp add: assms(1) assms(2) ndastatesem2ndetsscanl_h2)
proof-
  fix x::"'a stream \<rightarrow> 'b stream"
  assume a1: "x \<in> ndetsscanl (ndaTransitionC param) state"
  obtain spf where spf_def:"spf = sbeGen.setterSB fout oo x oo sbeGen.getterSB fin"
    by simp
  then have "x= sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin"
    apply(simp add: spf_def)
    apply(rule cfun_eqI)
    apply(simp)
    apply(subst sbeGen.getset_eq)
    apply (simp_all add: sbegenout assms)
    apply(subst sbeGen.getset_eq)
    by (simp_all add: sbegenin assms)
  thus "\<exists>spf::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>. x = sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin \<and> spf \<in> (StateSem param) state"
    apply(subst exI [where x="spf"])
    by (simp_all add: a1 assms(1) assms(2) ndetsscanl_h2ndasem_h2 spf_def)
qed



lemma spfoutinndetsscanlout:
 assumes "spf \<in> StateSem param state"
 and "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
shows "sbeGen.getterSB fout\<cdot>(spf\<cdot>(sbeGen.setterSB fin\<cdot>s)) \<in> 
       ndetsscanlout (ndaTransitionC param) state s"
  by(insert ndastatesem2ndetsscanl_h2[of spf param state],simp add: assms rev_image_eqI ndetsscanlout_def)


lemma ndastatesem2sscanl:
  assumes"\<And>state input. is_singleton (ndaTransitionC param state input)"
  and "spf \<in> StateSem param state"
 and "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
shows "sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin = 
       sscanlAutOne (\<lambda>s m. (SOME x . x \<in> (ndaTransitionC param s m))) state"
  apply(subgoal_tac "sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin \<in> ndetsscanl (ndaTransitionC param) state")
  apply(rule ndsscanl2sscanlaut;simp add: assms)
  using assms(2) ndastatesem2ndetsscanl_h2 by (simp add: assms(3) assms(4))
*)

lemma helping:"sbe2sb (sbeGen.setter fout m) = sbeGen.setterSB fout\<cdot>( sup' m)"
  by (metis sbconc_bot_r sbeGen.settersb_strict sbeGen.settersb_unfold sbegenout
      sconc_snd_empty)

lemma l1_hin:
assumes "\<not>(chDomEmpty TYPE('in))"
and "\<not>(chDomEmpty TYPE('out))"
shows "(\<lambda>s. (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) `  ndaStateSem (nda param) s) \<le> stateSem stream_step (nda_weak_stream param)"
proof -
  have "\<And>sbe sb. sbeGen.getterSB fout\<cdot>((sbe) \<Zcat>\<^sup>\<surd> (sb)) = \<up>(sbeGen.getter fout sbe) \<Zcat> sbeGen.getterSB fout\<cdot>sb"
    using sbeGen.gettersb_unfold[of fout] sbegenout by auto
  hence gettersbFoutUnfold: "\<And>sbeAsSb sb. sbeGen.getterSB fout\<cdot>((sbe2sb sbeAsSb) \<Zcat>\<Zcat> (sb)) = \<up>(sbeGen.getter fout sbeAsSb) \<Zcat> sbeGen.getterSB fout\<cdot>sb"
    by (simp add: conc_sb_def)
  show "(\<lambda>s.(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) `
        (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) s) \<le> StateSem_weak_stream param"
    apply(rule sem_change_inouttypes[where msgconv="sbeGen.setter fin"],auto)
    apply(subst sb_step2stream_step,simp_all add: assms oo_def)
    apply (rule sbegenin)
    apply (rule sbegenout) 
    apply(simp add: nda_weak_stream.rep_eq autTransition.rep_eq transition_def)
    using helping apply auto
    defer
    apply(simp add: transition_def)
    proof -
      fix b::"'out\<^sup>\<Omega>"  and s::"'state" and m::"'in\<^sup>\<surd>" and aa::'state and ba::"'out\<^sup>\<Omega>"
      assume "(aa, ba) \<in> apsnd (sbe2sb \<circ> sbeGen.setter fout) ` transitionC param s (sbeGen.getter fin m)"
      then obtain baSBE where baSbeDef: "ba = sbe2sb baSBE"
        by auto
      have "\<up>(sbeGen.getter fout baSBE) = sbeGen.getterSB fout\<cdot>ba"
        by (metis assms(2) baSbeDef botconc2 gettersbFoutUnfold sbeGen.gettersb_realboteps sbegenout sconc_snd_empty)
      thus "sbeGen.getterSB fout\<cdot>(ba\<Zcat>\<Zcat>b) = sbeGen.getterSB fout\<cdot>ba \<Zcat> sbeGen.getterSB fout\<cdot>b"
        apply (subst baSbeDef)
        apply (subst gettersbFoutUnfold[of baSBE b])
        by auto
    next 
      fix s1 and s2 and m and b
      assume "(\<And>m::'b. sbe2sb (sbeGen.setter fout m) = sbeGen.setterSB fout\<cdot>(\<up>m))" and "(s2, b) \<in> transitionC param s1 (sbeGen.getter fin (sbeGen.setter fin m))"
      show "(s2, sbeGen.getterSB fout\<cdot>(sbeGen.setterSB fout\<cdot>(\<up>b))) \<in> apsnd sup' ` transitionC param s1 m"
        apply auto[1]
        by (metis
            \<open>(s2::'state, b::'b) \<in> transitionC (param::'param) (s1::'state) (sbeGen.getter (fin::'a \<Rightarrow> 'in \<Rightarrow> M) (sbeGen.setter fin (m::'a)))\<close>
            apsnd_conv assms(2) image_iff sbeGen.get_set sbeGen.getset_eq sbegenin sbegenout)
    qed
qed

lemma l1_rueck:
assumes "\<not>(chDomEmpty TYPE('in))"
and "\<not>(chDomEmpty TYPE('out))"
shows "stateSem stream_step (nda_weak_stream param) \<le> (\<lambda>s. (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) `  ndaStateSem (nda param) s)"
  (* have h:" (\<lambda>s. (\<lambda>f. sbeGen.setterSB fout oo f oo sbeGen.getterSB fin) ` StateSem_weak_stream param s) \<le> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p)"
  apply(rule sem_change_inouttypes)
  oops *)
  (* 
  apply (rule le_funI)
  proof(auto)
    fix x xa
    assume a1:" xa \<in> StateSem_weak_stream param x"
    obtain spf where spf_def:"spf = sbeGen.setterSB fout oo xa oo sbeGen.getterSB fin "
        and "spf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) x"
    oops
    show "xa \<in> (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) ` (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) x"
      apply(subgoal_tac "sbeGen.setterSB fout oo xa oo sbeGen.getterSB fin \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) x")
      oops 
  *)
  oops

lemma l1_hin_alt:
  assumes "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s \<le> stateSem stream_step (nda_weak_stream param) s"
  using assms l1_hin
  by (simp add: le_fun_def)

lemma sem2streamsem_step_rule:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))" 
      and "\<And>spf. spf\<in> StateSem_weak_stream param s \<Longrightarrow> P i (spf\<cdot>i)"
      and "spf2 \<in> StateSem param s"
    shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
  proof -
    have "sbeGen.getterSB fout oo spf2 oo sbeGen.setterSB fin \<in> (\<lambda>c. sbeGen.getterSB fout oo c oo sbeGen.setterSB fin) ` (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) s"
      using assms(4) by blast
    then have "P i ((sbeGen.getterSB fout oo spf2 oo sbeGen.setterSB fin)\<cdot>i)"
      using assms(1) assms(2) assms(3) l1_hin_alt by blast
    then show ?thesis
      by simp
  qed

lemma 
assumes "chDomEmpty TYPE('in)"
  and "chDomEmpty TYPE('out)" 
  and "\<And>spf. spf\<in> StateSem_weak_stream param s \<Longrightarrow> P i (spf\<cdot>i)"
  and "spf2 \<in> StateSem param s"
shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
oops

lemma l1_h:
assumes "\<not>(chDomEmpty TYPE('in))"
and "\<not>(chDomEmpty TYPE('out))"
shows "(\<lambda>s. (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) `  ndaStateSem (nda param) s) = stateSem stream_step (nda_weak_stream param)"
  (* proof(rule antisym)
    show "(\<lambda>s.(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) `
          (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) s) \<le> StateSem_weak_stream param"
      using l1_hin assms by auto
  next
    show "StateSem_weak_stream param
      \<le> (\<lambda>s::'state.
             (\<lambda>f::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) `
             (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) s)"
      (*using l1_rueck assms by auto*)
    oops
    oops
  *)
  oops

lemma l1:
  assumes "\<not>(chDomEmpty TYPE('in))"
  and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s = stateSem stream_step (nda_weak_stream param) s"
  (*using l1_h by (metis assms(1,2))*)
  oops

end



lemma ndatransition_gen_ref2: 
  fixes f :: "'a::type \<Rightarrow> 'b::type"
    and trans1 :: "'p::type \<Rightarrow> 'a \<Rightarrow> 'd::countable \<Rightarrow> ('a \<times> 'e::countable) set"
    and init1::"'p \<Rightarrow> ('a \<times> _) set"
    and   fout :: "'e \<Rightarrow> 'g::{tschan,finite} \<Rightarrow> M"
    and trans2 :: "'p \<Rightarrow> 'b \<Rightarrow> 'd::countable \<Rightarrow> ('b \<times> 'e::countable) set"
    and init2::"'p \<Rightarrow> ('b \<times> _) set"
  assumes "\<And>state port t out. Inv state \<Longrightarrow> (t,out) \<in> (trans1 param state port) 
          \<Longrightarrow> (f t,out) \<in> (trans2 (g param) (f state) port) \<or> trans2 (g param) (f state) port = {}"
  and "\<And> state port. Inv state \<Longrightarrow> trans1 param state port = {} \<Longrightarrow>  trans2 (g param) (f state) port = {}"
  and ndagen1: "tsGen init1 fin fout"
  and ndagen2: "tsGen init2 fin fout"  and "Inv state"
  and "(t, out) \<in> (tsGen.transition trans1 fin fout) param state port"
shows "(f t, out) \<in> (tsGen.transition trans2 fin fout) (g param) (f state) port"
  apply(insert tsGen.transition_def[of init1 fin fout trans1 param state port])
  apply(insert tsGen.transition_def[of init2 fin fout trans2 "g param" "f state" port])
  apply(insert assms) apply(simp add: assms)  
  apply(insert tsGen.transitionC_def[of init1 fin fout trans1 param state ])
  apply(insert tsGen.transitionC_def[of init2 fin fout trans2 "g param" "f state" ])
  apply(simp add: assms)
  apply auto[1]
  by (metis (no_types) apsnd_conv assms(1) assms(2) assms(5) comp_apply empty_iff imageI)

theorem ndastaterefine_inv__ndagen:
  fixes f :: "'a::type \<Rightarrow> 'b::type"
    and trans1 :: "'p::type \<Rightarrow> 'a \<Rightarrow> 'd::countable \<Rightarrow> ('a \<times> 'e::countable) set"
    and init1::"'p \<Rightarrow> ('a \<times> _) set"
    and fout :: "'e \<Rightarrow> 'g::{tschan,finite} \<Rightarrow> M"
    and trans2 :: "'p \<Rightarrow> 'b \<Rightarrow> 'd::countable \<Rightarrow> ('b \<times> 'e::countable) set"
    and init2::"'p \<Rightarrow> ('b \<times> _) set"
  assumes "\<And>s sbe t out. Inv s \<Longrightarrow> (t, out) \<in> (trans1 p s sbe) \<Longrightarrow>
            (f t, out)  \<in> (trans2 (g p) (f s) sbe) \<or> (trans2 (g p) (f s) sbe) = {}"
  and "\<And>s sbe. Inv s \<Longrightarrow> (trans1 p s sbe) = {} \<Longrightarrow> (trans2 (g p) (f s) sbe) = {}"
  and ndagen1: "tsGen init1 fin fout"
  and ndagen2: "tsGen init2 fin fout"
  and invariant: "\<And>p currentState input nextState. Inv currentState
                 \<Longrightarrow> nextState \<in> fst ` trans1 p currentState input
                 \<Longrightarrow> Inv nextState"
  and invariant2: "\<And>p currentState input nextState. Inv currentState
                 \<Longrightarrow> trans1 p currentState input = {}
                 \<Longrightarrow> Inv nextState"
  and "Inv state"
shows "(tsGen.StateSem trans1 init1 fin fout p state ) \<subseteq>
         (tsGen.StateSem trans2 init2 fin fout (g p) (f state))"
proof(rule statesem_refine_rule [where Inv=Inv])
  fix state msg nextState out
  assume inv:"Inv state" 
    and "(nextState, out) \<in> (autTransition\<cdot>(tsGen.nda trans1 init1 fin fout p)) state msg"
  hence prev: "(nextState, out) \<in> ((tsGen.transition trans1 fin fout p) state msg)"
    by (simp add: tsGen.transition ndagen1)
  have "(f nextState, out) \<in> ((tsGen.transition trans2 fin fout (g p)) (f state) msg)"
    apply(rule ndatransition_gen_ref2 [of Inv trans1  p _  _  _  init1 _ _ init2])
    by (simp_all add: assms(1-5) inv prev )
  thus "(f nextState, out) \<in> (autTransition\<cdot>(tsGen.nda trans2 init2 fin fout (g p))) (f state) msg"
    by (simp add: tsGen.transition ndagen2)
next
  fix state msg nextState
  assume inv:"Inv state" 
      and "nextState \<in> fst ` (autTransition\<cdot>(tsGen.nda trans1 init1 fin fout p)) state msg"
  hence "nextState \<in> fst ` ((tsGen.transition trans1 fin fout p)) state msg"
    by (simp add: tsGen.transition ndagen1)
  thus "Inv nextState" 
    apply(cases "trans1 p state (sbeGen.getter fin msg) = {}")
    using tsGen.trans_fst2 ndagen1 inv invariant2 apply auto[1]
    using tsGen.trans_fst1 ndagen1 inv invariant by metis
next
  show "Inv state" by (simp add: assms(7))
qed


lemma ndastaterefineinv_ndagen_sem:
  fixes f :: "'a::type \<Rightarrow> 'b::type"
    and trans1 :: "'p::type \<Rightarrow> 'a \<Rightarrow> 'd::countable \<Rightarrow> ('a \<times> 'e::countable) set"
    and init1::"'p \<Rightarrow> ('a \<times> _) set"
    and fout :: "'e \<Rightarrow> 'g::{tschan,finite} \<Rightarrow> M"
    and trans2 :: "'p \<Rightarrow> 'b \<Rightarrow> 'd::countable \<Rightarrow> ('b \<times> 'e::countable) set"
    and init2::"'p \<Rightarrow> ('b \<times> _) set"
  assumes "\<And>s. Inv s \<Longrightarrow> tsGen.StateSem trans1 init1 fin fout p s \<subseteq>
       tsGen.StateSem trans2 init2 fin fout (g p) (f s)"
  and "\<And>s out. (s,out)\<in>(init1 p) \<Longrightarrow> (f s,out)\<in>(init2 (g p))"
  and "\<And>s. s \<in> (fst ` init1 p) \<Longrightarrow> Inv s"
  and ndagen1: "tsGen init1 fin fout"
  and ndagen2: "tsGen init2 fin fout"
shows "tsGen.Sps trans1 init1 fin fout p \<subseteq>
       tsGen.Sps trans2 init2 fin fout (g p)"
  apply(rule sem_refine_rule [where f=f])
   apply(simp add: tsGen.initconfig ndagen1 ndagen2 assms(2))
  by (simp add: assms(1) assms(3) tsGen.initconfig ndagen1)


locale tsWeakGen =
  fixes ndaTransition::   "'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                            \<Rightarrow> ('state\<times>'b::countable) set"
      and ndaInitConfig:: "'param \<Rightarrow> 'state set"
      and fin::           "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::          "'b::countable \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes sbegenfin:      "sbeGen fin"
      and sbegenfout:     "sbeGen fout"
begin

abbreviation initConfigC::"'param \<Rightarrow> 'state set" where
"initConfigC param \<equiv> if ndaInitConfig param = {} 
                            then UNIV 
                            else ndaInitConfig param"

definition initConfig::"'param \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set" where
"initConfig p = (\<lambda>out. (out,\<bottom>)) ` initConfigC p"

end

sublocale tsWeakGen \<subseteq> tsGen ndaTransition initConfig fin fout
  by (simp add: tsGen_def sbegenfin sbegenfout initConfig_def)

context tsWeakGen begin

lift_definition ndaw_stream::"'param \<Rightarrow> ('state, 'a, 'b stream) automaton" is
"\<lambda>param. ((\<lambda> s m. (apsnd sup') ` (transitionC param s m)), ((\<lambda>s. (s,\<bottom>)) ` initConfigC param))"
  by(simp add: transition_def transitionC_def completeinit)

abbreviation StateSemw_stream:: "'param \<Rightarrow> 'state \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"StateSemw_stream param \<equiv> stateSem stream_step (ndaw_stream param)"

abbreviation Spsw_stream:: "'param \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"Spsw_stream param \<equiv> sem stream_step (ndaw_stream param)"

lemma sem_def2: "Sps p = (\<Union>s\<in>initConfigC p. StateSem p s)"
  apply(subst sem_def_weak)
  by(auto simp add: initConfig_def)

lemma weaksem_unfold_pred:
  assumes "spf \<in> Sps p"
    and "\<And>spf out nstate. nstate \<in> initConfigC p
               \<Longrightarrow> spf \<in> StateSem p nstate        
               \<Longrightarrow> P (spf\<cdot>sb)"
  shows "P (spf\<cdot>sb)"
  using assms(1) assms(2) sem_def2 by auto

lemma weaksem_unfold_pred2:
  assumes "spf \<in> Sps p"
    and "\<And>spf out nstate. nstate \<in> initConfigC p
               \<Longrightarrow> spf \<in> StateSem p nstate        
               \<Longrightarrow> P spf"
  shows "P spf"
  using assms(1) assms(2) sem_def2 by auto


lemma StateSem_weak2StateSem[simp]:"StateSem_weak_stream = StateSemw_stream"
  by(simp add: nda_weak_stream_def ndaw_stream_def initConfig_def image_image)


lemma wsem2streamsem_step_rule:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))" 
      and "\<And>spf. spf\<in> StateSemw_stream param s \<Longrightarrow> P i (spf\<cdot>i)"
      and "spf2 \<in> StateSem param s"
    shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
  using sem2streamsem_step_rule StateSem_weak2StateSem assms
  by metis

lemma wl1_hin: 
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
    shows "(\<lambda>s. (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` StateSem param s) \<le> StateSemw_stream param"
  apply(insert l1_hin[where param=param])
  apply(simp add: assms)
  using StateSem_weak2StateSem
  by metis

lemma wl1_hin_alt: 
  assumes "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s \<le> stateSem stream_step (ndaw_stream param) s"
  using StateSem_weak2StateSem assms l1_hin_alt
  by metis


lemma wl2_hin: 
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
    shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) ` Sps param \<le> sem stream_step (ndaw_stream param)"
  apply (simp add: sem_def)
  apply auto
proof -
  fix initOut initState spf
  assume asm1: "(initState, initOut) \<in> initConfig param"
  assume asm2: "spf \<in> StateSem param initState"

  from asm1 obtain state_in where 
    state_in_def: "state_in \<in> initConfigC param" and
    pair_eq: "(initState, initOut) = (state_in, \<bottom>)"
    by (auto simp add: initConfig_def)

  from pair_eq have initState_eq: "initState = state_in" and initOut_empty: "initOut = \<bottom>"
    by simp_all

  obtain spf2 where spf2_def: "spf2 \<in> StateSemw_stream param initState" 
              and spf2_attr: "sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin = spf2"
    using asm2 assms wl1_hin_alt by blast

  have initState_in_config: "(initState, \<bottom>) \<in> autInitConfig\<cdot>(ndaw_stream param)"
  proof -
    have "autInitConfig\<cdot>(ndaw_stream param) = (\<lambda>s. (s, \<bottom>)) ` initConfigC param"
      by (simp add: autInitConfig.rep_eq ndaw_stream.rep_eq)
    then show ?thesis
      using state_in_def initState_eq by auto
  qed

  show "(initState, initOut) \<in> initConfig param \<Longrightarrow>
       spf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) initState \<Longrightarrow>
       \<exists>(initOuta::'b stream) (initState::'state) spfa::'a stream \<rightarrow> 'b stream.
          sbeGen.getterSB fout oo (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut\<Zcat>\<Zcat>spf\<cdot>sb) oo sbeGen.setterSB fin =
          (\<Lambda> (sb::'a stream). initOuta \<Zcat> spfa\<cdot>sb) \<and>
          (initState, initOuta) \<in> autInitConfig\<cdot>(ndaw_stream param) \<and>
          spfa \<in> StateSemw_stream param initState"
    apply(simp add: asm1 asm2)
    apply (rule_tac x="\<bottom>" in exI)
    apply (rule_tac x="initState" in exI)  
    apply (rule_tac x="spf2" in exI)
    apply (auto simp add: spf2_def initState_in_config)
    apply (rule cfun_eqI)
    apply (simp add: spf2_attr initOut_empty)
    done
qed


lemma wsem2streamsem_rule:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
  assumes "\<And>spf. spf\<in> sem stream_step (ndaw_stream param) \<Longrightarrow> P i (spf\<cdot>i)"
      and "spf2 \<in> Sps param"
    shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
proof -  
  have "sbeGen.getterSB fout oo spf2 oo sbeGen.setterSB fin \<in> 
        (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin) ` Sps param"
    using assms(4) by blast
  
  then have "sbeGen.getterSB fout oo spf2 oo sbeGen.setterSB fin \<in> Spsw_stream param"
    using wl2_hin[OF assms(1,2)] by auto
  
  then have "P i ((sbeGen.getterSB fout oo spf2 oo sbeGen.setterSB fin)\<cdot>i)"
    using assms(3) by blast
  
  then show ?thesis by simp
qed


lemma wl1:"(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s = stateSem stream_step (ndaw_stream param) s" 
  (* using l1 by (metis StateSem_weak2StateSem) *)
  oops

lemma l2:"(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` Sps param = sem stream_step (ndaw_stream param)"
  (*apply(auto)*)
  oops


lemma sem_weak_len[simp]:
  assumes "\<not>chDomEmpty TYPE('out)"  
      and "spf\<in> Sps p"
  shows "#(spf\<cdot>sb) = #sb"
  oops
(*
  apply (rule ndasem_weak_len2 [of "nda p"])
  using assms apply (simp_all)
  apply (auto simp: ndaTransition.rep_eq nda.rep_eq transition_def)[1]
  by (auto simp add: ndaInitConfig_def nda.rep_eq initConfig_def)
*)

lemma statesemw_stream_step:
  assumes"spf\<in> StateSemw_stream param state"
  shows"\<exists>nspf ns out. spf\<cdot>(\<up>a \<Zcat> s) = \<up>out \<Zcat> nspf\<cdot>s \<and> nspf\<in> StateSemw_stream param ns \<and> (ns,out) \<in> (transitionC param state a)"
proof -
  have helper:"(autTransition\<cdot>(nda_weak_stream param)) state a = apsnd sup' ` transitionC param state a"
    by(simp add: autTransition.rep_eq nda_weak_stream.rep_eq)
  obtain nspf out ns where step: "spf\<cdot>(\<up>a \<Zcat> s) = out \<Zcat> nspf\<cdot>s" and
      spf2_def: "nspf\<in> StateSemw_stream param ns" and
      transition_in: "(ns,out) \<in> (autTransition\<cdot>(nda_weak_stream param)) state a"
    by (metis StateSem_weak2StateSem assms conc_stream_def
        stateSemf_def[of "spf::'a stream \<rightarrow> 'b stream"
          stream_step "tsGen.nda_weak_stream
        (ndaTransition::'param \<Rightarrow> 'state \<Rightarrow> 'a \<Rightarrow> ('state \<times> 'b) set)
        (tsWeakGen.initConfig (ndaInitConfig::'param
       \<Rightarrow> 'state set)) (param::'param)"
          "state::'state"] stream_steps_sbe[of _ "a::'a"
          "s::'a stream"])
  then have "\<exists>m. out = \<up>m"
    using transition_in apply(simp add: helper)
    by fastforce
  then obtain  outb where
    outb_def :"out = \<up>outb" and
    transwell: "(ns, outb) \<in> transitionC param state a"
    using transition_in apply(simp add: helper)
    by force
  show ?thesis 
    apply (rule_tac x = nspf in exI)
    apply (rule_tac x= ns in exI)
    apply (rule_tac x= outb in exI)
    using spf2_def outb_def transwell step
    by simp

qed
lemma semw_stream_apply_init_step:
  assumes "spf \<in> Spsw_stream param"
  shows "\<exists>initState \<in> (initConfigC param). \<exists>spf2 \<in> (StateSemw_stream param initState). spf\<cdot>s = spf2\<cdot>s "
proof -
  obtain nspf Initout  Initstate where step: "spf\<cdot>(s) = Initout \<Zcat> nspf\<cdot>s" and
      nspf_def: "nspf\<in> StateSemw_stream param Initstate" and
      transition_def: "(Initstate,Initout) \<in> (autInitConfig\<cdot>(ndaw_stream param))" 
    by (metis assms conc_stream_def ndasem_pred)


  have initOut_value: "Initout = \<epsilon>"    using transition_def  ndaw_stream.rep_eq
    by (simp add: autInitConfig.rep_eq image_iff transition_def  ndaw_stream.rep_eq)
 

  show ?thesis
    apply(rule_tac x="Initstate" in bexI)
    apply(rule_tac x="nspf" in bexI)
    apply (simp add: initOut_value step)
     apply (simp add: nspf_def) 
    apply auto
  proof -
    fix x :: 'state
    assume a1: "Initstate \<notin> ndaInitConfig param"
    assume "x \<in> ndaInitConfig param"
    then have "ndaInitConfig param \<noteq> {}"
      by blast
    then have "(\<lambda>s. (s, \<epsilon>)) ` ndaInitConfig param = snd (Rep_automaton (ndaw_stream param))"
      by (simp add: ndaw_stream.rep_eq)
    then have "(Initstate, Initout) \<in> (\<lambda>s. (s, \<epsilon>)) ` ndaInitConfig param"
      by (metis (no_types) autInitConfig.rep_eq transition_def)
    then show False
      using a1 by blast
  qed
qed

lemma streamstatesem_len: assumes "spf\<in> StateSemw_stream param state"
  shows " #(spf\<cdot>i) = #i"
  using assms
proof (induction i arbitrary:spf param state)
  case adm
  then show ?case by (simp add: len_stream_def)
next
  case bottom
  then show ?case   
    by simp
next
  case (step a s)
  from this show ?case
    by (metis slen_scons step statesemw_stream_step) 
qed

lemma streamsem_len[simp]: assumes "spf\<in> Spsw_stream param"
  shows " #(spf\<cdot>i) = #i"
  apply (simp add: len_stream_def)
proof -
    obtain nspf initState where step: "spf\<cdot>(i) = nspf\<cdot>i" and
      nspf_def: "nspf\<in> StateSemw_stream param initState"
      using semw_stream_apply_init_step assms
      by blast
    have "spf\<cdot>i = nspf\<cdot>i"
      by (simp add: local.step)
    have "slen\<cdot>(nspf\<cdot>i) = slen\<cdot>i" using streamstatesem_len
      by (metis len_stream_def nspf_def) 
  from this show "slen\<cdot>(spf\<cdot>i) = slen\<cdot>i"
    by (simp add: local.step)
qed
end


locale tsStrongGen =
  fixes ndaTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable) set"
      and ndaInitConfig:: "'param \<Rightarrow> ('state \<times> 'b) set"
      and fin:: "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::"'b::countable \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes sbegenfin: "sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

abbreviation initConfigC::"'param \<Rightarrow> ('state \<times> 'b) set" where
"initConfigC param \<equiv> (if ndaInitConfig param = {} then UNIV else ndaInitConfig param)"

definition initConfig::"'param \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set" where
"initConfig param = apsnd (sbe2sb o sbeGen.setter fout) ` initConfigC param"

end


sublocale tsStrongGen \<subseteq> tsGen ndaTransition initConfig fin fout
  by (simp add: tsGen_def sbegenfin sbegenfout initConfig_def)

context tsStrongGen begin

lift_definition ndas_stream::"'param \<Rightarrow> ('state, 'a::countable, 'b::countable stream) automaton" is
"\<lambda>param. ((\<lambda> s m. (apsnd sup') ` (transitionC param s m)), ((\<lambda>(s,i). (s,\<up>i)) ` initConfigC param))"
  by(simp add: transition_def transitionC_def completeinit)

abbreviation StateSems_stream:: "'param \<Rightarrow> 'state \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"StateSems_stream param \<equiv> stateSem stream_step (ndas_stream param)"

abbreviation Spss_stream:: "'param \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"Spss_stream param \<equiv> sem stream_step (ndas_stream param)"

lemma strongsem_unfold_pred_s:
  assumes "spf \<in> (Sps p)"
    and "(\<And>spf out nstate. (nstate,out)\<in> (initConfigC p)
               \<Longrightarrow> spf \<in> (StateSem p) nstate        
               \<Longrightarrow> P(sbeGen.setter fout out \<Zcat>\<^sup>\<surd> (spf\<cdot>sb)))"
  shows "P (spf\<cdot>sb)"
  apply(rule strongsem_unfold_pred[of _ p])
  apply(simp_all add: assms)
proof-
  fix spf out nstate
  assume a1:"(nstate, out) \<in> initConfig p"
  assume a2:"spf \<in> (\<lbrakk>(nda p)\<rbrakk>\<^sup>p) nstate"
  obtain outo where out_def:"out = sbe2sb (sbeGen.setter fout outo)"
              and "(nstate, outo) \<in> initConfigC p"
    using a1 by(auto simp add: initConfig_def)
  thus "P (out \<Zcat>\<^sup>\<Omega> spf\<cdot>sb)"
    apply(simp)
    apply(rule assms(2)[of nstate])
    by(simp_all add: a1 a2 out_def)
qed

lemma strongsem_unfold_pred_s2:
  assumes "spf \<in> (Sps p)"
    and "(\<And>spf out nstate. (nstate,out)\<in> (initConfigC p)
               \<Longrightarrow> spf \<in> (StateSem p) nstate        
               \<Longrightarrow> P (\<Lambda> sb. sbeGen.setter fout out \<Zcat>\<^sup>\<surd> (spf\<cdot>sb)))"
  shows "P spf" 
  apply(rule strongsem_unfold_pred2[of _ p])
  apply(simp_all add: assms)
  proof-
  fix spf out nstate
  assume a1:"(nstate, out) \<in> initConfig p"
  assume a2:"spf \<in> (\<lbrakk>(nda p)\<rbrakk>\<^sup>p) nstate"
  obtain outo where out_def:"out = sbe2sb (sbeGen.setter fout outo)"
              and "(nstate, outo) \<in> initConfigC p"
    using a1 by(auto simp add: initConfig_def)
  thus "P (\<Lambda> sb. out \<Zcat>\<^sup>\<Omega> spf\<cdot>sb)"
    apply(simp)
    apply(rule assms(2)[of nstate])
    by(simp_all add: a1 a2 out_def)
qed


lemma strong[simp]:
  assumes "spf \<in> Sps p"
  shows "strong spf"
  apply (rule sem_strong)
  using assms apply simp_all
  apply(auto simp add: transition_def initConfig_def tlen_len_eq)[2]
  by(cases "chDomEmpty TYPE('out)";simp)+

lemma strongpred[simp]:
  assumes "spf \<in> Sps p"
  shows "strongpred sb (spf\<cdot>sb)"
  apply(simp add: strongpred_def)
  apply(rule sem_strong_sblen[of _ "nda p"])
  using assms apply simp_all
  apply(auto simp add: transition_def initConfig_def tlen_len_eq)[2]
  by(cases "chDomEmpty TYPE('out)";simp)+

(*
lemma strongpred_ts[simp]:
  assumes "spf\<in> Sem p"
  shows "strongpred_ts sb (spf\<cdot>sb)"
  apply(simp add: strongpred_ts_def)
  apply (simp add: tlen_len_eq [symmetric])
  by (meson assms strongpred strongpred_def)
*) 

lemma strongwell[simp]:
  assumes "spf \<in> Sps p"
  shows "strong spf"
  apply (auto simp add: strong_def)[1]
  apply(rule sem_strong_sblen[of _ "nda p"])
  using assms apply simp_all
  apply(auto simp add: transition_def initConfig_def tlen_len_eq)[2]
  by(cases "chDomEmpty TYPE('out)";simp)+

lemma sem_strong_len[simp]:
  assumes "\<not>chDomEmpty TYPE('out)"  
    and "spf\<in> Sps p"
  shows "#(spf\<cdot>sb) = lnsuc\<cdot>(#sb)"
  (*apply (simp add: tlen_len_eq [symmetric])*)
  oops

(*
  apply (rule ndasem_strong_len [of "nda p"])
  using assms apply (simp_all)
  apply (auto simp: ndaTransition.rep_eq nda.rep_eq transition_def)[1]
  by (auto simp add: ndaInitConfig_def  nda.rep_eq initConfig_def initConfigH_def)
*)

theorem statesem_eq:
  assumes "autTransition\<cdot>aut1 = autTransition\<cdot>aut2"
  shows "stateSem step aut1 = stateSem step aut2"
  by (metis assms stateSem_eqI)

lemma StateSem_strong2StateSems[simp]:"StateSem_weak_stream = StateSems_stream"
  apply rule
  apply(rule statesem_eq)
  by(simp add: nda_weak_stream.rep_eq autTransition.rep_eq ndas_stream.rep_eq)

lemma sl1_hin: 
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
    shows "(\<lambda>s. (\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` StateSem param s) \<le> StateSems_stream param"
  apply(insert l1_hin[where param=param])
  apply(simp add: assms)
  using StateSem_strong2StateSems
  by metis

lemma sl1_hin_alt: 
  assumes "\<not>(chDomEmpty TYPE('in))"
    and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s \<le> stateSem stream_step (ndas_stream param) s"
  using assms sl1_hin
  by (simp add: le_fun_def)

lemma wsem2streamsem_step_rule:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
      and  "\<And>spf. spf\<in> StateSems_stream param s \<Longrightarrow> P i (spf\<cdot>i)"
      and "spf2 \<in> StateSem param s"
    shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
  using sem2streamsem_step_rule StateSem_strong2StateSems assms
  by metis

lemma sl1:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))" 
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` ndaStateSem (nda param) s = stateSem stream_step (ndas_stream param) s"
  oops

lemma l2_hin: 
 assumes "\<not>(chDomEmpty TYPE('in))"
     and "\<not>(chDomEmpty TYPE('out))"
   shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` Sps param \<le> sem stream_step (ndas_stream param)"
  apply (simp add: sem_def)
  apply auto
proof -
  fix initOut and initState and spf
  assume asm1: "(initState, initOut) \<in> initConfig param" 
    and asm2: "spf \<in> (\<lbrakk>(nda param)\<rbrakk>\<^sup>p) initState"
  obtain out where outDef: "sbe2sb (sbeGen.setter fout (out::'b)) = initOut"
    using asm1 unfolding initConfig_def
    by force
  
  obtain spf2 where spf2_def: "spf2 \<in> (StateSems_stream param initState)" 
              and spf2_attr: "sbeGen.getterSB fout oo spf oo sbeGen.setterSB fin = spf2" 
    using asm2 assms
    using sl1_hin_alt[of "param::'param" "initState::'state"] by blast
  
  show "\<exists>(initOuta::'b stream) (initState::'state) spfa::'a stream \<rightarrow> 'b stream.
          sbeGen.getterSB fout oo (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut\<Zcat>\<Zcat>spf\<cdot>sb) oo sbeGen.setterSB fin =
          (\<Lambda> (sb::'a stream). initOuta \<Zcat> spfa\<cdot>sb) \<and>
          (initState, initOuta) \<in> autInitConfig\<cdot>(ndas_stream param) \<and> spfa \<in> StateSems_stream param initState"
    apply (rule_tac x="\<up>out" in exI)
    apply (rule_tac x="initState" in exI)
    apply (rule_tac x="spf2" in exI)
    apply (simp add: spf2_def) apply auto
    defer
    unfolding autInitConfig.rep_eq ndas_stream.rep_eq
    using asm1 outDef
    unfolding initConfig_def
    subgoal 
    proof-
      have "(initState, initOut) \<in> apsnd (sbe2sb \<circ> sbeGen.setter fout) ` initConfigC param"
        using asm1 initConfig_def by blast
      
      then obtain i where "(initState, i) \<in> initConfigC param"
        and "initOut = sbe2sb (sbeGen.setter fout i)"
        by auto
      
      have "sbe2sb (sbeGen.setter fout out) = sbe2sb (sbeGen.setter fout i)"
        by (simp add: \<open>(initOut::'out\<^sup>\<Omega>) = sbe2sb (sbeGen.setter (fout::'b \<Rightarrow> 'out \<Rightarrow> M) (i::'b))\<close> outDef) 
      
      from this have "out = i"
        by (metis sbeGen.get_set sbegenout sbeinv)
      
      have "(initState, out) \<in> initConfigC param"
        using \<open>(initState::'state, i::'b) \<in> initConfigC (param::'param)\<close> \<open>(out::'b) = (i::'b)\<close> by blast
      
         show ?thesis
           by (simp add: \<open>(initState::'state, out::'b) \<in> initConfigC (param::'param)\<close> pair_imageI[of "initState::'state" "out::'b" "initConfigC (param::'param)" "\<lambda>(uu::'state) uua::'b. (uu, \<up>uua)"])
       qed
    apply (rule cfun_eqI)
    apply simp
    apply (subst outDef [symmetric])
    apply (subst conc_sb_def)
    apply (subst sbeGen.gettersb_unfold)
    apply (simp add: sbegenout)
    apply (subst sbeGen.get_set)
    apply (simp add: sbegenout)
    using spf2_attr
    by fastforce
qed
  


lemma ssem2streamsem_rule:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
      and  "\<And>spf. spf\<in> sem stream_step (ndas_stream param) \<Longrightarrow> P i (spf\<cdot>i)"
      and "spf2 \<in> Sps param"
    shows "P i (sbeGen.getterSB fout\<cdot>(spf2\<cdot>(sbeGen.setterSB fin\<cdot>i)))"
  using l2_hin assms
  by (metis
      cfcomp2[of "sbeGen.getterSB (fout::'b \<Rightarrow> 'out \<Rightarrow> M)"
        "(spf2::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) oo sbeGen.setterSB (fin::'a \<Rightarrow> 'in \<Rightarrow> M)" "i::'a stream"]
      cfcomp2[of "spf2::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>" "sbeGen.setterSB (fin::'a \<Rightarrow> 'in \<Rightarrow> M)" "i::'a stream"]
      image_subset_iff[of
        "\<lambda>uub::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
          sbeGen.getterSB (fout::'b \<Rightarrow> 'out \<Rightarrow> M) oo uub oo sbeGen.setterSB (fin::'a \<Rightarrow> 'in \<Rightarrow> M)"
        "\<lbrakk>(nda (param::'param))\<rbrakk>\<^sup>c" "Spss_stream (param::'param)"])
  
  

lemma l2:
  assumes "\<not>(chDomEmpty TYPE('in))"
      and "\<not>(chDomEmpty TYPE('out))"
  shows "(\<lambda>f. sbeGen.getterSB fout oo f oo sbeGen.setterSB fin ) ` Sps param = sem stream_step (ndas_stream param)"
  oops

lemma statesems_stream_step:
  assumes"spf\<in> StateSems_stream param state"
  shows"\<exists>nspf ns out. spf\<cdot>(\<up>a \<Zcat> s) = \<up>out \<Zcat> nspf\<cdot>s \<and> nspf\<in> StateSems_stream param ns \<and> (ns,out) \<in> (transitionC param state a)"
proof -
  have helper:"(autTransition\<cdot>(ndas_stream param)) state a = apsnd sup' ` transitionC param state a"
    by (simp add: autTransition.rep_eq ndas_stream.rep_eq)
  obtain nspf out ns where step: "spf\<cdot>(\<up>a \<Zcat> s) = out \<Zcat> nspf\<cdot>s" and
      spf2_def: "nspf\<in> StateSems_stream param ns" and
      transition_in: "(ns,out) \<in> (autTransition\<cdot>(ndas_stream param)) state a"
    using StateSem_strong2StateSems
    by (metis assms conc_stream_def stateSemf_def
        stream_steps_sbe) 
  then have "\<exists>m. out = \<up>m"
    using transition_in apply(simp add: helper)
    by fastforce
  then obtain  outb where
    outb_def :"out = \<up>outb" and
    transwell: "(ns, outb) \<in> transitionC param state a"
    using transition_in apply(simp add: helper)
    by force
  show ?thesis 
    apply (rule_tac x = nspf in exI)
    apply (rule_tac x= ns in exI)
    apply (rule_tac x= outb in exI)
    using spf2_def outb_def transwell step
    by simp
qed

lemma sems_stream_apply_init_step:
  assumes "spf \<in> Spss_stream param"
  shows "\<exists>(initState, initOut) \<in> (initConfigC param). \<exists>spf2 \<in> (StateSems_stream param initState) .  
          spf\<cdot>s = \<up>initOut \<Zcat> spf2\<cdot>s"
proof -
  obtain nspf Initout  Initstate where step: "spf\<cdot>(s) = Initout \<Zcat> nspf\<cdot>s" and
      nspf_def: "nspf\<in> StateSems_stream param Initstate" and
      transition_def: "(Initstate,Initout) \<in> (autInitConfig\<cdot>(ndas_stream param))"
    by (metis assms conc_stream_def
        ndasem_pred) 

  then have  "\<exists>m. Initout = \<up>m"
  proof -
    have f1: "\<forall>p. if ndaInitConfig p = {} then Rep_automaton (ndas_stream p) = (\<lambda>s a. apsnd sup' ` transitionC p s a, range (\<lambda>(s, b). (s, \<up>b))) else Rep_automaton (ndas_stream p) = (\<lambda>s a. apsnd sup' ` transitionC p s a, (\<lambda>(s, b). (s, \<up>b)) ` ndaInitConfig p)"
      using ndas_stream.rep_eq by fastforce
    have f2: "(\<lambda>(s, b). (s, \<up>b)) ` (if ndaInitConfig param = {} then UNIV else ndaInitConfig (id param)) = snd (Rep_automaton (ndas_stream param)) \<longrightarrow> (Initstate, Initout) \<in> (\<lambda>(s, b). (s, \<up>b)) ` (if ndaInitConfig param = {} then UNIV else ndaInitConfig (id param))"
      by (metis autInitConfig.rep_eq transition_def)
    { assume "(Initstate, Initout) \<notin> (\<lambda>(s, b). (s, \<up>b)) ` ndaInitConfig param"
      then have "(\<lambda>(s, b). (s, \<up>b)) ` ndaInitConfig param \<noteq> snd (Rep_automaton (ndas_stream param))"
        by (metis (no_types) autInitConfig.rep_eq transition_def)
      then have "ndaInitConfig param = {}"
        using f1 by (metis Pair_eqD2 surjective_pairing)
      then have ?thesis
        using f2 f1 by auto }
    then show ?thesis
      by fastforce
  qed

  then obtain  Initoutb where
    outb_def :"Initout = \<up>Initoutb"
    by auto 

  show ?thesis
    apply(rule_tac x="(Initstate, Initoutb)" in bexI)
    using local.step nspf_def outb_def
     apply blast
    apply auto
    using transition_def autInitConfig_def autInitConfig.rep_eq Rep_automaton ndas_stream_def ndas_stream.rep_eq outb_def
  proof -
    fix a :: 'state and b :: 'b
    assume a1: "(a, b) \<in> ndaInitConfig param"
    assume a2: "(Initstate, Initoutb) \<notin> ndaInitConfig param"
    have "ndaInitConfig param \<noteq> {}"
      using a1 by blast
    then have "(\<lambda>(s, b). (s, \<up>b)) ` ndaInitConfig param = snd (Rep_automaton (ndas_stream param))"
      by (simp add: ndas_stream.rep_eq)
    then have "(Initstate, Initout) \<in> (\<lambda>(s, b). (s, \<up>b)) ` ndaInitConfig param"
      by (metis (no_types) autInitConfig.rep_eq transition_def)
    then show False
      using a2 outb_def by force
  qed
qed

end

declare tlen_len_eq[simp]
end
