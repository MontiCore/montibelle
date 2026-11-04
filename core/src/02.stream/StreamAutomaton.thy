theory StreamAutomaton

imports Stream automaton.DeterministicAutomaton automaton.Reachability automaton.Steps
begin
default_sort type
paragraph\<open>Processing streams element-wise\<close>
text\<open>is can be realized as a special case of our deterministic 
automatons state semantic given a appropriate splitting operator.
The following one applies a given function to the head and rest of 
a stream. The output must be a @{class pcpo} to map the empty 
stream to \<open>\<bottom>\<close>.\<close>
definition stream_step::"('m::countable \<Rightarrow> 'm stream \<rightarrow> 'a::pcpo) \<rightarrow>
                           'm stream \<rightarrow> 'a" where
"stream_step \<equiv> \<Lambda> k s. fup\<cdot>(\<Lambda> a. k (undiscr a)\<cdot>(srt\<cdot>s))\<cdot>((lshd\<cdot>s))"

lemma stream_step_insert:"stream_step\<cdot>f\<cdot>s = 
                      (case lshd\<cdot>s of up\<cdot>a \<Rightarrow> f (undiscr a)\<cdot>(srt\<cdot>s))"
  apply(simp add: stream_step_def)
  done
theorem stream_step_eps[simp]:"stream_step\<cdot>f\<cdot>\<epsilon> = \<bottom>"
  by (simp add: stream_step_insert)

theorem stream_steps_sbe[simp]:"stream_step\<cdot>f\<cdot>(\<up>a \<Zcat> s) = f a\<cdot>s"
  by (simp add: stream_step_insert)

lemma stream_steps_one[simp]:"stream_step\<cdot>f\<cdot>(\<up>a) = f a\<cdot>\<epsilon>"
  by (metis sconc_snd_empty stream_steps_sbe)


lemma streamsplit_eqI: assumes "\<And>sbe sb. spf\<cdot>(\<up>sbe \<Zcat> sb) = f sbe\<cdot>sb"
      and "spf\<cdot>\<epsilon> = \<epsilon>"
    shows "spf = stream_step\<cdot>f"
  by(rule cfun_eqI,case_tac x,simp_all add: assms)
definition sscanlA::"('s \<Rightarrow> 'i \<Rightarrow> ('s \<times> 'o::{conc})) \<Rightarrow> 's \<Rightarrow> 
                 'i::countable stream \<rightarrow> 'o" where
"sscanlA f s = daStateSem stream_step (| dautTransition = f, dautInitConfig = undefined |) s"

lemma sscanlAsimps_eps[simp]:"sscanlA f state\<cdot>\<epsilon> = \<bottom>"
  and sscanlAsimps_step[simp]:"sscanlA f state\<cdot>(\<up>a \<Zcat> s) = snd (f state a) \<Zcat>\<Zcat> sscanlA f (fst (f state a))\<cdot>s"
  and sscanlAsimps_one[simp]:"sscanlA f state\<cdot>(\<up>a) = snd (f state a)"
   apply(simp_all add: sscanlA_def)
  by(subst dastatesem_step,auto simp add: case_prod_beta)+

lemma statesem2da:"daStateSem stream_step da s = sscanlA (dautTransition da) s"
  by(simp add: daStateSem_def sscanlA_def)

theorem dastatesem_unfold_stream_step:
  assumes "(ns, out) = (dautTransition da) s sbe"
  shows "(daStateSem stream_step da) s\<cdot>(<(sbe#xs)> \<Zcat> ss) = out \<Zcat>\<Zcat> daStateSem stream_step da ns\<cdot>(<xs> \<Zcat> ss)"
  using assms apply(subst dastatesem_step)
  apply(simp add: case_prod_unfold Let_def)
  by (metis fst_conv snd_conv)

theorem scanLineStateSem:
assumes "\<And> b state. (transitionFunc state b)  \<in> ((autTransition\<cdot>automaton) state b)"
shows "sscanlA transitionFunc state \<in> stateSem stream_step automaton state"
  proof -
    have "(\<And>(s::'b) i::'a. transitionFunc s i \<in> (autTransition\<cdot>automaton) s i)"
      using assms by simp
    thus ?thesis
      apply (subst sscanlA_def)
      using dasseminssem_rule[of "\<lparr>dautTransition = transitionFunc, dautInitConfig = undefined\<rparr>" id automaton stream_step state]
      by auto
  qed

theorem transitionFuncOneStateIS:
  assumes
    "\<And> b state. ((transitionFunc::'s \<Rightarrow> bool \<Rightarrow> ('s \<times> bool stream)) state b)  \<in> ((autTransition\<cdot>automaton) state b)"
  and
    "\<forall>y::bool. nextState = ((fst (transitionFunc state y)))"
  and
    "spf \<in> stateSem stream_step automaton nextState"
  shows
  "stream_step\<cdot>(\<lambda> x. \<Lambda> s. (snd (transitionFunc state x)) \<Zcat> spf\<cdot>s ) 
              \<in> stateSem stream_step automaton state"
proof -
  have "\<forall>msg. \<exists>output nextState.
             (nextState, output) \<in> (autTransition\<cdot>automaton) state msg \<and>
             (\<exists>nextSPF.
                 nextSPF \<in> stateSem stream_step automaton nextState \<and>
                 (\<forall>input. snd (transitionFunc state msg) \<Zcat> spf\<cdot>input = output \<Zcat> nextSPF\<cdot>input))"
    apply (rule allI)
    proof -
      fix msg
      show "\<exists>output nextState.
              (nextState, output) \<in> (autTransition\<cdot>automaton) state msg \<and>
              (\<exists>nextSPF.
                  nextSPF \<in> stateSem stream_step automaton nextState \<and>
                  (\<forall>input. snd (transitionFunc state msg) \<Zcat> spf\<cdot>input = output \<Zcat> nextSPF\<cdot>input))"
        apply (rule_tac x="snd (transitionFunc state msg)" in exI)
        apply (rule_tac x="fst (transitionFunc state msg)" in exI)
        apply auto
         defer
        apply (rule_tac x="spf" in exI)
        using assms by auto
    qed

  thus ?thesis
    unfolding stateSem_unfold[of stream_step automaton state] stateSem_step_def
    image_def
    apply auto
    apply (rule_tac x="(\<lambda>x. \<Lambda> s. snd (transitionFunc state x) \<Zcat> spf\<cdot>s)" in exI)
    by simp
qed

theorem transitionFuncOneStateGeneralIS:
  assumes
    "\<And>b state. (transitionFunc::('s \<Rightarrow> ('intype::countable) \<Rightarrow> ('s \<times> ('outtype::conc)))) state b \<in> (autTransition\<cdot>automaton) state b"
  and
    "\<forall>(y::'intype). nextState = ((fst (transitionFunc state y)))"
  and
    "spf \<in> stateSem stream_step automaton nextState"
  shows
    "stream_step\<cdot>(\<lambda> x. \<Lambda> s. (snd (transitionFunc state x)) \<Zcat>\<Zcat> spf\<cdot>s) \<in> stateSem stream_step automaton state"
proof -
  have "\<forall>msg. \<exists>output nextState.
             (nextState, output) \<in> (autTransition\<cdot>automaton) state msg \<and>
             (\<exists>nextSPF.
                 nextSPF \<in> stateSem stream_step automaton nextState \<and>
                 (\<forall>input. snd (transitionFunc state msg) \<Zcat>\<Zcat> spf\<cdot>input = output \<Zcat>\<Zcat> nextSPF\<cdot>input))"
    apply (rule allI)
    proof -
      fix msg
      show "\<exists>output nextState.
              (nextState, output) \<in> (autTransition\<cdot>automaton) state msg \<and>
              (\<exists>nextSPF.
                  nextSPF \<in> stateSem stream_step automaton nextState \<and>
                  (\<forall>input. snd (transitionFunc state msg) \<Zcat>\<Zcat> spf\<cdot>input = output \<Zcat>\<Zcat> nextSPF\<cdot>input))"
        apply (rule_tac x="snd (transitionFunc state msg)" in exI)
        apply (rule_tac x="fst (transitionFunc state msg)" in exI)
        apply auto
         defer
        apply (rule_tac x="spf" in exI)
        using assms by auto
    qed

  thus ?thesis
    unfolding stateSem_unfold[of stream_step automaton state] stateSem_step_def
    image_def
    apply auto
    apply (rule_tac x="(\<lambda>x. \<Lambda> s. snd (transitionFunc state x) \<Zcat>\<Zcat> spf\<cdot>s)" in exI)
    by simp
qed

theorem transitionThenScanLine:
  assumes
    "\<And> b state. ((transition1::'s \<Rightarrow> bool \<Rightarrow> ('s \<times> bool stream)) state b)  \<in> ((autTransition\<cdot>automaton) state b)"
  assumes
    "\<And> b state. ((transition2::'s \<Rightarrow> bool \<Rightarrow> ('s \<times> bool stream)) state b)  \<in> ((autTransition\<cdot>automaton) state b)"
  and
    "\<forall>y::bool. nextState = ((fst (transition1 state y)))"
  shows
  "stream_step\<cdot>(\<lambda> x. \<Lambda> s. (snd (transition1 state x)) \<Zcat> (sscanlA transition2 nextState)\<cdot>(s) ) 
              \<in> stateSem stream_step automaton state"
  using assms using scanLineStateSem[of transition2 automaton nextState] 
  transitionFuncOneStateIS[of transition1 automaton nextState state "(sscanlA transition2 nextState)"]
  by auto

   
definition sscanlAOne::"('s \<Rightarrow> 'i \<Rightarrow> ('s \<times> 'o)) \<Rightarrow> 's \<Rightarrow> 
                'i::countable stream \<rightarrow> 'o::countable stream" where
"sscanlAOne f = sscanlA (\<lambda>s i. apsnd sup' (f s i))"

text \<open>One-step unfolding equation for @{const sscanlAOne} on a non-empty stream.\<close>
lemma sscanlaone_step:
  "sscanlAOne f init\<cdot>(\<up>a \<Zcat> rest) =  sup' (snd (f init a)) \<Zcat> sscanlAOne f (fst (f init a))\<cdot>rest"
  by (simp add: sscanlAOne_def )

lemma svalues_sscanlaone_subset_sscanlaone_init:
  assumes a2: "\<And> s m. snd (t s m) = snd (t init m) \<or> snd (t s m) \<in> S"
  assumes a3: "\<And> s m. fst (t init m) \<noteq> init \<Longrightarrow> fst (t init m) = fst (t s m)"
  shows "sValues\<cdot>(sscanlAOne t state\<cdot>s) \<subseteq> sValues\<cdot>(sscanlAOne t init\<cdot>s) \<union> S"
proof (induction s arbitrary: state)
  case adm
    then show ?case
      unfolding subset_iff
      apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
      using adm_cmp apply force 
      apply (simp add: SetPcpo.adm_in2)
      by (metis (mono_tags, lifting) adm_upward cont_pref_eq1I in_mono sValues_prefix)
  next
    case bottom
    then show ?case
      by (simp add: sscanlAOne_def sscanlAsimps_eps)
  next
  case (step a s)

  obtain st1 out1 where T1: "t state a = (st1, out1)"
    by (cases "t state a") auto
  obtain st0 out0 where T0: "t init a = (st0, out0)"
    by (cases "t init a") auto

  have SV_L:
    "sValues\<cdot>(sscanlAOne t state\<cdot>(\<up>a \<Zcat> s))
     = sValues\<cdot>(sup' out1) \<union> sValues\<cdot>(sscanlAOne t st1\<cdot>s)"
    by (simp add: sscanlaone_step T1)

  have SV_R:
    "sValues\<cdot>(sscanlAOne t init\<cdot>(\<up>a \<Zcat> s))
     = sValues\<cdot>(sup' out0) \<union> sValues\<cdot>(sscanlAOne t st0\<cdot>s)"
    by (simp add: sscanlaone_step T0)

  have out_rel: "out1 = out0 \<or> out1 \<in> S"
    using a2[of state a]
    by (simp add: T1 T0)

  have head_sub:
    "sValues\<cdot>(sup' out1) \<subseteq> sValues\<cdot>(sup' out0) \<union> S"
  proof (cases "out1 = out0")
    case True
    then show ?thesis by simp
  next
    case False
    with out_rel have "out1 \<in> S" by blast
    then show ?thesis by simp
  qed

  have tail_sub:
    "sValues\<cdot>(sscanlAOne t st1\<cdot>s) \<subseteq> sValues\<cdot>(sscanlAOne t st0\<cdot>s) \<union> S"
  proof (cases "st0 = init")
    case True
    have "sValues\<cdot>(sscanlAOne t st1\<cdot>s) \<subseteq> sValues\<cdot>(sscanlAOne t init\<cdot>s) \<union> S"
      using step.IH by blast
    then show ?thesis
      using True by simp
  next
    case False
    have st_eq: "st1 = st0"
    proof -
      have "fst (t init a) \<noteq> init"
        using False by (simp add: T0)
      hence "fst (t init a) = fst (t state a)"
        by (simp add: a3)
      thus ?thesis
        by (simp add: T1 T0)
    qed
    then show ?thesis by simp
  qed

  show ?case
    using head_sub tail_sub
    using SV_L SV_R by blast

qed

lemma svalues_sscanlaone_subset_input_union:
  assumes a2: "\<And> s m. snd (t s m) = m \<or> snd (t s m) \<in> S"
  shows "sValues\<cdot>(sscanlAOne t state\<cdot>s) \<subseteq>  sValues\<cdot>s \<union> S"
proof (induction s arbitrary: state)
  case adm
  then show ?case 
    unfolding subset_iff
    apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
    using adm_cmp apply force 
    apply (simp add: SetPcpo.adm_in2)
    done
next
  case bottom
  then show ?case
    by (simp add: sscanlAOne_def sscanlAsimps_eps)
next
  case (step a s)
  obtain st' out where T: "t state a = (st', out)"
    by (cases "t state a") auto

  have scan:
    "sscanlAOne t state\<cdot>(\<up>a \<Zcat> s) = sup' out \<Zcat>\<Zcat> sscanlAOne t st'\<cdot>s"
    by (simp add: sscanlaone_step T)

  have sv:
    "sValues\<cdot>(sscanlAOne t state\<cdot>(\<up>a \<Zcat> s))
     = {out} \<union> sValues\<cdot>(sscanlAOne t st'\<cdot>s)"
    by (simp add: scan)

  have IH:
    "sValues\<cdot>(sscanlAOne t st'\<cdot>s) \<subseteq> sValues\<cdot>s \<union> S"
    using step.IH by simp

  have out_in:
    "out \<in> sValues\<cdot>(\<up>a \<Zcat> s) \<union> S"
  proof -
    from a2[of state a] have "out = a \<or> out \<in> S"
      by (simp add: T)
    then show ?thesis
      by (auto simp: sValues2un)
  qed

  show ?case
    unfolding sv
    using IH out_in
    by (auto simp: sValues2un)
qed

theorem dastatesem_x_steps:
  "daStateSem stream_step da s\<cdot>(<ls> \<Zcat> xs)
   = (let (nextState, output) = multTransitionsInOne da s ls in
        output \<Zcat>\<Zcat> daStateSem stream_step da nextState\<cdot>xs)"
  apply(induction ls arbitrary: s; simp add: case_prod_beta Let_def)
  apply(subst dastatesem_step, simp add: case_prod_beta)
  by (simp add: assoc)
lemma multTransitionsInOne_oup_rs_aux: "daReach (a # ls) s (dautTransition da) = daReach ls (fst (dautTransition da s a)) (dautTransition da)"
  and "snd (dautTransition da s a)\<Zcat>\<Zcat>daStateSem stream_step da (fst (dautTransition da s a))\<cdot>(<ls>) =
         daStateSem stream_step da s\<cdot>(\<up>a \<Zcat> <ls>)"
   apply (metis daReach_dautTransition_eq daReach_step)
   by (simp add: statesem2da)

lemma multTransitionsInOne_oup_rs_def: "multTransitionsInOne da s ls = ((daReach ls s (dautTransition da)), (daStateSem stream_step da s\<cdot>(list2s ls)))"
  apply(induction ls arbitrary: s; simp add: case_prod_beta Let_def)
  apply(simp add: daReach_def; fail)
  by (simp add: multTransitionsInOne_oup_rs_aux statesem2da)


lemma dastatesem_processlist: "(daStateSem stream_step da s\<cdot>((<ls>) \<Zcat> xs)) = (daStateSem stream_step da s\<cdot>(list2s ls)) \<Zcat>\<Zcat> (daStateSem stream_step da (daReach ls s (dautTransition da))\<cdot>xs)"
  by (subst dastatesem_x_steps, simp add: multTransitionsInOne_oup_rs_def)

lemma stream_lnatadd_bot[simp]: "daStateSem (step_lnat_add\<cdot>stream_step) daDemand s\<cdot>(\<epsilon>, ln) = \<bottom>"
  by(induction ln; simp)

lemma stateSemMsg_def: assumes "spf \<in> stateSem stream_step aut s" 
   shows "\<forall>msg. (\<exists>out nextState. ((nextState, out) \<in> (autTransition\<cdot>aut) s msg) \<and>
      (\<exists>nextSPF. ((nextSPF \<in> (stateSem stream_step aut) nextState)) \<and>
      (spf\<cdot>(\<up>(msg)\<Zcat>rt) = out \<Zcat>\<Zcat> (nextSPF\<cdot>rt))) )"
  using assms
proof auto
  fix msg::'a
  assume "spf \<in> stateSem stream_step aut s"
  
  have spf_in_step: "spf \<in> stateSem_step stream_step aut (stateSem stream_step aut) s"
    by (simp add: assms stateSem_stepI)

  from this obtain f where f_def: "\<forall>msg. \<exists>output nextState. 
     (nextState,output) \<in> (autTransition\<cdot>aut) s msg
      \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem stream_step aut) nextState 
      \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
    and spf_def: "spf = stream_step\<cdot>f"
    by (auto simp add: stateSem_step_def stateSemf_def) 

  from this obtain out nextState nextSPF where 
    out_def: "((nextState,out) \<in> (autTransition\<cdot>aut) s msg
      \<and>  (nextSPF \<in> (stateSem stream_step aut) nextState) 
      \<and>  (\<forall>sb. f msg\<cdot>sb = out \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
    and spf_def_2: "spf = stream_step\<cdot>f"
    by blast  

  thus "\<exists>(out::'b) nextState::'c.
          (nextState, out) \<in> (autTransition\<cdot>aut) s msg \<and>
          (\<exists>nextSPF::'a stream \<rightarrow> 'b. nextSPF \<in> stateSem stream_step aut nextState \<and> spf\<cdot>(\<up>msg \<Zcat> rt) = out\<Zcat>\<Zcat>nextSPF\<cdot>rt)"
    by (auto)                          
qed



definition prod_shd::"('a::countable stream \<times> 'b::countable stream) \<rightarrow> ('a \<times> 'b) lift" where
"prod_shd = (\<Lambda> input. Abs_lift (lshd\<cdot>(szip\<cdot>(fst input)\<cdot>(snd input))))"

lemma prod_shd_insert: "prod_shd\<cdot>input =  Abs_lift (lshd\<cdot>(szip\<cdot>(fst input)\<cdot>(snd input)))"
  apply(simp_all add: prod_shd_def)
   apply(subst beta_cfun)
   apply(simp add: cont_Abs_lift)
  ..
definition prod_srt::"('a::countable stream \<times> 'b::countable stream) \<rightarrow> ('a stream \<times> 'b stream)" where
"prod_srt = (\<Lambda> input. (srt\<cdot>(fst input), srt\<cdot>(snd input)))"

lemma assumes  "prod_shd\<cdot>input = Def (a1, a2)"
  shows prodshd_fst:"shd (fst input) = a1" 
    and prodshd_snd:"shd (snd input) = a2"
  using assms apply(simp_all add: prod_shd_insert)
   apply(cases input; simp)
  apply(case_tac a;case_tac b; simp)
  apply (metis(mono_tags) DefE inst_lift_pcpo)+
  apply (metis Def_def lift.inject prod.inject)

   apply(cases input; simp)
  apply(case_tac a;case_tac b; simp)
  apply (metis(mono_tags) DefE inst_lift_pcpo)+
  apply (metis Def_def lift.inject prod.inject)
  done

lemma prod_srt_fst[simp]: "fst (prod_srt\<cdot>input) = srt\<cdot>(fst input)"
  by(simp add: prod_srt_def)

lemma prod_shd_shd [simp]: "prod_shd\<cdot>input = Def msg \<Longrightarrow> msg = (shd (fst input), shd (snd input))"
  apply(cases msg)
  using prodshd_fst prodshd_snd by blast

lemma prod_shd_bot1[simp]: "prod_shd\<cdot>(\<epsilon>, s2) = \<bottom>"
  apply(simp_all add: prod_shd_insert)
  using inst_lift_pcpo by auto

lemma prod_shd_bot2[simp]: "prod_shd\<cdot>(s1,\<epsilon>) = \<bottom>"
  apply(simp_all add: prod_shd_insert)
  using inst_lift_pcpo by auto

definition stream_prod_step::"(('fst::countable \<times> 'snd::countable)  \<Rightarrow> ('fst stream \<times> 'snd stream) \<rightarrow> 'out) \<rightarrow> ('fst stream \<times> 'snd stream) \<rightarrow> 'out::pcpo" where
"stream_prod_step \<equiv> step_create\<cdot>prod_shd\<cdot>prod_srt"

lemma stream_prod_step_eps1[simp]:"stream_prod_step\<cdot>f\<cdot>(\<epsilon>,s2) = \<bottom>"
  by (simp add: stream_prod_step_def)
lemma stream_prod_step_eps2[simp]:"stream_prod_step\<cdot>f\<cdot>(s1,\<epsilon>) = \<bottom>"
  by (simp add: stream_prod_step_def)

lemma stream_prod_step_msg[simp]:"stream_prod_step\<cdot>f\<cdot>((\<up>a1 \<Zcat> s1), (\<up>a2 \<Zcat> s2)) = f (a1,a2)\<cdot>(s1,s2)"
  apply (simp add: stream_prod_step_def)
  apply(subst step_create_insert2 [where msg ="(a1,a2)"])
  by (auto simp add: prod_shd_insert Def_def prod_srt_def)

lemma stream_prod_step_msg2[simp]: "stream_prod_step\<cdot>f\<cdot>((\<up>a1, \<up>a2)\<Zcat>\<Zcat>(s1, s2)) = f (a1, a2)\<cdot>(s1, s2)"
  by (simp add: conc_prod_stream_apply)

lemma stream_prod_step[simp]:"stream_prod_step\<cdot>f\<cdot>(\<up>a1, \<up>a2) = f (a1,a2)\<cdot>(\<epsilon>,\<epsilon>)"
  by (metis sconc_snd_empty sconc_snd_empty stream_prod_step_msg)

lemma allf_not_eps: assumes " (\<And>f. f (a1, a2)\<cdot>(s1, s2) = \<epsilon>)"
  shows False
proof -
  let ?f = "\<lambda>a. \<Lambda> s. \<up>undefined"
  have "?f (a1, a2)\<cdot>(s1, s2) \<noteq> \<epsilon>"
    by simp
  thus ?thesis
    using assms by fastforce
qed

lemma stream_prod_step_empty: assumes "\<And>f. stream_prod_step\<cdot>f\<cdot>(a, b) = \<epsilon>"
  shows "a = \<epsilon> \<or> b=\<epsilon>"
  apply(insert assms)
  apply(simp add: stream_prod_step_def)
  apply(cases a; simp; cases b; simp)
  by (metis allf_not_eps assms stream_prod_step_msg)

lemma induction_stream_prod_h:
  assumes "adm P"
    and "\<And>s1. P (s1,\<epsilon>)" 
    and "\<And>s2. P (\<epsilon>,s2)" 
    and "\<And>a1 a2 s1 s2. P (s1, s2) \<Longrightarrow> P (\<up>a1 \<Zcat> s1, \<up>a2 \<Zcat> s2)"
  shows "P (s1,s2)"
  apply(induction s1 arbitrary: s2)
    apply (simp add: adm2adm_snd assms(1))
  using assms(3) apply simp
  by (metis assms(2) assms(4) streamcases)

lemma induction_stream_prod:
  assumes "adm P"
    and "\<And>s1. P (s1,\<epsilon>)" 
    and "\<And>s2. P (\<epsilon>,s2)" 
    and "\<And>a1 a2 s1 s2. P (s1, s2) \<Longrightarrow> P (\<up>a1 \<Zcat> s1, \<up>a2 \<Zcat> s2)"
  shows "P s"
  apply(cases s; simp)
  apply(rule induction_stream_prod_h[OF assms])
  .


lemma sreachable_step_mono[simp]:"monofun
        (\<lambda>s. if s = \<epsilon> then S else S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s))"
unfolding monofun_def
proof (intro allI impI)
  fix x y :: "'a stream"
  assume assm: "x \<sqsubseteq> y"
  show "(if x = \<epsilon> then S else S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd x))\<cdot>(srt\<cdot>x)) \<sqsubseteq>
        (if y = \<epsilon> then S else S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd y))\<cdot>(srt\<cdot>y))"
  proof (cases "y = \<epsilon>")
    case True
    with assm have "x = \<epsilon>" by simp
    then show ?thesis by (simp add: True) 
  next
    case False
    then show ?thesis 
    proof (cases "x = \<epsilon>")
      case True
      have "S \<sqsubseteq> S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd y))\<cdot>(srt\<cdot>y)" 
      using le_funD
      by (simp add: SetPcpo.less_set_def)
      then show ?thesis
        by (simp add: True) 
    next
      case False
      from `x \<sqsubseteq> y` `x \<noteq> \<epsilon>` `y \<noteq> \<epsilon>` have 
        "shd x = shd y" and "srt\<cdot>x \<sqsubseteq> srt\<cdot>y"
        apply (simp add: below_shd)
        by (simp add: assm monofun_cfun_arg)
      from this False `y \<noteq> \<epsilon>` 
      have "S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd x))\<cdot>(srt\<cdot>x) \<sqsubseteq>
            S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd y))\<cdot>(srt\<cdot>y)" 
        by (metis SetPcpo.less_set_def Un_mono below_refl monofun_cfun_arg)
      from this  show ?thesis
        by (simp add: False \<open>y \<noteq> \<epsilon>\<close>)   
    qed
  qed
qed

lemma sreachable_step_cont[simp]:"cont
        (\<lambda>s. if s = \<epsilon> then S else S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s))"
    apply(rule Cpo.contI2,simp)
proof(case_tac "(\<Squnion>i. Y i) = \<epsilon>",simp_all add: lub_eq_bottom_iff,simp add: cont2contlubE)
  fix Y::"nat \<Rightarrow> 'a stream"
  assume a1:"chain Y "
  assume a2:"chain  (\<lambda>i. if Y i = \<epsilon> then S
              else S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd (Y i)))\<cdot>(srt\<cdot>(Y i)))"
  assume a3:"\<exists>i. Y i \<noteq> \<epsilon>"
  then obtain n a s where n_def:"(Y n) = (\<up>a \<Zcat> s)"
    by (meson streamcases)
  from a1 n_def have "\<forall>i\<ge>n. shd (Y i) = a"
    using chain_mono less_imp_le_nat
    by (metis below_shd_conc)
  from n_def have lub_shd_def:"shd (\<Squnion>i. Y i) = a" 
    apply (subst below_shd_conc [of a s])
     apply (simp add: n_def [symmetric])
    using a1 
     apply (simp add: is_ub_thelub)
    ..
  have yshd:"\<And>x. Y x \<noteq> \<epsilon> \<Longrightarrow> shd (Y x) = a"
    using a1 below_shd is_ub_thelub lub_shd_def
    by blast
  have reduce_set_case1:"{i. Y i = \<epsilon>} = {} \<Longrightarrow> ((\<lambda>x. S) ` {i. Y i = \<epsilon>} \<union>
          (\<lambda>x. S \<union> fun2  (\<Union>state\<in>S. fun1 state (shd (Y x)))\<cdot>(srt\<cdot>(Y x))) ` {i. Y i \<noteq> \<epsilon>}) =
          (\<lambda>x. S \<union> fun2  (\<Union>state\<in>S. fun1 state a)\<cdot>(srt\<cdot>(Y x))) ` {i. Y i \<noteq> \<epsilon>}"
    by(simp add: yshd)
  have "{i. Y i = \<epsilon>} \<noteq> {} \<Longrightarrow> (\<lambda>x. S) ` {i. Y i = \<epsilon>} = {S}"
    by auto
  then have reduce_set_case2:"{i. Y i = \<epsilon>} \<noteq> {} \<Longrightarrow> ((\<lambda>x. S) ` {i. Y i = \<epsilon>} \<union>
          (\<lambda>x. S \<union> fun2  (\<Union>state\<in>S. fun1 state (shd (Y x)))\<cdot>(srt\<cdot>(Y x))) ` {i. Y i \<noteq> \<epsilon>}) =
          (\<lambda>x. S \<union> fun2  (\<Union>state\<in>S. fun1 state a)\<cdot>(srt\<cdot>(Y x))) ` {i. Y i \<noteq> \<epsilon>} \<union> {S}"
      by (simp add: yshd)
  have rule_h:"(\<And>S x y. x\<sqsubseteq> y \<Longrightarrow> fun2 S\<cdot>x \<subseteq> fun2 S\<cdot>y)"
    by (simp add: set_monofun_cfun)
  have a4:"\<not> (\<forall>i. Y i = \<epsilon>)"
    by (simp add: a3)
  show "(\<Squnion>x. S \<union> fun2 (\<Union>x\<in>S. fun1 x (shd (Lub Y)))\<cdot>(srt\<cdot>(Y x))) \<sqsubseteq>
         lub ((\<lambda>x. S) ` {i. Y i = \<epsilon>} \<union>
               (\<lambda>x. S \<union> fun2 (\<Union>state\<in>S. fun1 state (shd (Y x)))\<cdot>(srt\<cdot>(Y x))) ` {i. Y i \<noteq> \<epsilon>})"
    apply(simp add: lub_shd_def)
    apply(cases "{i. Y i = \<epsilon>} = {}",subst reduce_set_case1,simp,simp)
    apply(subst  reduce_set_case2,simp)
    apply(simp add: less_set_def lub_eq_Union)
    apply(subgoal_tac "(\<Union>x. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x))) = (fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>\<epsilon>))\<union> (\<Union>x\<in>{i. Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))")
     apply simp
     apply(subgoal_tac "\<forall>y. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>\<epsilon> \<subseteq> fun2 (\<Union>state\<in>S. fun1 state a)\<cdot>y")
      apply(simp add: a3 a4)
    apply(subgoal_tac "{i. Y i \<noteq> \<epsilon>} \<noteq> {}")
    apply blast
    apply (simp add: a4)
     apply (simp add: rule_h)
   (* apply(subgoal_tac "(\<Union>x\<in>{i. \<not>Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x))) = (fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(\<epsilon>)))")*)
  proof
    assume "\<exists>x. Y x = \<epsilon>"
    then show  " (\<Union>x. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x))) \<subseteq> fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>\<epsilon>) \<union> (\<Union>x\<in>{i. Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))"
      apply (auto simp: SUP_le_iff UnCI mem_Collect_eq subsetI)
      by (metis stream.sel_rews(2))
  
    show  "...  \<subseteq> (\<Union>x. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))" 
    proof
      fix z
      assume "z \<in> fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>\<epsilon>)
               \<union> (\<Union>x\<in>{i. Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))"
      then show "z \<in> (\<Union>x. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))"
      using \<open>z \<in> fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>\<epsilon>)\<union> (\<Union>x\<in>{i. Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))\<close>
      by (metis (no_types) Sup_subset_mono UNIV_I UN_I Un_iff \<open>z \<in> fun2 (\<Union>x\<in>S. fun1 x a)\<cdot> (srt\<cdot>\<epsilon>) \<union> (\<Union>x\<in>{i. Y i \<noteq> \<epsilon>}. fun2 (\<Union>x\<in>S. fun1 x a)\<cdot>(srt\<cdot>(Y x)))\<close> 
          image_mono in_mono minimal rule_h stream.sel_rews(2) subset_UNIV)
    qed
  qed
qed


lemma sreachable_fun_mono[simp]:" monofun (\<lambda>S. \<Lambda> s. if s = \<epsilon> then S else S \<union> fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s))"
proof (rule monofunI)
  fix S T :: "'a set"
  assume assm:  "S \<sqsubseteq> T"
  show "(\<Lambda> s. if s = \<epsilon> then S else S \<union> fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s)) \<sqsubseteq>
        (\<Lambda> s. if s = \<epsilon> then T else T \<union> fun2\<cdot>(\<Union>state\<in>T. fun1 state (shd s))\<cdot>(srt\<cdot>s))"
    unfolding below_cfun_def below_fun_def
  proof (rule allI)
    fix x s
    show "(\<Lambda> s. if s = \<epsilon> then S else S \<union> fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s))\<cdot>x \<sqsubseteq>
        (\<Lambda> s. if s = \<epsilon> then T else T \<union> fun2\<cdot>(\<Union>state\<in>T. fun1 state (shd s))\<cdot>(srt\<cdot>s))\<cdot>x"
      apply (auto simp add: assm)
    proof - 
      assume assm2:"x \<noteq> \<epsilon>"
      have "fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd x)) \<sqsubseteq> 
            fun2\<cdot>(\<Union>state\<in>T. fun1 state (shd x))" 
        apply (rule monofun_cfun_arg)
        by (metis SetPcpo.less_set_def Sup_subset_mono assm image_mono) 
       then show 
         "S \<union> fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd x))\<cdot>(srt\<cdot>x) \<sqsubseteq>
         T \<union> fun2\<cdot>(\<Union>state\<in>T. fun1 state (shd x))\<cdot>(srt\<cdot>x)"
         apply (simp add: less_set_def)
         by (metis SetPcpo.less_set_def assm cfun_below_iff sup.coboundedI1 sup.coboundedI2)
     qed
   qed
 qed
         
lemma sreachable_fun_cont[simp]:"cont
        (\<lambda> S. \<Lambda> s. if s = \<epsilon> then S else S \<union> fun2\<cdot>(\<Union>state\<in>S. fun1 state (shd s))\<cdot>(srt\<cdot>s))"
  apply(rule Cpo.contI2,simp)
  apply (rule cfun_belowI)
   apply(simp add: contlub_cfun_fun contlub_cfun_arg)
   apply(subst lub_union_pairwise,simp_all) defer
  apply(subgoal_tac "(\<Squnion>i. fun2\<cdot>(\<Union>state\<in>Y i. fun1 state (shd x))\<cdot>(srt\<cdot>x)) = ( fun2\<cdot>(\<Squnion>i. \<Union>state\<in>Y i. fun1 state (shd x))\<cdot>(srt\<cdot>x))")
  apply simp
     apply(simp add: less_set_def lub_eq_Union)
    apply(subst contlub_cfun_arg) defer
    apply(subst contlub_cfun_fun,simp_all) defer
proof -
  fix Y x
  assume chain_Y: "chain Y"
     and chain_outer: "chain (\<lambda>i. \<Lambda> s. if s = \<epsilon> then Y i else Y i \<union> fun2\<cdot>(\<Union>state\<in>Y i. fun1 state (shd s))\<cdot>(srt\<cdot>s))"

  have "\<forall>i. Y i \<sqsubseteq> Y (i+1)"
    by (simp add: chain_Y po_class.chainE) 

  from this have inner: "\<forall>i. (\<Union>state\<in>Y i. fun1 state (shd x)) \<sqsubseteq>
                        ((\<Union>state\<in>Y (i+1). fun1 state (shd x)))"
    by (simp add: SetPcpo.less_set_def Sup_subset_mono image_mono) 

  show "chain (\<lambda>xa. fun2\<cdot>(\<Union>state\<in>Y xa. fun1 state (shd x))\<cdot>(srt\<cdot>x))"
    apply (rule chainI) 
    by (metis Cfun.cfun.Rep_cfun_inverse Suc_eq_plus1 cont_below_f inner monofun_cfun_fun)
next
  fix Y x
  assume chain_Y: "chain Y"
     and chain_outer: "chain (\<lambda>i. \<Lambda> s. if s = \<epsilon> then Y i else Y i \<union> fun2\<cdot>(\<Union>state\<in>Y i. fun1 state (shd s))\<cdot>(srt\<cdot>s))"

  have "\<forall>i. Y i \<sqsubseteq> Y (i+1)"
    by (simp add: chain_Y po_class.chainE) 


  show "chain (\<lambda>i. \<Union>state\<in>Y i. fun1 state (shd x))"
    apply (rule chainI)
    by (metis chain_Y po_class.chainE SetPcpo.less_set_def Sup_subset_mono image_mono) 

next
  fix Y x
  assume chain_Y: "chain Y"
     and chain_outer: "chain (\<lambda>i. \<Lambda> s. if s = \<epsilon> then Y i else Y i \<union> fun2\<cdot>(\<Union>state\<in>Y i. fun1 state (shd s))\<cdot>(srt\<cdot>s))"

  have "\<forall>i. Y i \<sqsubseteq> Y (i+1)"
    by (simp add: chain_Y po_class.chainE) 

  from this have inner: "\<forall>i. (\<Union>state\<in>Y i. fun1 state (shd x)) \<sqsubseteq>
                        ((\<Union>state\<in>Y (i+1). fun1 state (shd x)))"
    by (simp add: SetPcpo.less_set_def Sup_subset_mono image_mono) 

  show "chain (\<lambda>i. fun2\<cdot>(\<Union>state\<in>Y i. fun1 state (shd x)))"
    apply (rule chainI) 
    using cont_below_f inner by auto
qed

lemma sreachable_stepfun_mono[simp]: 
  "monofun (\<lambda>h. \<Lambda> S s. if s = \<epsilon> then S else S \<union> h\<cdot>(\<Union>state\<in>S. fun state (shd s))\<cdot>(srt\<cdot>s))"
proof (rule monofunI)
  fix x y :: "'a set \<rightarrow> 'b stream \<rightarrow> 'c set"
  assume assm: "x \<sqsubseteq> y"
    have "\<forall>S s. x\<cdot>(\<Union>state\<in>S. fun state (shd s))\<cdot>(srt\<cdot>s)\<sqsubseteq> 
          y\<cdot>(\<Union>state\<in>S. fun state (shd s))\<cdot>(srt\<cdot>s)" 
      by (meson assm monofun_cfun_fun)
  show "(\<Lambda> S s. if s = \<epsilon> then S else S \<union> x\<cdot>(\<Union>state\<in>S. fun state (shd s))\<cdot>(srt\<cdot>s)) \<sqsubseteq>
        (\<Lambda> S s. if s = \<epsilon> then S else S \<union> y\<cdot>(\<Union>state\<in>S. fun state (shd s))\<cdot>(srt\<cdot>s))" 
    apply (rule cfun_belowI)+
    apply (simp add: below_cfun_def less_set_def)
    by (metis SetPcpo.less_set_def assm le_supI2 monofun_cfun_fun)
qed

lift_definition sreachable_nda_step::"('state \<Rightarrow> 'msg \<Rightarrow> 'state set) \<Rightarrow> 
('state::type set \<rightarrow> 'msg::countable stream  \<rightarrow> 'state set) \<rightarrow> 'state::type set \<rightarrow> 'msg::countable stream  \<rightarrow> 'state set" is
"\<lambda> transition h . \<Lambda> S  s. if s = \<epsilon> then S else S \<union> h\<cdot>(\<Union>state\<in>S. transition state (shd s))\<cdot>(srt\<cdot>s)"
  apply (simp add: cfun_def)
  apply(rule Cpo.contI2,simp)
   apply (rule cfun_belowI)+
   apply(simp add: contlub_cfun_fun contlub_cfun_arg)
   apply(subst contlub_cfun_fun) defer apply simp
    apply(subst contlub_cfun_fun) defer apply simp
     apply auto
    apply(subst lub_unionL,simp_all)
proof -
  fix  Y::"nat \<Rightarrow> 'state set \<rightarrow> 'msg stream \<rightarrow> 'state set" 
    and x
    and y :: "'state \<Rightarrow> 'msg \<Rightarrow> 'state set"
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i. \<Lambda> S s. if s = \<epsilon> then S else S \<union> Y i\<cdot>(\<Union>state\<in>S. y state (shd s))\<cdot>(srt\<cdot>s))"


  show "chain (\<lambda>xa. \<Lambda> s. if s = \<epsilon> then x else x \<union> Y xa\<cdot>(\<Union>state\<in>x. y state (shd s))\<cdot>(srt\<cdot>s))"
    apply (rule chainI)
    apply (rule cfun_belowI)
    apply (simp add: below_cfun_def less_set_def)
    by (metis SetPcpo.less_set_def a1 monofun_cfun_fun
        po_class.chainE sup.coboundedI2)
next
  fix  Y::"nat \<Rightarrow> 'state set \<rightarrow> 'msg stream \<rightarrow> 'state set" 
    and x
    and y :: "'state \<Rightarrow> 'msg \<Rightarrow> 'state set"
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i. \<Lambda> S s. if s = \<epsilon> then S else S \<union> Y i\<cdot>(\<Union>state\<in>S. y state (shd s))\<cdot>(srt\<cdot>s))"


  show "chain (\<lambda>xa. \<Lambda> s. if s = \<epsilon> then x else x \<union> Y xa\<cdot>(\<Union>state\<in>x. y state (shd s))\<cdot>(srt\<cdot>s))"
    apply (rule chainI)
    apply (rule cfun_belowI)
    apply (simp add: below_cfun_def less_set_def)
    by (metis SetPcpo.less_set_def a1 monofun_cfun_fun
        po_class.chainE sup.coboundedI2)
qed

definition sreachable_nda_all::"('state \<Rightarrow> 'msg \<Rightarrow> 'state set) \<Rightarrow> 'state::type set \<rightarrow> 'msg::countable stream  \<rightarrow> 'state set" where
"sreachable_nda_all transition = fix\<cdot>(sreachable_nda_step transition)"

lemma sreachable_nda_all_mono [simp]:"mono (\<lambda>h S s. if s = \<epsilon> then S else S \<union> h (\<Union>state\<in>S. transition state (shd s)) (srt\<cdot>s))"
unfolding mono_def apply auto
  apply(rule le_funI)+
  apply(case_tac xb,simp_all)
  using le_funD 
  by (metis le_supI2)

lemma sreachable_nda_all_bot[simp]:
  "sreachable_nda_all transition\<cdot>Init\<cdot>\<epsilon> = Init"
  unfolding sreachable_nda_all_def sreachable_nda_step.rep_eq
  apply(subst fix_eq)
  by(simp add: sreachable_nda_step.rep_eq)

lemma sreachable_nda_all_one[simp]:
  "sreachable_nda_all transition\<cdot> Init\<cdot>(\<up>a) =  Init \<union> (\<Union>state\<in>Init. transition state a)"
  unfolding sreachable_nda_all_def
  apply(subst fix_eq)
  apply(subst sreachable_nda_step.rep_eq,simp)
apply(subst fix_eq)
  by(subst sreachable_nda_step.rep_eq,simp)

lemma sreachable_nda_all_unfold:
  "sreachable_nda_all transition\<cdot> Init\<cdot>(\<up>a \<Zcat> s) =  Init \<union> sreachable_nda_all transition\<cdot>(\<Union>state\<in>Init. transition state a)\<cdot>s"
  unfolding sreachable_nda_all_def
  apply(subst fix_eq)
  by(subst sreachable_nda_step.rep_eq,simp)


definition sreachable_nda::"('state \<Rightarrow> 'msg \<Rightarrow> 'state set) \<Rightarrow> 'state::type set \<Rightarrow> 'msg::countable stream  \<Rightarrow> 'state set" where
"sreachable_nda transition = lfp (\<lambda> h S s. if s = \<epsilon> then S else h (\<Union>state\<in>S. transition state (shd s)) (srt\<cdot>s))"

lemma sreachable_nda_mono [simp]:"mono (\<lambda>h S s. if s = \<epsilon> then S else h (\<Union>state\<in>S. transition state (shd s)) (srt\<cdot>s))"
unfolding mono_def apply auto
  apply(rule le_funI)+
  apply(case_tac xb,simp_all)
  by (simp add: le_funD)

lemma sreachable_nda_bot[simp,code]:
  "sreachable_nda transition Init \<epsilon> = Init"
  unfolding sreachable_nda_def
  by(subst lfp_fixpoint[symmetric],simp_all)

lemma sreachable_nda_one[simp]:
  "sreachable_nda transition Init (\<up>a) =  (\<Union>state\<in>Init. transition state a)"
  unfolding sreachable_nda_def
  apply(subst lfp_unfold,simp_all)
  unfolding sreachable_nda_def[symmetric]
  by simp

lemma sreachable_nda_unfold:
  "sreachable_nda transition Init (\<up>a \<Zcat> s) =  sreachable_nda transition (\<Union>state\<in>Init. transition state a) s"
  unfolding sreachable_nda_def
  by(subst lfp_unfold,simp_all)

lemma sreachable_nda_code_unfold[code]:
  "sreachable_nda transition Init (updis a && s) =  sreachable_nda transition (\<Union>state\<in>Init. transition state a) s"
  by (simp add: lscons_conv sreachable_nda_unfold)

definition sreachableStates::"('state::type,'msg,'out::conc)automaton \<Rightarrow> 'msg::countable stream  \<rightarrow> 'state set" where
"sreachableStates aut = sreachable_nda_all (\<lambda> s m. fst ` ((autTransition\<cdot>aut) s m))\<cdot>(fst ` (autInitConfig\<cdot>aut))"

end
