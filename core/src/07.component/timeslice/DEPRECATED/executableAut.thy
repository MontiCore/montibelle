theory executableAut                                       
  imports autDeterminization ndaLocale daLocale
begin

default_sort type

type_synonym seed = "natural \<times> natural"


text\<open>This section mainly adds a new locale to the framework that defines a deterministic automaton 
which is executable and might behave non-deterministically from an outside perspective.
There are a few restrictions needed for the execution, the main one being to never have infinitely 
many transitions or starting configurations. Furthermore, the transition function and 
initial configuration must be complete (or completed before the locale interpretation). Beside these
assumptions, no new ones are added compared to the @{locale daGen} or @{locale ndaGen} locales.\<close>






locale ndaExec =
  fixes ndaTransition::"('param::type \<times>seed) \<Rightarrow> 'state::{type,random} \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitConfig:: "('param\<times> seed) \<Rightarrow> ('state \<times> 'out::{tschan,finite}\<^sup>\<Omega>) list"
      and fin::"'a \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"
      and fout::"'b \<Rightarrow> 'out \<Rightarrow> M"
  assumes execsbegenin:"sbeGen fin"
      and execsbegenout:"sbeGen fout"
      and initconfnotempty:"\<And>p s. ndaInitConfig (p,s) \<noteq> []"
begin

text\<open>The automaton created through @{locale ndaGen} has no seed, as it is a regular NDA. However,
  the deterministic automaton should contain the seed used to determine the chosen transition
  function or initial state. The following function therefore lifts the fixed input transition 
  function to an pseudo-seeded transition function. This is necessary, since the type of the
  parameter used to interpretate the @{locale daGen} has to be the same for the initial config
  and the transition function.\<close>

text\<open>The following two definitions use the set instead of the list representation for possible 
transitions and configurations. These are the parameters for the @{locale ndaGen} locale to define
a non-deterministic automaton.\<close>

definition "ndaGenTransition p s i = set (ndaTransition p s i)"


definition "ndaGenInitConfig p = set (ndaInitConfig p)"
definition "completeTransition \<equiv> \<lambda> p s i. let out = ndaTransition p (fst s) i in (if out=[] 
                                            then [rnd (snd s)] 
                                            else out)"

lemma completetransition_h [code_abbrev]:
          "(\<lambda> p s i. let out = ndaTransition p (fst s) i in (if out=[] 
                                            then [rnd (snd s)] 
                                            else out)) = completeTransition"
  by (simp add: completeTransition_def)

definition "completeConfig \<equiv> (\<lambda>p. let out = ndaInitConfig p in (if out=[] 
                                then map (apsnd (Rep_cfun (sbeGen.setterSB fout))) 
                                     [rnd (snd p)] 
                                else out))"

lemma [code_abbrev]:" (\<lambda>p. let out = ndaInitConfig p in (if out=[] 
                                then map (apsnd (Rep_cfun (sbeGen.setterSB fout))) 
                                     [rnd (snd p)] 
                                else out)) = completeConfig"
  by(simp add: completeConfig_def)

definition "daGenTransition \<equiv> (\<lambda> p s i. 
                              let ((ns,out),seed) = Random.select (completeTransition p s i) (snd s)
                               in ((ns,seed),out))"

lemma [code_abbrev]:"(\<lambda> p s i. let ((ns,out),seed) = Random.select (completeTransition p s i) (snd s)
                               in ((ns,seed),out)) = daGenTransition"
  by(simp add: daGenTransition_def)

                                                                             
definition "daGenInitConfig  \<equiv> (\<lambda> p. let ((inits,initout),seed) = Random.select (completeConfig p) (snd p) in 
                                    ((inits,seed),initout))"

lemma[code_abbrev]:"(\<lambda>p. let ((inits,initout),seed) = Random.select (completeConfig p) (snd p) in 
                                    ((inits,seed),initout)) = daGenInitConfig"
  by(simp add: daGenInitConfig_def)

definition "daGenInitState = (\<lambda>p. fst (daGenInitConfig p))"

lemma [code_abbrev]:"(\<lambda>p. fst (daGenInitConfig p)) = daGenInitState"
  by(simp add: daGenInitState_def)

definition "daGenInitOut = (\<lambda>p. snd (daGenInitConfig p))"

lemma[code_abbrev]:"(\<lambda>p. snd (daGenInitConfig p)) = daGenInitOut"
  by(simp add: daGenInitOut_def)
(*
definition "dastatecode \<equiv> (\<lambda> p. sscanlAutOne (daGenTransition p))"

lemma dastatecode_h [code_abbrev, simp]:
   "sscanlAutOne (\<lambda> s i. let ((ns,out),seed) = Random.select (completeTransition p s i) (snd s) in
                                    ((ns,seed),out)) = dastatecode p"
  by(simp add: dastatecode_def daGenTransition_def)

definition "dastatecode_exec \<equiv> (\<lambda> p s i. dastatecode p s\<cdot>i)"

definition "dacode \<equiv> (\<lambda> p input. (sbeGen.getterSB fout \<cdot> (daGenInitOut p)) \<Zcat> ((dastatecode p (daGenInitState p))\<cdot>input))"
*)
end
text\<open>This is enough to instantiate the @{locale ndaExec} locale as a sub-locale of @{locale ndaGen} 
and @{locale daGen} by using the locales transition and initial configuration definitions.\<close>

sublocale ndaExec \<subseteq> ndaGen ndaGenTransition ndaGenInitConfig fin fout
  by (simp add: ndaGen_def execsbegenin execsbegenout ndaGenInitConfig_def initconfnotempty)

sublocale ndaExec \<subseteq> daGen daGenTransition daGenInitState daGenInitOut fin fout
  by (simp add: daGen_def sbegenin sbegenout)

context ndaExec
begin

(*
lemma ndarefda2nda: "ndaSem (da2nda (da p)) \<subseteq> daSem p"
  apply(simp only: Sem_def)
  apply(rule ndastateref [where f="fst"])
  apply(simp add: ndaTransition.rep_eq da2nda.rep_eq nda.rep_eq da_def dtransition_def 
      transition_def transitionH_def dtransitionH_def daGenTransition_def ndaGenTransition_def)
  apply(simp add: case_prod_unfold Let_def completeTransition_def)
  apply(case_tac "ndaTransition p (fst s) (sbeGen.getter fin sbe) = []",simp_all)
  using image_iff apply fastforce
  apply (metis (mono_tags) apsnd_conv imageI select)
  apply(simp add: ndaInitConfig.rep_eq da2nda.rep_eq da_def daGenInitState_def daGenInitConfig_def 
      daGenInitOut_def case_prod_unfold Let_def completeConfig_def)
  by(simp add: nda.rep_eq ndaGenInitConfig_def select)


(*final refinement lemma*)
theorem execrefnda:
  shows "dSem p \<subseteq> Sem p"
  using dSem_def ndarefda2nda sem_def
  by (simp add: subset_eq)
*)
text\<open>The theorem shows that the parametric singleton deterministic semantic @{const dSem} from
@{locale daGen} is a subset of the parametric semantic @{const Sem} of the non-deterministic
automaton from @{locale ndaGen}.\<close>


(*
theorem dstatesem2sscanl: (*code_abbrev doesn't work*)
  assumes "chDom TYPE('in) \<noteq> {}"
  assumes "chDom TYPE('out) \<noteq> {}"
  shows "dastatecode p state = sbeGen.getterSB fout oo stateSem p state oo sbeGen.setterSB fin"
  apply(rule cfun_eqI)
  apply(simp add: stateSem_def oo_def)
  by(subst daut2sscanl [where param="p"],simp_all add: da_def dastatecode_def assms)

theorem sscanlpredstatesem: (*code_abbrev doesn't work*)
  shows "dastatecode p state\<cdot>i \<sqsubseteq> (sbeGen.getterSB fout oo stateSem p state oo sbeGen.setterSB fin)\<cdot>i"
  apply(simp add: stateSem_def oo_def dastatecode_def)
proof(induction i arbitrary: state)
  case adm
  then show ?case 
    apply(rule adm_all)
    by(rule adm_below,simp,simp)
next
  case bottom
  then show ?case 
    by simp
next
  case (step a i)
  then show ?case (*dont judge me*)
    apply simp
    apply(subst sbeGen.settersb_unfold)
    using sbegenin apply blast
    apply (simp)
    apply(subgoal_tac "daNextOut (da p) state (sbeGen.setter fin a) = sbe2sb (sbeGen.setter fout (snd (daGenTransition p state a)))")
    apply simp
    apply(subst sbeGen.gettersb_unfold)
    using sbegenout apply blast
    apply(subst sbeGen.get_set)
    using sbegenout apply blast
    apply(rule cont_pref_eq1I)
    apply(subgoal_tac "(daNextState (da p) state (sbeGen.setter fin a)) = fst (daGenTransition p state a)",simp)
    apply(simp_all add: da_def dtransition_def dtransitionH_def)
    apply(subst sbeGen.get_set)
    using sbegenin apply blast
     apply simp
    apply(subst sbeGen.get_set)
    using sbegenin apply blast
    by simp
qed


lemma weakdsem2sscanl:
  assumes "daInitOut (da p) = \<bottom> "
  assumes "chDom TYPE('in) \<noteq> {}"
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"dastatecode p (daGenInitState p)\<cdot>input= ((sbeGen.getterSB fout) oo (sem p) oo (sbeGen.setterSB fin))\<cdot>input"
  apply(simp add: sem_def daSem_def assms)
  by (simp add: da_def dstatesem2sscanl assms stateSem_def)

lemma strongdsem2sscanl:
  assumes "chDom TYPE('in) \<noteq> {}"
  assumes "chDom TYPE('out) \<noteq> {}"
  assumes "\<And> c. #(daInitOut (da p) \<^enum> c) = 1 "
  shows"dacode p input= ((sbeGen.getterSB fout) oo (sem p) oo (sbeGen.setterSB fin))\<cdot>input"
  apply(simp add: sem_def daSem_def)
  apply(subgoal_tac "\<exists>sbe. daInitOut (da p) = sbe2sb sbe", auto)
  apply (smt assms(1) assms(2) dAutomaton.select_convs(2) dAutomaton.select_convs(3) da_def dacode_def
        dastatecode_def daut2sscanl sbconc_bot_r sbeGen.gettersb_realboteps sbeGen.gettersb_unfold 
        sbegenout sconc_snd_empty)
  by (metis len2sbe_ex assms(3))



text\<open>Sometimes it might be useful to proof that the executable automaton is a refinement of a not
executable one defined using the @{locale ndaGen} locale. To proof the refinement, it is enough to
show that the transition and configuration options of the executable automaton are a subset of the 
non-executable options.\<close>
theorem execrefinesset:
  assumes "\<And>s i. set (ndaTransition p s i) \<subseteq> trans2 (fst p) s i"
  and "set (ndaInitConfig p) \<subseteq> init2 (fst p)"
  and "\<And>s sbe. ndaTransition p s sbe = [] \<Longrightarrow> trans2 (fst p) s sbe = {}"
  and "ndaInitConfig p = [] \<Longrightarrow> init2 (fst p) = {}"
  shows "Sem p \<subseteq> ndaGen.Sem trans2 init2 fin fout (fst p)"
  apply(rule ndastaterefine_ndagen_sem[of ndaGenTransition p id])
  apply (simp_all add: assms ndaGenTransition_def ndaGenInitConfig_def 
         ndaGen_axioms case_prod_unfold)
  using assms by auto[2]
*)
end




locale ndaExecWeak =
  fixes ndaNoSeedTransition::"('param::type) \<Rightarrow> 'state::{type,random} \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitState:: "'param \<Rightarrow> 'state list"
      and fin::"'a \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"
      and fout::"'b \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes execsbegeninweak:"sbeGen fin"
      and execsbegenoutweak:"sbeGen fout"
begin

definition initConfig::"('param \<times> seed) \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) list" where
"initConfig p \<equiv> (let out = ndaInitState (fst p) in 
                (if out = [] then [(rnd (snd p), \<bottom>)]
                          else map (\<lambda>out. (out,(\<bottom>))) (ndaInitState (fst p))))"

lemma [code_abbrev]:"((let out = ndaInitState (fst p) in 
                (if out = [] then [(rnd (snd p), botsb)]
                          else map (\<lambda>out. (out,(botsb))) (ndaInitState (fst p))))) = initConfig p"
  by(simp add: initConfig_def botsb_eq)


end

sublocale ndaExecWeak \<subseteq> ndaExec "(\<lambda>(p,seed). ndaNoSeedTransition p)" initConfig fin fout
  by (simp add: execsbegeninweak execsbegenoutweak ndaExec_def initConfig_def)

context ndaExecWeak
begin

definition "completeState \<equiv> (\<lambda> p. let out = ndaInitState (fst p) in (if out=[] 
                                then [rnd (snd p)]
                                else out))"

lemma [code_abbrev]: "(\<lambda> p. let out = ndaInitState (fst p) in (if out=[] 
                                then [rnd (snd p)]
                                else out)) = completeState"
  by (simp add: completeState_def)

definition "comInitState \<equiv> (\<lambda> p. let (inits,seed) = Random.select (completeState p) (snd p) in 
                                    (inits,seed))"

lemma [code_abbrev]: "(\<lambda> p. let (inits,seed) = Random.select (completeState p) (snd p) in 
                                    (inits,seed)) = comInitState"
  by (simp add: comInitState_def)


declare ranselect_zero [simp]

lemma same_state [code_abbrev]: "(comInitState p) = (daGenInitState p)"
  apply(auto simp add: daGenInitState_def daGenInitConfig_def completeConfig_def initConfig_def comInitState_def completeState_def case_prod_unfold Let_def Random.select_def)
  by (metis eq_fst_iff length_greater_0_conv nat_of_natural_inverse natural_of_nat_of_nat nth_map of_nat_less_iff range zero_natural.rep_eq)

lemma weakinitout[simp]:"daInitOut (da p) = \<bottom>"
  apply(simp add: da_def)
  apply(simp add: daGen_axioms daGen.da_def daGenInitOut_def daGenInitConfig_def case_prod_unfold 
        Let_def completeConfig_def initConfig_def,auto)
  apply (metis select list.distinct(1) list.set_cases set_ConsD snd_conv)
  by (metis (no_types, lifting) Nil_is_map_conv ex_map_conv snd_conv select)

lemma weakinitout2: "\<And> p. ((daGenInitOut p) = \<bottom>)"
  apply(auto simp add: daGenInitOut_def daGenInitConfig_def completeConfig_def Let_def case_prod_unfold)
   apply (metis List.map.compositionality initConfig_def length_greater_0_conv map_eq_imp_length_eq not_Cons_self2)
  apply(auto simp add: initConfig_def Random.select_def)
   apply (metis (mono_tags) case_prod_beta' fst_conv less_natural.rep_eq less_one nth_Cons_0 one_natural.rep_eq range snd_conv zero_less_one)
proof -
  fix a :: 'param and aa :: natural and b :: natural
  assume "ndaInitState a \<noteq> []"
  then have "nat_of_natural (fst (Random.range (of_nat (length (ndaInitState a))) (aa, b))) < length (ndaInitState a)"
    by (metis (no_types) length_greater_0_conv less_natural.rep_eq nat_of_natural_of_nat range zero_natural.rep_eq)
  then show "snd (fst (case Random.range (of_nat (length (ndaInitState a))) (aa, b) of (n, x) \<Rightarrow> (map (\<lambda>s. (s, \<bottom>::'out\<^sup>\<Omega>)) (ndaInitState a) ! nat_of_natural n, x))) = \<bottom>"
    by (simp add: case_prod_beta')
qed

lemma "dacode_exec = dacode"
  oops

lemma weakinitstate[simp]:"daInitState (da p) = daGenInitState p"
  by(simp add: da_def)
(*
lemma weakdsem2sscanl2:
  assumes "chDom TYPE('in) \<noteq> {}"
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"dastatecode p (daGenInitState p)\<cdot>input= ((sbeGen.getterSB fout) oo (sem p) oo (sbeGen.setterSB fin))\<cdot>input"
  by(simp add: assms weakdsem2sscanl)

lemma dacode2dastatecode_exec:
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"dastatecode_exec p (daGenInitState p)= dacode p"
  apply(subst fun_eq_iff,rule)
  apply(simp add: dacode_def)
  apply(subgoal_tac "daGenInitOut p = \<bottom>")
   apply(simp add: completeConfig_def Let_def,auto)
  apply(subst sbeGen.gettersb_realboteps)
  using sbegenout apply blast
  using assms apply blast
  apply(simp add: dastatecode_exec_def)
  apply(auto simp add: initConfig_def daGenInitOut_def daGenInitConfig_def completeConfig_def case_prod_unfold Let_def select)
  apply (metis select list.distinct(1) list.set_cases set_ConsD snd_conv)
  using select
proof -
  assume a1: "ndaInitState (fst p) \<noteq> []"
  have f2: "\<forall>ss s p. snd p = (s::'out\<^sup>\<Omega>) \<or> p \<notin> set (map (\<lambda>sa. (sa::'state, s)) ss)"
    by (metis (no_types) ex_map_conv snd_conv)
  have "map (\<lambda>s. (s, \<bottom>::'out\<^sup>\<Omega>)) (ndaInitState (fst p)) \<noteq> []"
    using a1 by (metis Nil_is_map_conv)
  then show "snd (fst (Random.select (map (\<lambda>s. (s, \<bottom>::'out\<^sup>\<Omega>)) (ndaInitState (fst p))) (snd p))) = \<bottom>"
    using f2 select by blast
qed
*)
end


locale ndaExecStrong =
  fixes ndaTransition::"('param::type) \<Rightarrow> 'state::{type,random} \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitRawConfig:: "'param \<Rightarrow> ('state \<times> 'b) list"
      and fin::"'a \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"
      and fout::"'b \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes execsbegeninstrong:"sbeGen fin"
      and execsbegenoutstrong:"sbeGen fout"
begin


definition config::"('param\<times>seed) \<Rightarrow> ('state \<times> 'b) list" where
"config p \<equiv> let out = ndaInitRawConfig (fst p) in (if out=[] 
                                then [rnd (snd p)] 
                                else out)"

lemma [code_abbrev]:" (let out = ndaInitRawConfig (fst p) in (if out=[] 
                                then [rnd (snd p)] 
                                else out)) = config p"
  by(simp add: config_def)

definition initConfigH::"('param\<times>seed) \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>) list" where
"initConfigH p \<equiv> map (apsnd (sbeGen.setter fout)) (config p)"

lemma [code_abbrev]:"map (apsnd (sbeGen.setter fout)) (config p) = initConfigH p "
  by(simp add: initConfigH_def)


definition initConfig::"('param\<times>seed) \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) list" where
"initConfig p \<equiv> map (apsnd sbe2sb) (initConfigH p)"

lemma[code_abbrev]:"( map (apsnd sbe2sb) (initConfigH p)) = initConfig p"
  by(simp add: initConfig_def)

end

sublocale ndaExecStrong \<subseteq> ndaExec "(\<lambda>(p,s). ndaTransition p)" initConfig fin fout
  by (simp add: execsbegeninstrong execsbegenoutstrong ndaExec_def initConfig_def initConfigH_def 
      config_def Let_def)

context ndaExecStrong begin

definition "completeState \<equiv> (\<lambda> p. let out = ndaInitRawConfig (fst p) in (if out=[] 
                                then [rnd (snd p)]
                                else out))"

definition "comConfig \<equiv> (\<lambda> p. let ((inits, out),seed) = Random.select (completeState p) (snd p) in 
                                    ((inits,seed),out))"

declare ranselect_zero [simp]

lemma config_reduce : "apsnd sbe2sb (apsnd (sbeGen.setter fout) (comConfig p)) = (daGenInitConfig p)"
  apply(auto simp add: daGenInitConfig_def case_prod_unfold Let_def completeConfig_def comConfig_def completeState_def initConfig_def initConfigH_def config_def Random.select_def)
  apply (metis (no_types, lifting) fst_apsnd length_greater_0_conv length_map less_natural.rep_eq map_map nat_of_natural_of_nat nth_map range zero_natural.rep_eq)  
  by (metis comp_apply length_greater_0_conv less_natural.rep_eq nat_of_natural_of_nat nth_map range snd_apsnd zero_natural.rep_eq)


lemma sbgetset_eq : 
  shows "(inv (sbeGen.setter fout)) ((inv sbe2sb) (sbe2sb ((sbeGen.setter fout) input))) = input"
  apply(simp add: sbeinv)
  by (simp add: sbeGen.set_inj sbegenout)

lemma comconfig_reduce: 
    "apsnd (inv (sbeGen.setter fout)) (apsnd (inv sbe2sb) (daGenInitConfig p))
       = (comConfig p)"
  apply(auto simp add: daGenInitConfig_def completeConfig_def case_prod_unfold Let_def comConfig_def completeState_def rnd_def initConfig_def initConfigH_def config_def Random.select_def)
  using sbgetset_eq apply blast
  apply (metis (no_types, lifting) fst_apsnd length_greater_0_conv length_map less_natural.rep_eq map_map nat_of_natural_of_nat nth_map range zero_natural.rep_eq)
  by (metis (no_types, lifting) length_greater_0_conv length_map less_natural.rep_eq map_map nat_of_natural_of_nat nth_map range sbgetset_eq snd_apsnd zero_natural.rep_eq)

(*
definition "dacode_exec \<equiv> 
      (let daConfig = (\<lambda>p. apsnd (inv (sbeGen.setter fout)) (apsnd (inv sbe2sb) (daGenInitConfig p))) in
      (\<lambda> p input. \<up>(snd(daConfig p))
                   \<Zcat> ((dastatecode p (fst(daConfig p)))\<cdot>input)))"

lemma dacode_reduce [code]: "dacode_exec = (\<lambda> p input. \<up>(snd((\<lambda> p. let ((inits, out),seed) = Random.select ((\<lambda> p. let out = ndaInitRawConfig (fst p) in (if out=[] 
                                then [rnd (snd p)]
                                else out)) p) (snd p) in 
                                    ((inits,seed),out)) p)) \<Zcat> ((dastatecode p (fst((\<lambda> p. let ((inits, out),seed) = Random.select ((\<lambda> p. let out = ndaInitRawConfig (fst p) in (if out=[] 
                                then [rnd (snd p)]
                                else out)) p) (snd p) in 
                                    ((inits,seed),out)) p)))\<cdot>input))"
  apply (simp add: dacode_exec_def comConfig_def completeState_def)
proof -
  have "\<forall>p s. \<up>(inv (sbeGen.setter fout) (inv sbe2sb (snd (daGenInitConfig p)))) \<Zcat> dastatecode p (fst (daGenInitConfig p))\<cdot> s = \<up>(snd (case Random.select (if ndaInitRawConfig (fst p) = [] then [rnd (snd p)] else ndaInitRawConfig (fst p)) (snd p) of (x, xa) \<Rightarrow> (case x of (s, b) \<Rightarrow> \<lambda>p. ((s, p), b)) xa)) \<Zcat> dastatecode p (fst (case Random.select (if ndaInitRawConfig (fst p) = [] then [rnd (snd p)] else ndaInitRawConfig (fst p)) (snd p) of (x, xa) \<Rightarrow> (case x of (s, b) \<Rightarrow> \<lambda>p. ((s, p), b)) xa))\<cdot> s"
    by (metis (no_types) comConfig_def comconfig_reduce completeState_def fst_apsnd snd_apsnd)
  then show "(\<lambda>p s. \<up>(inv (sbeGen.setter fout) (inv sbe2sb (snd (daGenInitConfig p)))) \<Zcat> dastatecode p (fst (daGenInitConfig p))\<cdot> s) = (\<lambda>p s. \<up>(snd (case Random.select (let ps = ndaInitRawConfig (fst p) in if ps = [] then [rnd (snd p)] else ps) (snd p) of (x, xa) \<Rightarrow> (case x of (s, b) \<Rightarrow> \<lambda>p. ((s, p), b)) xa)) \<Zcat> dastatecode p (fst (case Random.select (let ps = ndaInitRawConfig (fst p) in if ps = [] then [rnd (snd p)] else ps) (snd p) of (x, xa) \<Rightarrow> (case x of (s, b) \<Rightarrow> \<lambda>p. ((s, p), b)) xa))\<cdot> s)"
    by meson
qed
*)
lemma strongoutsbe:"\<exists>sbe. daInitOut (da p) = sbe2sb sbe"
  apply(simp add: da_def daGenInitOut_def daGenInitConfig_def case_prod_unfold daGen_axioms 
        daGen.da_def Let_def completeConfig_def initConfig_def,auto)
  apply(simp add: initConfigH_def Let_def config_def)
  apply (metis not_Cons_self2)
proof -
  assume "initConfigH p \<noteq> []"
  then have "fst (Random.select (map (apsnd sbe2sb) (initConfigH p)) (snd p)) \<in> set (map (apsnd sbe2sb) (initConfigH p))"
    by (meson list.map_disc_iff select)
  then show "\<exists>s. snd (fst (Random.select (map (apsnd sbe2sb) (initConfigH p)) (snd p))) = sbe2sb s"
    by auto
qed
(*
lemma strongdsem2sscanl2:
  assumes "chDom TYPE('in) \<noteq> {}"
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"dacode p input= ((sbeGen.getterSB fout) oo (sem p) oo (sbeGen.setterSB fin))\<cdot>input"
  apply(rule strongdsem2sscanl,simp_all add: assms)
  apply(subgoal_tac "\<exists>sbe. daInitOut (da p) = sbe2sb sbe", auto)
  by(simp_all add: assms sbe2slen_1 strongoutsbe)
*)
end
hide_type seed

end
