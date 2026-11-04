theory daLocale

imports dAutomaton_causal

begin


text\<open>The semantic mapping allows us to verify the behaviour of
components with \glspl{spf}. Since these components are modeled as 
automatons, we introduce two locals for constructing and
transforming automatons. These locals are used in the generation
process, where a \gls{MontiArc} model provides the information about
the automatons components. Hence, they provide us with a state type,
message types, the transition function directly obtained from the
model and an initial state. Since the \gls{MontiArc} model has no
\glspl{sb}, @{type sbElem}s or the @{type M}, the transition 
function also does not use any of these types. Instead it uses 
exactly the types from its model. But the message types do not have 
to be in type @{type M} to construct an automaton in Isabelle,
because the local @{locale sbeGen} is also 
interpreted with constructors provided by the generator and we can
utilize them to define the automaton internally and independently.\<close>

locale daGen =
  fixes daTransition :: "'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState :: "'param \<Rightarrow> 'state"
  and   daInitOut :: "'param \<Rightarrow> 'out::{chan,finite}\<^sup>\<Omega>"
  and fin :: "'a \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"
  and fout :: "'b \<Rightarrow> 'out \<Rightarrow> M"
  assumes dasbegenin: "sbeGen fin"
      and dasbegenout: "sbeGen fout"
begin

text\<open>Using the setter, getter and \gls{MontiArc} transition function
we define the corresponding transition function for our automaton by
applying the provided getter to its input @{type sbElem}, running
the \gls{MontiArc} transition function and then using the setter to 
convert its output back to a @{type sbElem}. The state type is not
converted.\<close> 

definition dtransitionH :: "'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>)" where
"dtransitionH param state sbe = apsnd (sbeGen.setter fout) 
                (daTransition param state (sbeGen.getter fin sbe))"

definition dtransition :: "'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>)" where
"dtransition param state sbe = apsnd sbe2sb (dtransitionH param state sbe)"

text\<open>Then the \gls{deterministic} automaton is defined with the initial
state and @{const dtransition}.\<close>

definition da::"'param \<Rightarrow> ('state, 'in, 'out) dAutomaton" where
"da param = \<lparr> daTransition = dtransition param,
              daInitState  = daInitialState param,
              daInitOut    = daInitOut param \<rparr>"

lemma transition_weak:
  assumes "chDom TYPE('out) \<noteq> {}"
  shows"#(daNextOut (da param) s i  \<^enum>  c) = (1::lnat)"
  apply(simp add: da_def dtransition_def)
  apply(cases "chDom TYPE('out) = {}",simp_all add: assms)
  by (simp add: assms sbe2slen_1)
 
text\<open>Often components output behaviour depends on the input. These
components have a non-empty input and output domain and so does
their semantic. We can then represent their components behaviour by
reducing its semantic with the setter and getter to a 
@{const sscanlAOne} mapping that uses the \gls{MontiArc} transition
function and works completely over streams. This is an important 
part of the verification process because it is often easier to proof
properties directly for the streams of a bundle and not for the
bundle itself. If the input domain is empty, the source component 
has no input and its output is predetermined.\<close>
(*
theorem daut2sscanl: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "sbeGen.getterSB fout \<cdot>
  (daStateSem (da param) state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   sscanlAutOne (daTransition param) state\<cdot>input"
  using assms apply(induction input arbitrary: state)
  apply(simp_all)
  apply (simp add: dastatesem_strict sbeGen.gettersb_boteps sbeGen.settersb_strict dasbegenin dasbegenout)
  apply (simp add: sbeGen.settersb_unfold dasbegenin da_def dtransition_def)
  by (simp add: sbeGen.get_set sbeGen.gettersb_unfold dasbegenin dasbegenout dtransitionH_def)

lemma daut2sscanl2:
  assumes "\<not>chDomEmpty TYPE('in)"
  shows "(daStateSem (da p) state\<cdot>input) =  
   sbeGen.setterSB fout\<cdot>(sscanlAutOne (daTransition p) state\<cdot>
                                        (sbeGen.getterSB fin\<cdot>input))"
proof (induction input)
  oops
*)
lemma emptychan_eq[simp]:
  "chDomEmpty TYPE('out) \<Longrightarrow> (sb1::'out\<^sup>\<Omega>) = sb2"
  by (metis (full_types)sbtypeepmpty_sbbot)



lemma setterListFin_unfolding: "sbeGen.setterList fin (x#xs) = 
      (sbeGen.setter fin x)  \<Zcat>\<^sup>\<surd>  (sbeGen.setterList fin xs)"
  using sbeGen.setterList.simps(2) dasbegenin by blast

lemma setterListFout_unfolding: "sbeGen.setterList fout (x#xs) = 
      (sbeGen.setter fout x)  \<Zcat>\<^sup>\<surd>  (sbeGen.setterList fout xs)"
  using sbeGen.setterList.simps(2) dasbegenout by blast

lemma assumes "\<not>chDomEmpty TYPE('in)"
  shows "daStateSem (da p) state\<cdot>(sbeGen.setterList fin input) = 
        sbeGen.setterList fout (stateSemList (daTransition p) state input)"
  proof(induction input arbitrary: state)
  case Nil
  have a1: "stateSemList (daTransition p) state [] = []" 
    by (simp add: stateSemList_def)
  then have a2: "sbeGen.setterList fout [] = \<bottom>"
    by (simp add: sbeGen.setterList.simps(1) dasbegenout)
  then have a3: "sbeGen.setterList fin [] = \<bottom>"
    by (simp add: sbeGen.setterList.simps(1) dasbegenin)
  then have a4: "sbeGen.setterList fout (stateSemList (daTransition p) state []) = \<bottom>"
    by (simp add: a1 a2)
  then have a5: "daStateSem (da p) state\<cdot>\<bottom> = \<bottom>"
    by (simp add: a4 assms dastatesem_strict)
  then show ?case by (simp add: a3 a4)
next
  case (Cons a input)
  have b1: "stateSemList (daTransition p) state (a#input) = snd((daTransition p) state a) # 
                      stateSemList (daTransition p) (fst ((daTransition p) state a)) input"
    by (simp add: stateSemList_def)
  then have b2: "sbeGen.setterList fout (stateSemList (daTransition p) state (a # input)) = 
    (sbeGen.setter fout (snd((daTransition p) state a))) \<Zcat>\<^sup>\<surd> 
   (sbeGen.setterList fout (stateSemList (daTransition p) (fst ((daTransition p) state a)) input))"
    by (simp add: b1 sbeGen.setterList.simps(2) dasbegenout)
  then have b3: "sbeGen.setterList fin (a # input) = 
    (sbeGen.setter fin  a) \<Zcat>\<^sup>\<surd> (sbeGen.setterList fin input)"
    using sbeGen.setterList.simps(2) dasbegenin by blast
  then have b4: "sbe2sb (sbeGen.setter fout (snd((daTransition p) state a))) = 
     snd (dAutomaton.daTransition (da p) state (sbeGen.setter fin a))"
    by (simp add: da_def sbeGen.get_set dasbegenin dtransitionH_def dtransition_def)

  then have b5: "daStateSem (da p) state\<cdot>(sbeGen.setterList fin (a # input)) =  
              snd (dAutomaton.daTransition (da p) state (sbeGen.setter fin a)) \<Zcat>\<^sup>\<Omega> 
              daStateSem (da p) (fst ((daTransition p) state a))\<cdot>(sbeGen.setterList fin input)"
    using b2 b3
    by (simp add: da_def dtransition_def dtransitionH_def 
                      sbeGen.get_set dasbegenin)
  thus ?case
      by (simp add: Cons.IH b2 b4)
  qed

definition stateSem :: "'param \<Rightarrow> 'state \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>)"where
"stateSem p = daStateSem (da p)"

definition sem :: "'param \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>)" where
"sem p = daSem (da p)"

definition dSem :: "'param \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"dSem p = {sem p}"



lemma statesem_removeoutsetget:
"sbeGen.setterSB fout\<cdot>(sbeGen.getterSB fout\<cdot>(stateSem param state\<cdot>input))
        = (stateSem param state\<cdot>input)"
  apply(simp add: stateSem_def)
  apply(cases "#input = \<infinity>")
  apply(rule sbeGen.setget_eq_inf,simp_all add: dasbegenout)
  apply (metis dAutomaton.select_convs(1) da_def dastatesem_weak
 dtransition_def inf_less_eq sbe2sb_len snd_apsnd weak_well_ts_def)
proof-
  assume a1:"#input \<noteq> \<infinity>"
  then obtain k where k_def:"#input = Fin k"
    using infI by blast
  hence "daStateSem (da param) state\<cdot>input = sbTake k\<cdot>(daStateSem (da param) state\<cdot>input)"
    apply(cases "chDom TYPE('out) = {}",simp)
    apply(subst statesem_sbtakeoutput,simp_all)
    using transition_weak apply blast
    apply (subst dastatesem_weak_leneq[where n=k],simp_all)
    using transition_weak by blast
  thus "sbeGen.setterSB fout\<cdot>(sbeGen.getterSB fout\<cdot>(daStateSem (da param) state\<cdot>input)) = daStateSem (da param) state\<cdot>input"
    apply(cases "chDom TYPE('out) = {}",simp)
    apply(subst sbeGen.setget_eq_fin[where k=k],simp_all add: dasbegenout)
    apply(subst dastatesem_weak_leneq[where n=k],simp_all add: k_def)
    using transition_weak by blast
qed

lemma statesem_removeinsetget:
"stateSem param state\<cdot>(sbeGen.setterSB fin\<cdot>(sbeGen.getterSB fin\<cdot>input))
        = (stateSem param state\<cdot>input)"
  apply(simp add: stateSem_def)
  apply(cases "#input = \<infinity>")
  apply (simp add: sbeGen.setget_eq_inf dasbegenin)
proof-
  assume a1:"#input \<noteq> \<infinity>"
  then obtain k where k_def:"#input = Fin k"
    using infI by blast
  hence "daStateSem (da param) state\<cdot>input = daStateSem (da param) state\<cdot>(sbTake k\<cdot>input)"
    by (simp add: statesem_sbtakeinput)
  thus "daStateSem (da param) state\<cdot>(sbeGen.setterSB fin\<cdot>(sbeGen.getterSB fin\<cdot>input)) = daStateSem (da param) state\<cdot>input"
    apply simp
    by (simp add: k_def sbeGen.setget_eq_fin dasbegenin)
qed

lemma statesem_removesetget:
"sbeGen.setterSB fout\<cdot>(sbeGen.getterSB fout\<cdot>(stateSem param state\<cdot>(sbeGen.setterSB fin\<cdot>(sbeGen.getterSB fin\<cdot>input))))
        = (stateSem param state\<cdot>input)"
  by(simp add: statesem_removeinsetget statesem_removeoutsetget)
 (*
theorem statesem2sscanl: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "sbeGen.getterSB fout \<cdot>
  (stateSem param state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   sscanlAutOne (daTransition param) state\<cdot>input"
  by(simp add: assms daut2sscanl stateSem_def)

lemma daut2sscanl_bundle:
  assumes "chDom TYPE('in)\<noteq>{}" (*Keine Lust das zu beweisen, sollte aber unnötig sein*)
  shows"(stateSem p state\<cdot>input) = sbeGen.setterSB fout\<cdot>
  (sscanlAutOne (daTransition p) state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  apply(subst statesem_removesetget[symmetric])
  apply(cases "\<not>chDomEmpty TYPE('in)";cases "\<not>chDomEmpty TYPE('out)",simp_all)
  apply(subst statesem2sscanl,simp_all)
  using assms by blast
*)

end



locale daWeakGen =
  fixes daTransition :: "'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState :: "'param \<Rightarrow> 'state"
  and fin :: "'a \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"
  and fout :: "'b \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenfin: "sbeGen fin"
      and sbegenfout: "sbeGen fout"
begin

end

sublocale daWeakGen \<subseteq> daGen daTransition daInitialState "(\<lambda>_.\<bottom>)" fin fout
  by (simp add: daGen_def sbegenfin sbegenfout)


context daWeakGen
begin

definition daw::"'param \<Rightarrow> ('state, 'in, 'out) dAutomaton_weak" where
"daw param = \<lparr> dawTransition = dtransitionH param,
              dawInitState  = daInitialState param \<rparr>"

lemma da_def2: "da param = daw2da (daw param)"
  apply(auto simp add: da_def daw2da_def daw_def)
   apply(rule)+
  by (auto simp add: dtransition_def)

lemma statesem_def2:"stateSem p = dawStateSem (daw p)"
  by (simp add: da_def2 dawStateSem_def stateSem_def)

lemma sem_def2: "sem p = dawSem (daw p)"
  apply(simp add: sem_def dawSem_def dawStateSem_def da_def2[symmetric])
  by(simp add: daSem_def da_def daw_def)

lemma sem_def3: "sem p = stateSem p (daInitState (da p))"
  by(simp add: sem_def daSem_def da_def stateSem_def)

lemma dawstatesem_unfold[simp]:
  shows "stateSem para s\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) =
  snd (dtransition para s sbe) \<Zcat>\<^sup>\<Omega> 
  stateSem para (fst(dtransition para s sbe))\<cdot>sb"
  by(simp add: stateSem_def dtransition_def dtransitionH_def da_def)
(*
theorem dwaut2sscanl: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "sbeGen.getterSB fout \<cdot>
  (stateSem param state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   sscanlAutOne (daTransition param) state\<cdot>input"
  apply(simp add: stateSem_def)
  using assms(1) assms(2) daut2sscanl by blast

theorem dwautsem2sscanl: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "sbeGen.getterSB fout \<cdot>
  (sem param\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   sscanlAutOne (daTransition param) (daInitialState param)\<cdot>input"
  apply(simp add: sem_def daSem_def)
  using assms(1) assms(2) da_def daut2sscanl by auto
*)
lemma weirdinduction:
  assumes"\<And>state n param. adm (\<lambda>xa. P (snth n (sbeGen.getterSB fout\<cdot>(stateSem param state\<cdot>xa))))"
      and "chDom TYPE('in)\<noteq> {}"
      and "chDom TYPE('out)\<noteq> {}"
      and "Fin n < #sb"
      and "\<And>sbe s. P (shd (sbeGen.getterSB fout\<cdot>(sbe2sb (snd (dawTransition (daw param) s sbe)))))"
    shows " P (snth n (sbeGen.getterSB fout\<cdot>(stateSem param state\<cdot>sb)))"
  apply(insert spf2stream_ind[of "(\<lambda>s. \<Lambda> sb. sbeGen.getterSB fout\<cdot>(stateSem param s\<cdot>sb))" P n sb state])
  by (simp add: assms statesem_def2 sbegenfout sbeGen.gettersb_realboteps sbeGen.outns_ex)

end

locale daStrongGen =
  fixes daTransition :: "'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable \<Rightarrow> 
                      ('state\<times>'b::countable)"
  and daInitialState :: "'param \<Rightarrow> 'state"
  and daInitOut :: "'param \<Rightarrow> 'b"
  and fin :: "'a \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout :: "'b \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenfin: "sbeGen fin"
      and sbegenfout: "sbeGen fout"
begin

definition initialOutSBE::"'param \<Rightarrow> 'out\<^sup>\<surd>" where
"initialOutSBE = (sbeGen.setter fout) o daInitOut"

end
sublocale daStrongGen \<subseteq> daGen daTransition daInitialState "sbe2sb o initialOutSBE" fin fout
  by (simp add: daGen_def sbegenfin sbegenfout)

context daStrongGen begin

definition das::"'param \<Rightarrow> ('state, 'in, 'out) dAutomaton_strong" where
"das param = \<lparr> dawTransition = dtransitionH param,
              dawInitState  = daInitialState param,
              dasInitOut    = initialOutSBE param \<rparr>"


lemma da_def2: "da param = das2da (das param)"
  apply(auto simp add: da_def das2da_def das_def)
    apply(rule)+
  by (auto simp add: dtransition_def)

lemma sem_def2: "sem param = dasSem (das param)"
  by (simp add: da_def2 dasSem_def sem_def)

end


locale daGen_singleton =
  fixes daTransition :: "'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable)"
  and   daInitialState :: "'param \<Rightarrow> 'state"
  and   daInitOut :: "'param \<Rightarrow> 'out::{chan,finite}\<^sup>\<Omega>"
  and fin :: "'a \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"
  and fout :: "'b \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenin: "sbeGen fin"
      and sbegenout: "sbeGen fout"
      and singlestate:"is_singleton (UNIV::'state set)"

sublocale daGen_singleton \<subseteq> daGen
  by (simp add: daGen_def sbegenin sbegenout)

lemma single_eq:
  "is_singleton (UNIV::('a::type) set) \<Longrightarrow> x = (y::'a)"
proof(rule ccontr)
  assume single:"is_singleton (UNIV::('a::type) set)"
  assume ineq:"x \<noteq> (y::'a)"
  then have "{x,y} \<subseteq> UNIV"
    by simp 
  hence "\<not> is_singleton UNIV"
    by (metis ineq insert_subset is_singleton_def single singletonD)
  thus "False"
    using single by auto
qed


lemma fun_below_left:"x \<sqsubseteq> (\<lambda>s. y) \<Longrightarrow>  x s \<sqsubseteq> y"
  by (simp add: fun_below_iff)


context daGen_singleton
begin


lemma statesem_single_def:"stateSem p s = fix\<cdot>(\<Lambda> h. sb_step\<cdot>
        (\<lambda>sbe. \<Lambda> sb. daNextOut (da p) s sbe \<Zcat>\<^sup>\<Omega> h\<cdot>sb))"
  apply(rule fix_eqI[symmetric])
  apply(rule cfun_eqI, auto)
  apply(simp add: stateSem_def, subst stateSem_def[symmetric])
  apply(subst dastatesem_unfolding,simp add: Let_def 
        case_prod_unfold stateSem_def)
  apply(subgoal_tac "\<And>sbe. (daNextState (da p) s sbe) = s")
  apply simp 
  using single_eq singlestate 
  apply (metis (full_types))
  apply(rule_tac x="stateSem p" and y="z"in fun_below_left)
  apply(simp add: stateSem_def daStateSem_def case_prod_unfold Let_def)
  apply(rule fix_least_below)
  apply(subst beta_cfun)
  apply(intro cont2cont)
  apply(rule fun_belowI)
  apply(subgoal_tac "x = s")
  apply simp
  using single_eq singlestate
  by (metis (full_types))

lemma sem_single_def:"sem p = (\<Lambda> i. (daInitOut p) \<Zcat>\<^sup>\<Omega> stateSem p s\<cdot>i)"
  apply(simp add: sem_def daSem_def stateSem_def[symmetric])
  apply(simp add: da_def)
  apply(subst single_eq[of "daInitialState p" s])
  by(simp_all add: singlestate)
(*
lemma daut2smap: 
  assumes "\<not>chDomEmpty TYPE('out)"
  and "\<not>chDomEmpty TYPE('in)"
  shows "sbeGen.getterSB fout \<cdot>
  (stateSem param state\<cdot>(sbeGen.setterSB fin\<cdot>input)) =  
   smap (\<lambda>i. snd (daTransition param s i))\<cdot>input"
  apply(simp add: stateSem_def)
  apply(subst daGen.daut2sscanl)
  apply (simp_all add: assms daGen_axioms)
  apply(subgoal_tac "state = s",simp)
  apply(subst sscanlautone2smap)
  by (metis (mono_tags) single_eq singlestate)+
*)
end
  


end

