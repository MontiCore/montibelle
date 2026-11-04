theory Executable

imports DeterministicAutomaton

begin




text\<open>An executable automaton might have multiple, even infinitely 
many, different configuration and transition options. To still allow
randomized execution, this is represented as a function in the 
following record. Again, beside a small signature change it is close
to the @{type iAutomaton} record.\<close>
record ('state::type,'message::type,'out::conc)
  execAutomaton =
    exautTransition :: "'state \<Rightarrow> 'message \<Rightarrow> (natural \<Rightarrow> ('state\<times>'out))"
    exautInitConfig :: "natural \<Rightarrow> ('state \<times> 'out)"

type_synonym seed = "natural \<times> natural"


fun rndTransition::"('state, 'msg, 'out::conc) execAutomaton \<Rightarrow> 
        'state\<times>seed \<Rightarrow> 'msg \<Rightarrow> (('state\<times> seed) \<times> 'out)"where
"rndTransition eaut (state,seed) msg = 
(let (nat,nextSeed) = Random.next seed
  in apfst (\<lambda>s. (s,nextSeed)) (exautTransition eaut state msg nat))"


fun rndInitConfig::"('state, 'msg, 'out::conc) execAutomaton \<Rightarrow>
         seed \<Rightarrow> (('state\<times>seed) \<times> 'out)"where
"rndInitConfig eaut seed = 
(let (nat,nextSeed) = Random.next seed 
  in apfst (\<lambda>s. (s,nextSeed)) (exautInitConfig eaut nat))"


definition execToDa:: "('state, 'msg, 'out::conc) execAutomaton \<Rightarrow> 
        seed \<Rightarrow>  ('state\<times>seed, 'msg, 'out)  dAutomaton" where
"execToDa aut seed = (| dautTransition = rndTransition aut, 
                        dautInitConfig = rndInitConfig aut seed |)"

lift_definition execToAut:: "('s, 'm, 'out::conc) execAutomaton \<Rightarrow> 
         ('s, 'm, 'out)  automaton" is
"\<lambda>eaut. (\<lambda>state msg. range (exautTransition eaut state msg), 
                     range (exautInitConfig eaut))"
by auto

theorem execdainexecnda[simp]:"daSem step (execToDa aut seed) \<in> sem step (execToAut aut)"
  apply(rule daseminsem_rule[where g="fst"])
  apply(simp add: execToDa_def case_prod_beta' Let_def autInitConfig.rep_eq execToAut.rep_eq)
  apply(simp add: Let_def)
  apply(rule dasseminssem_rule)
  apply(case_tac s)
  by(simp add: Let_def case_prod_beta' execToDa_def autTransition.rep_eq execToAut.rep_eq)


lemma auttrans_range[simp]:"autTransition\<cdot>(execToAut aut') = (\<lambda>s i. range ((exautTransition aut') s i))"
  by(simp add: autTransition.rep_eq execToAut.rep_eq)
theorem execstatesem_refine_rule:
    assumes "\<And>state msg nextState out. Inv state 
                \<Longrightarrow> (  nextState, out) \<in> range ((exautTransition aut') state msg)
                \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
        and invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` range ((exautTransition aut') state msg)
                   \<Longrightarrow> Inv nextState"
        and "Inv s"
      shows "(stateSem step (execToAut aut') s \<subseteq> stateSem step aut (f s))"
  by(rule statesem_refine_rule[where Inv=Inv];simp add: assms)

lemma autinit_range[simp]:"autInitConfig\<cdot>(execToAut aut') = range (exautInitConfig aut')"
  by(simp add: autInitConfig.rep_eq execToAut.rep_eq)


theorem execsem_refine_rule:
   assumes "\<And>initState initOut. (initState, initOut) \<in> range (exautInitConfig aut') \<Longrightarrow>
                                (f initState, initOut) \<in> autInitConfig\<cdot>aut"
      and "\<And>s. s \<in> fst` range (exautInitConfig aut') \<Longrightarrow> (stateSem step (execToAut aut') s \<subseteq> stateSem step aut (f s))"
    shows "(sem step (execToAut aut') \<subseteq> sem step aut)"
   apply(auto simp add: sem_def)[1]
   apply(rule_tac x="initOut" in exI)
   apply(rule_tac x="f initState" in exI)
   apply(rule_tac x="spf" in exI)
   using assms(1) assms(2) apply auto[1]
   by (metis (no_types, lifting) fst_eqD imageI in_mono rangeI)

 text\<open>Defining an executable automaton might be to cumbersome, we 
further introduce a list automaton record. This does not allow 
infinitely many transition or configuration options but is easy to
use for specifying components. Its signatures are different
to the @{type iAutomaton} signatures by only exchanging sets through 
lists.\<close>
record ('state::type,'message::type,'out::conc)
  listAutomaton =
    listTransition :: "'state \<Rightarrow> 'message \<Rightarrow> ('state\<times>'out) list"
    listInitConfig :: "('state \<times> 'out) list"

definition listfun::"'a list \<Rightarrow>natural\<Rightarrow> 'a" where
"listfun list n = nth list 
           (nat_of_natural (n mod (natural_of_nat (length list))))"


lemma listfuninset:"ls \<noteq> [] \<Longrightarrow> listfun ls n \<in> set ls"
  by(simp add: listfun_def)

lemma listfunmaptof:"ls \<noteq> [] \<Longrightarrow> 
               listfun (map f ls) n = f (listfun ls n)"
  by(simp add: listfun_def)
text\<open>Applying @{const listfun} to the transitions output and 
configuration of a list automaton defines the executable automaton.\<close>
definition listToExec:: "('s, 'm, 'out::conc) listAutomaton \<Rightarrow> 
                         ('s, 'm, 'out)  execAutomaton" where
"listToExec laut = (| exautTransition = 
           (\<lambda>state msg. listfun (listTransition laut state msg)), 
                      exautInitConfig = 
            listfun (listInitConfig laut) |)"

end