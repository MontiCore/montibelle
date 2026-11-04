theory EventExecLocale

imports BundleMergeExec eventcomponent.EventAutomatonExec bundle.SBCodegen 

begin

default_sort type

typedef ('s::type,'cs::"{chan}") outlist ="{ls::('s\<times>('cs \<Rightarrow> M stream)) list | ls. list_all (lsb_well o snd) ls}"
  apply auto[1]
  by(rule_tac x="[]" in exI,simp)

setup_lifting type_definition_outlist


lemma pred_prod_def:"pred_prod P1 P2 = (\<lambda>(a,b). P1 a \<and> P2 b)"
  by auto

lift_definition outlist2sb::"('s,('cs::{chan})) outlist \<Rightarrow> ('s\<times>'cs\<^sup>\<Omega>)list"is
"Rep_outlist"
proof(simp add: pred_prod_def)
  fix outlist::"('s, 'cs) outlist"
  show "list_all (\<lambda>(a::'s, b::'cs \<Rightarrow> M stream). lsb_well b) (Rep_outlist outlist)"
    using Rep_outlist[of outlist] 
    by (simp add: o_def split_beta')
qed

default_sort chan

lemma list_allIh:"(\<And>x. P (f x)) \<Longrightarrow> list_all (\<lambda>x. P (snd x))
        (map (apsnd f) list)"
  by(induction list,simp_all)

lemma list_all_imp:
  assumes"\<And>x. P x \<Longrightarrow> Q x"
  shows "list_all P ls \<Longrightarrow> list_all Q ls"
  using assms list.pred_mono_strong by blast

lemma list_all_or:"list_all P ls \<Longrightarrow> list_all (\<lambda>ls. P ls \<or> Q ls) ls"
  by(induction ls,simp_all)

lemma list_all_and:"list_all (\<lambda>x. list_all P (snd x)) = list_all (list_all P) o (map snd)"
  apply(rule fun_eqI)
  by(induct_tac x,simp_all)

lift_definition listoutconv::"('state::type\<times>('out::{echan,finite} msgWithChan) event list) list \<Rightarrow> ('state,'out) outlist"is
"map (apsnd ((Rep_lsb o Rep_cfun uSplit) o list2s))"
  apply (auto simp add: o_def)[1]
  by(rule list_allIh,simp)

lemma [ccodeAbs]:"Rep_lsb (uSplit\<cdot>(s::'cs msgWithChan event stream)) = (if chDom TYPE ('cs::{echan,finite}) = {} then (\<lambda>c. sbot) else (\<lambda>c. smap (Timed o TLive)\<cdot>(emap snd\<cdot>(efilter (\<lambda>(x,e). x=c)\<cdot>(emap Rep_msgWithChan\<cdot>s)))))"
  apply(simp)
  apply(rule conjI)
  apply(simp add: uSplit.rep_eq)
  apply (metis Rep_lsb_strict app_strict)
  apply(rule impI)
  by(simp add: demerge_rep_eq)

lemma [code]:"Rep_cfun uSplit = uSplit_nc"
  by(simp add: uSplit_nc_def)


lemma listoutconv_apfst: "map (apfst f) (outlist2sb (listoutconv A)) = outlist2sb (listoutconv (map (apfst f) A))"
  by(auto simp add: outlist2sb_def listoutconv.rep_eq)
  
fun listeventWrapper::"('a::type event \<Rightarrow> ('state\<times>'b list) list) \<Rightarrow>('a event  
                        \<Rightarrow> ('state::type\<times> 'b::type event list) list)" where
"listeventWrapper f Tick = map (apsnd (\<lambda>ls. Tick#(map EventMsg ls))) (f Tick)" |
"listeventWrapper f e = map (apsnd (\<lambda>ls. map EventMsg ls)) (f e)"

locale eventExecGen =
  fixes ndaTransition_event::"'param::type \<Rightarrow> 'state::random \<Rightarrow> ('in::{echan,enum} \<times> msg)  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) list"
    and ndaTransition_tick::"'param::type \<Rightarrow> 'state  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) list"
      and ndaInitConfig:: "'param \<Rightarrow> ('state \<times> ('out msgWithChan) list) list"
      and delay::"bool"
begin


definition ndaInitConfigC::"'param \<Rightarrow> ('state \<times> ('out msgWithChan) list) list" where
"ndaInitConfigC p = (if ndaInitConfig p= [] then [(rnd (2,3),[])] else ndaInitConfig p)"

definition ndaTransition_eventC::"'param \<Rightarrow> 'state \<Rightarrow> ('in::{echan,enum} \<times> msg)  
                        \<Rightarrow> ('state\<times>('out::{echan,finite} msgWithChan) list) list" where
"ndaTransition_eventC p s i = ( if ndaTransition_event p s i = [] then [(s,[])] 
                                        else ndaTransition_event p s i)"

definition ndaTransition_tickC::"'param \<Rightarrow> 'state  
                        \<Rightarrow> ('state\<times>('out::{echan,finite}msgWithChan) list) list" where
"ndaTransition_tickC p s = (if ndaTransition_tick p s = [] then [(s, [])] 
                                        else ndaTransition_tick p s)"

fun ndaTransition::"'param \<Rightarrow> 'state \<Rightarrow> (('in::{echan,enum} \<times> msg) event)
                        \<Rightarrow> (('state\<times>('out::{echan,finite}msgWithChan) list) list)" where
"ndaTransition p s (EventMsg m) = ndaTransition_eventC p s m" | 
"ndaTransition p s Tick      = ndaTransition_tickC p s" 
declare ndaTransition.simps[code]

definition transition::"'param \<Rightarrow> 'state \<Rightarrow> ('in\<times>msg) event  
                        \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) list" where
"transition p s = outlist2sb o (listoutconv) o (listeventWrapper (ndaTransition p s))"
                                                                      
lemma transitioncode[code]:"transition p s = (map (apsnd ((Rep_cfun uSplit) o list2s))) o (listeventWrapper (ndaTransition p s))"
  by(simp add: transition_def o_def listoutconv.rep_eq outlist2sb.abs_eq map_prod_def case_prod_beta apsnd_def split_beta')
  
lemma transition_def2_h[simp]:"t \<in> eValues\<cdot>(<(map EventMsg ls)>) \<Longrightarrow> t\<in> set ls"
  by(induction ls;auto)

lemma trans_states: "map fst (transition p s input) = map fst (ndaTransition p s (input))"
  apply(cases input)
  by(simp add: transition_def outlist2sb_def listoutconv.rep_eq)+

definition config::"'param \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) list" where
"config p = outlist2sb (if delay then listoutconv (map (apsnd (\<lambda>ls. map EventMsg ls@[Tick])) (ndaInitConfigC p)) else 
                            listoutconv (map (apsnd (map EventMsg)) (ndaInitConfigC p)))"

lemma configcode[code]:"config p = (if delay then map (apsnd (( Rep_cfun uSplit) o list2s)) (map (apsnd (\<lambda>ls. map EventMsg ls@[Tick])) (ndaInitConfigC p))
else map (apsnd (( Rep_cfun uSplit) o list2s)) (map (apsnd (map EventMsg)) (ndaInitConfigC p)))"
 by(simp add: config_def o_def listoutconv.rep_eq outlist2sb.abs_eq map_prod_def case_prod_beta apsnd_def split_beta')
  

definition lsaut::"'param \<Rightarrow> ('state, ('in\<times>msg) event, 'out\<^sup>\<Omega>) listAutomaton" where
"lsaut p =  (| listTransition = transition p, listInitConfig = config p |)"

fun rndSem::"'param\<times>seed\<times>seed \<Rightarrow> ('in\<^sup>\<Omega> \<Rightarrow> 'out\<^sup>\<Omega>)"where
"rndSem (p,seed1,seed2) sb = execSem (execToDa (listToExec (lsaut (p))) seed1)\<cdot>(Rep_eventwellstream (execBMerge seed2 sb))"


lemma execseminndasem:
  assumes "\<And>s. set (ndaTransition_tickC (p) s) \<subseteq> eventGenndaTransition_tickC p s"
  and "\<And>s i. set (ndaTransition_eventC (p) s i) \<subseteq> eventGenndaTransition_eventC p s i"
  and "set (ndaInitConfigC p) \<subseteq> eventGenndaInitConfig p"
  shows "rndSem (p,seed) \<in> Rep_cfun ` (eventGenSem p)"
  oops

end

end