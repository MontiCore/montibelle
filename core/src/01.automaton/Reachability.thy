theory Reachability

imports Automaton
begin
default_sort type

definition reachable::"'state set \<Rightarrow> ('state \<Rightarrow> ('state set)) \<Rightarrow> 'state set" where
"reachable Init transition = lfp (\<lambda> S. Init \<union> (\<Union>s\<in>S. transition s))"

lemma reachable_unfold:
  "reachable Init transition = Init \<union> (\<Union>s\<in>(reachable Init transition). transition s)"
  unfolding reachable_def
  apply(rule lfp_fixpoint[symmetric])
  unfolding mono_def
  by blast

lemma reachable_switch_init: assumes "Init \<subseteq> X" and "X \<subseteq> reachable Init t"
  shows "reachable Init t = reachable X t"
  apply(rule order_antisym)
   apply(subst reachable_def, rule lfp_lowerbound, subst (2)reachable_unfold)
  using assms(1) apply auto[1]
  apply(subst reachable_def, rule lfp_lowerbound)
  apply (auto simp add: assms)[1]
  apply(subst reachable_unfold)
  by auto

lemma reachable_end: assumes "(\<Union> (transition ` Init)) \<subseteq> Init"
  shows "reachable Init transition = Init"
  apply(rule order_antisym)
   apply(subst reachable_def, rule lfp_lowerbound)
  using assms apply auto[1]
  apply(subst reachable_unfold)
  by auto

lemma reachable_exec [code]: "reachable Init transition = (let nextStates = \<Union>(transition ` Init)\<union>Init in 
    if nextStates = Init then Init else reachable nextStates transition) "
  apply(simp add: Let_def)
  apply(rule conjI; rule impI)
   apply(rule reachable_end, blast)
  apply(rule reachable_switch_init; simp)
  by (metis UN_Un Un_subset_iff sup.cobounded1 sup.cobounded2 reachable_unfold)

lemma reachable_step_in: "state \<in> reachable Init t \<Longrightarrow> t state \<subseteq> reachable Init t"
  apply(subst reachable_unfold, simp)
  by blast




datatype testState = someA | someB | someC | notReachable
fun testTransition where
"testTransition someA = {someA}" |
"testTransition someB = {someA}" |
"testTransition someC = {someA, someC}" |
"testTransition notReachable = {notReachable,someC}" 

value "testTransition` testTransition someC"

value "reachable {} testTransition"
value "reachable {someA} testTransition"
value "reachable {someC} testTransition"
value "reachable {someB,someC, someA} testTransition"




definition reachableStates::"('s,'msg,'out::conc) automaton \<Rightarrow> 's set" where
"reachableStates aut = reachable (fst ` autInitConfig\<cdot>aut) 
                          (\<lambda>s. fst ` (\<Union>(range ((autTransition\<cdot>aut) s))))"

definition "reachablePred aut s  = (s\<in>reachableStates aut)"

lemma reachablePred_inv: "(reachablePred aut) state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut) state msg
                   \<Longrightarrow> reachablePred aut nextState"
  unfolding reachablePred_def reachableStates_def
  apply auto[1]
  using reachable_step_in by fastforce

lemma reach_statinv_substet: assumes "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut) state msg
                   \<Longrightarrow> Inv nextState"
        and "\<And>initState. initState \<in> fst ` (autInitConfig\<cdot>aut) 
                   \<Longrightarrow> Inv initState"
  shows "reachableStates aut \<subseteq> {s. Inv s}"
  unfolding reachableStates_def reachable_def
  apply(rule lfp_lowerbound)
  apply auto
  using assms(2) apply fastforce
  by (metis assms(1) fst_conv imageI)


definition isStateInv::"('state, 'message, 'out::conc) automaton 
                              \<Rightarrow> ('state \<Rightarrow> bool) \<Rightarrow> bool" where
"isStateInv nda Inv \<equiv> (\<forall>state msg nextState. Inv state
                \<longrightarrow> nextState \<in> fst ` (autTransition\<cdot>nda) state msg
                \<longrightarrow> Inv nextState )
        \<and> (\<forall>state. state \<in> fst ` (autInitConfig\<cdot>nda) \<longrightarrow> Inv state)"

lemma "isStateInv nda (\<lambda>s. s \<in> reachableStates nda)"
  unfolding isStateInv_def
  apply auto
  using reachablePred_inv apply (metis fst_eqD imageI reachablePred_def)
  apply(subst reachableStates_def, subst reachable_unfold)
  apply auto
  by (metis fst_conv image_eqI)
  
lemma assumes "isStateInv aut Inv"
        shows  "reachableStates aut \<subseteq> {s. Inv s}"
  using reach_statinv_substet isStateInv_def by (metis assms)

lemma invariant_sem_refine: 
    assumes "\<And>state msg nextState out. Inv state 
        \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
        \<Longrightarrow> (f nextState, out) \<in> (autTransition\<cdot>aut) (f state) msg"
      and "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut'
        \<Longrightarrow> (f initState, initOut) \<in> autInitConfig\<cdot>aut"
      and "isStateInv aut' Inv"
    shows "sem step aut' \<subseteq> sem step aut"
  apply(rule invariant_sem_refine[where f=f and Inv=Inv])
     apply(auto simp add: assms isStateInv_def)
   apply (metis assms(3) fst_conv image_eqI isStateInv_def)
  by (metis assms(3) fst_conv image_eqI isStateInv_def)



fun lreach::"'msg::type list \<Rightarrow> 'state::type \<Rightarrow> ('state \<Rightarrow> 'msg \<Rightarrow> 'state) \<Rightarrow> 'state" where
"lreach [] init transition = init" |
"lreach (x#xs) init transition = lreach xs (transition init x) transition"

definition daReach::"'msg::type list \<Rightarrow> 'state::type \<Rightarrow> ('state \<Rightarrow> 'msg \<Rightarrow> ('state \<times> 'out::type)) \<Rightarrow> 'state" where
"daReach input s t = lreach input s (\<lambda> s msg. fst (t s msg))"

lemma daReach_dautTransition_eq: "fst ((dautTransition aut) s input) = daReach [input] s (dautTransition aut)"
  by (metis daReach_def lreach.simps(1) lreach.simps(2))

lemma daReach_step:
  assumes "ns = daReach ([a]) s (dautTransition da)"
  shows "daReach ls ns (dautTransition da) = daReach (a#ls) s (dautTransition da)"
  apply(simp add: daReach_def)
  by (simp add: assms daReach_dautTransition_eq)


fun nda_lreach::"'msg::type list \<Rightarrow> 'state::type set \<Rightarrow> ('state \<Rightarrow> 'msg \<Rightarrow> 'state set) \<Rightarrow> 'state set" where
"nda_lreach [] init transition = init" |
"nda_lreach (x#xs) init transition = nda_lreach xs (\<Union>s\<in>init. transition s x) transition"

definition ndaReach::"'msg::type list \<Rightarrow> 'state::type set \<Rightarrow> ('state \<Rightarrow> 'msg \<Rightarrow> ('state \<times> 'out::type)set) \<Rightarrow> 'state set" where
"ndaReach input s t = nda_lreach input s (\<lambda> s msg. fst `(t s msg))"

lemma ndaReach_autTransition_eq: "fst ` (\<Union>s\<in>S. (autTransition\<cdot>aut) s input) = ndaReach [input] S (autTransition\<cdot>aut)"
  apply(simp add: ndaReach_def)
  by blast

lemma ndaReach_step:
  assumes "ns = ndaReach ([a]) s (autTransition\<cdot>nda)"
  shows "ndaReach ls ns (autTransition\<cdot>nda) = ndaReach (a#ls) s (autTransition\<cdot>nda)"
  apply(simp add: ndaReach_def)
  apply (simp add: assms )
  apply(subst ndaReach_autTransition_eq[symmetric],simp add: image_UN)
  done

end
