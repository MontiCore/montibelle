theory TSEventAutomaton


imports stream.EventStream automaton.Automaton
  bundle.MsgWithChan
  TsAutomaton

begin
default_sort type




definition merge::"('cs \<Rightarrow> 'm list) \<Rightarrow> ('cs\<times>'m) list set" where
"merge = gfp (\<lambda> F sbe. if (\<forall>c. sbe c = []) then {[]} 
  else {((c, hd (sbe c))#rest) | c rest. sbe c \<noteq> [] 
    \<and> rest \<in> F (\<lambda>c'. if c=c' then tl (sbe c') else sbe c')})"

lemma merge_mono: "mono (\<lambda> F sbe. if (\<forall>c. sbe c = []) then {[]} 
  else {((c, hd (sbe c))#rest) | c rest. sbe c \<noteq> [] 
    \<and> rest \<in> F (\<lambda>c'. if c=c' then tl (sbe c') else sbe c')})"
  apply(intro monoI le_funI)
  apply auto[1]
  by (simp add: le_fun_def subset_iff)

lemma merge_unfold: "merge sbe = (if (\<forall>c. sbe c = []) then {[]} 
  else {((c, hd (sbe c))#rest) | c rest. sbe c \<noteq> [] 
    \<and> rest \<in> merge (\<lambda>c'. if c=c' then tl (sbe c') else sbe c')})"
  apply(subst merge_def)+
  by(subst gfp_fixpoint[OF merge_mono, symmetric], simp)

lemma merge_end: assumes "\<And>c. sbe c = []"
  shows "merge sbe = {[]}"
  by(simp add: merge_unfold assms)

lemma merge_step: assumes "\<exists>c. sbe c \<noteq> []"
  shows "merge sbe = {((c, hd (sbe c))#rest) | c rest. sbe c \<noteq> [] 
    \<and> rest \<in> merge (\<lambda>c'. if c=c' then tl (sbe c') else sbe c')}"
  by(simp add: merge_unfold assms)



definition tsbelem2events::"'in::chan sbElem \<Rightarrow> ('in msgWithChan event list) set" where
"tsbelem2events sbe = (\<lambda>ls. map (\<lambda>m. EventMsg (Abs_msgWithChan m)) ls @ [Tick]) 
                              ` merge (\<lambda>c. sbelist c sbe)" 


fun multTransitionsInOne::
  "('state \<Rightarrow> 'msg \<Rightarrow> ('state\<times>'out::{pcpo,conc}) set )
    \<Rightarrow> 'state \<Rightarrow> 'msg list \<Rightarrow> ('state \<times> 'out) set" where
"multTransitionsInOne _ s [] = {(s,\<bottom>)}"  |
"multTransitionsInOne ndaTrans s (x#xs) = 
  {(sFinal, outNext \<Zcat>\<Zcat> outFinal) | sNext sFinal outNext outFinal. 
        (sNext, outNext) \<in> ndaTrans s x
      \<and> (sFinal, outFinal) \<in> multTransitionsInOne ndaTrans sNext xs}"


definition event2tsTrans::"
  ('state \<Rightarrow> 'in::tschan msgWithChan event \<Rightarrow> ('state \<times> 'out::conc) set)
 \<Rightarrow> ('state \<Rightarrow> 'in sbElem \<Rightarrow> ('state \<times> 'out) set)" where
"event2tsTrans f s msg = \<Union>(multTransitionsInOne f s`(tsbelem2events msg))"




definition event2tsAut::
"('state, 'in::{tschan,finite} msgWithChan event, 'out::conc) automaton 
                      \<Rightarrow> ('state, 'in sbElem, 'out::conc) automaton" where
"event2tsAut \<equiv> \<lambda>aut. Abs_automaton (event2tsTrans (autTransition\<cdot>aut), 
                                    autInitConfig\<cdot>aut)"
  

definition tseventSem::"('state, 'in::{tschan,finite} msgWithChan event, 'out::conc) automaton \<Rightarrow> 
                            ('in\<^sup>\<Omega> \<rightarrow> 'out) set" where
"tseventSem aut = ndaSem (event2tsAut aut)"




definition event2listAut::
"('state, 'in, 'out::conc) automaton 
 \<Rightarrow> ('state, 'in list, 'out::conc) automaton " where
"event2listAut aut = Abs_automaton (multTransitionsInOne (autTransition\<cdot>aut), autInitConfig\<cdot>aut)"


end