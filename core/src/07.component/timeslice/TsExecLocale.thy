theory TsExecLocale

imports TsAutomatonExec TsAutomaton bundlelocale.SBEGen automaton.Executable
begin

locale tsExecGen =
  fixes ndaTransition::"'param::type \<Rightarrow> 'state::random \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitConfig:: "'param \<Rightarrow> ('state \<times> 'out::{tschan,finite}\<^sup>\<Omega>) list"
      and fin:: "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::"'b \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenin: "sbeGen fin"
      and sbegenout:"sbeGen fout"
      and completeinit:"\<And>p. ndaInitConfig p \<noteq> []"
begin

definition ndaTransitionC::"'param \<Rightarrow> 'state \<Rightarrow> 'a
                        \<Rightarrow> ('state\<times>'b) list" where
"ndaTransitionC p s a = (if ndaTransition p s a = [] then [rnd (2,3)] else 
                            ndaTransition p s a)"

definition transition::"'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd>
                        \<Rightarrow> ('state\<times>'out\<^sup>\<Omega>) list" where
"transition p s = (map (apsnd (sbe2sb o (sbeGen.setter fout)))) o (ndaTransitionC p s) o (sbeGen.getter fin)"


definition lsaut::"'param \<Rightarrow> ('state, 'in\<^sup>\<surd>, 'out\<^sup>\<Omega>) listAutomaton" where
"lsaut p =  (| listTransition = transition p, listInitConfig = ndaInitConfig p |)"

fun rndSem::"'param\<times>seed \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>)"where
"rndSem (p,seed) = tsExecSem (execToDa (listToExec (lsaut (p))) seed)"


lemma execseminndasem:
  assumes "\<And>s i. set (ndaTransitionC p s i) \<subseteq> tsGenndaTransition_tickC p s i"
  and "set (ndaInitConfig p) \<subseteq> tsGenndaInitConfig p"
  shows "rndSem (p,seed) \<in>  (tsGenSem p)"
  oops


end


locale tsExecWeakGen =
  fixes ndaTransition::   "'param::type \<Rightarrow> 'state::random \<Rightarrow> 'a::countable 
                            \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitConfig:: "'param \<Rightarrow> 'state list"
      and fin::           "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::          "'b \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes sbegenfin:      "sbeGen fin"
      and sbegenfout:     "sbeGen fout"
begin


definition ndaInitConfigC::"'param \<Rightarrow> 'state list"where
"ndaInitConfigC p = (if ndaInitConfig p = [] then [rnd(2,3)] else ndaInitConfig p)"

definition initConfig::"'param \<Rightarrow> ('state\<times> 'out\<^sup>\<Omega>) list"where
"initConfig p = map (\<lambda>s. (s,bot_nc)) (ndaInitConfigC p)"

end

sublocale tsExecWeakGen \<subseteq> tsExecGen ndaTransition initConfig fin fout
  by(simp add: tsExecGen_def sbegenfin sbegenfout initConfig_def ndaInitConfigC_def)

context tsExecWeakGen
begin

lemma [code]:"rndSem (p,s) = (let da = (execToDa (listToExec (lsaut (p))) s) in 
                              tsExecStateSem da (fst (dautInitConfig da)))"
  apply(rule cfun_eqI)
  apply(simp add: tsExecSem_def tsExecStateSem_def daSem_def case_prod_unfold Let_def)
  apply(subst lsaut_def)
  apply(subst execToDa_def)
  apply(simp add: case_prod_unfold Let_def)
  apply(subst listToExec_def,simp)
  apply(subst initConfig_def)
  apply(subst listfunmaptof,simp add: ndaInitConfigC_def)
  apply(simp add: bot_nc_sb_def bot_nc_stream_def stream_bottom_nc_def bot_sb[symmetric])
  by (metis botconc1 least_sb_bottom_eq)

end

locale tsExecStrongGen =
  fixes ndaTransition::   "'param::type \<Rightarrow> 'state::random \<Rightarrow> 'a::countable 
                            \<Rightarrow> ('state\<times>'b::{countable,random}) list"
      and ndaInitConfig:: "'param \<Rightarrow> ('state\<times>'b) list"
      and fin::           "'a::countable \<Rightarrow> 'in::{tschan,finite} \<Rightarrow> M"  
      and fout::          "'b \<Rightarrow> 'out::{tschan,finite} \<Rightarrow> M"
  assumes sbegenfin:      "sbeGen fin"
      and sbegenfout:     "sbeGen fout"
begin


definition ndaInitConfigC::"'param \<Rightarrow> ('state\<times>'b) list"where
"ndaInitConfigC p = (if ndaInitConfig p = [] then [rnd(2,3)] else ndaInitConfig p)"

definition initConfig::"'param \<Rightarrow> ('state\<times> 'out\<^sup>\<Omega>) list"where
"initConfig p = map (apsnd (sbe2sb o (sbeGen.setter fout))) (ndaInitConfigC p)"

end

sublocale tsExecStrongGen \<subseteq> tsExecGen ndaTransition initConfig fin fout
  by(simp add: tsExecGen_def sbegenfin sbegenfout initConfig_def ndaInitConfigC_def)

context tsExecStrongGen
begin

end


end
