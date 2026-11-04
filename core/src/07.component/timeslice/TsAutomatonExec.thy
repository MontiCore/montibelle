theory TsAutomatonExec 

imports stream.StreamAutomaton stream.StreamCodegen TsAutomaton bundle.SBCodegen

begin
default_sort type



definition tsExecStateSem::"('state::type, 'cs::{chan,finite}\<^sup>\<surd>, 'out::{pcpo,conc,bot_nc}) dAutomaton
  \<Rightarrow> 'state \<Rightarrow> ('cs\<^sup>\<Omega> \<rightarrow> 'out)" where
"tsExecStateSem = daStateSem sb_step"

definition tsExecStateSem_nc::"('state::type, 'cs::{chan,finite}\<^sup>\<surd>, 'out::{pcpo,conc,bot_nc}) dAutomaton
  \<Rightarrow> 'state \<Rightarrow> ('cs\<^sup>\<Omega> \<Rightarrow> 'out)" where
"tsExecStateSem_nc aut s = Rep_cfun (tsExecStateSem aut s)"

text\<open>Again, the splitting operator @{const sb_step} is enough to 
implement the deterministic time slice automatons semantics.\<close>
definition tsExecSem::"('state::type, 'cs::{chan,finite}\<^sup>\<surd>, 'out::{pcpo,conc,bot_nc}) dAutomaton 
  \<Rightarrow> ('cs\<^sup>\<Omega> \<rightarrow> 'out)" where
"tsExecSem = daSem sb_step"


lemma %visible tsexecssemstep[code]:
" (tsExecStateSem_nc aut s)  = (\<lambda>sb. 
        (if sbIsLeast (sb::'cs::{chan,finite}\<^sup>\<Omega>) \<and> chDom TYPE('cs) \<noteq> {} then bot_nc 
                     else (snd(dautTransition aut s (sbHdElem sb))) 
 \<Zcat>\<Zcat> (tsExecStateSem_nc aut (fst(dautTransition aut s (sbHdElem sb))) (sbRt\<cdot>sb))))"
  apply(simp add: tsExecStateSem_nc_def)
  apply(cases "chDom TYPE('cs) = {}",simp_all)
  apply(simp_all add: tsExecStateSem_def)
  apply(subst dastatesem_step)
  apply(rule fun_eqI)
  apply(subst sb_steps_sbe_empty2)
  apply(simp_all add: case_prod_unfold Let_def )
  apply (metis (full_types)sb_empty_eq tsExecStateSem_def tsExecStateSem_nc_def)
  apply(subst dastatesem_step)
  apply(rule fun_eqI)
  apply(case_tac x;simp)
  using botnc_eq_bot sbnleast_len apply blast
  by (simp add: case_prod_beta sbhdelem_sbecons tsExecStateSem_def tsExecStateSem_nc_def)

lemma [code]:"Rep_cfun (tsExecStateSem aut s) = tsExecStateSem_nc aut s"
  by (simp add: tsExecStateSem_nc_def)


lemma %visible [code]:"Rep_cfun (tsExecSem aut) =
     (\<lambda> sb. snd (dautInitConfig aut) \<Zcat>\<Zcat> 
       tsExecStateSem_nc aut (fst (dautInitConfig aut)) sb)"
  by(simp add: tsExecSem_def tsExecStateSem_def tsExecStateSem_nc_def 
               daSem_def case_prod_unfold Let_def)

lemma tsexecsem_insert[simp]:"Rep_cfun (tsExecSem aut) =
     (\<lambda> sb. snd (dautInitConfig aut) \<Zcat>\<Zcat> 
       tsExecStateSem aut (fst (dautInitConfig aut))\<cdot>sb)"
  by(simp add: tsExecSem_def tsExecStateSem_def tsExecStateSem_nc_def 
               daSem_def case_prod_unfold Let_def)

end