theory EventAutomatonExec 

imports stream.StreamAutomaton stream.StreamCodegen EventAutomaton

begin
default_sort type

definition execStateSem::"('state::type, 'msg::countable, 'out::{pcpo,conc}) dAutomaton
  \<Rightarrow> 'state \<Rightarrow> ('msg stream \<rightarrow> 'out)" where
"execStateSem = daStateSem stream_step"
definition execSem::"('state::type, 'msg::countable, 'out::{pcpo,conc}) dAutomaton 
  \<Rightarrow> ('msg stream \<rightarrow> 'out)" where
"execSem = daSem stream_step"

lemma %visible[ccode,simp]:"execStateSem aut s\<cdot>\<epsilon> = bot_nc"
  by(simp add: execStateSem_def botnc_eq_bot)


lemma %visible [ccode]:"execStateSem aut s\<cdot>(updis a&& rt) = 
      snd (dautTransition aut s a) \<Zcat>\<Zcat> 
      execStateSem aut (fst (dautTransition aut s a))\<cdot>rt"
  apply(simp add: execStateSem_def lscons_conv)
  by(subst dastatesem_step,simp add: case_prod_beta' Let_def)

export_code %invisible execStateSem_nc in SML module_name naas

lemma %visible [ccode,simp]:"execSem aut\<cdot>s = snd (dautInitConfig aut) 
                   \<Zcat>\<Zcat> execStateSem aut (fst (dautInitConfig aut))\<cdot>s"
  apply(simp add: execSem_def)
  apply(subst dasem_unfold)
  by(simp add: execStateSem_def[symmetric])

lemma [code_abbrev]:"execSem = daSem stream_step"
  by (simp add: execSem_def)

end
