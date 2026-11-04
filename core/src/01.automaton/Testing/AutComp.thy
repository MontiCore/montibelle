theory AutComp
imports automaton.DeterministicAutomaton 

begin

definition aut_comp_test::"('super \<Rightarrow> 'wmsg) \<Rightarrow> ('super \<Rightarrow> 'wout) \<Rightarrow> 
                     ('super \<Rightarrow> 'smsg) \<Rightarrow> ('super \<Rightarrow> 'sout) \<Rightarrow>
       ('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton
    \<Rightarrow> (('wstate\<times>'sstate),'input,'super::conc) automaton" where
"aut_comp_test towmsg towout tosmsg tosout aut1 aut2 = Abs_automaton (
  (\<lambda>(ws,ss) msg. {(state,undefined z)| state z. undefined})
  , undefined)"





definition pairwise_union::"'a set \<Rightarrow> 'b set \<Rightarrow> ('a\<times>'b) set" where
"pairwise_union A B = {(a,b) | a b. a\<in>A \<and> b\<in>B}"

lemma pairwise_union_nempty: "A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> pairwise_union A B \<noteq> {}"
  by(auto simp add: pairwise_union_def)

definition aut_trans_one::"('state::type,'msg::type,'out::{conc, pcpo}) automaton
  \<Rightarrow> ('in \<Rightarrow> 'msg option) \<Rightarrow> ('in::cpo \<rightarrow> 'in) \<Rightarrow> 'in \<Rightarrow> 'state \<Rightarrow> ('in \<times> (('state \<times> 'out) set))" where
"aut_trans_one aut shd srt input state = (case (shd input) of None \<Rightarrow> (input, {(state,\<bottom>)}) | 
                    Some msg \<Rightarrow> (srt\<cdot>input, ((autTransition\<cdot>aut) state msg)))"



definition aut_comp_init::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton 
    \<Rightarrow> (('wout\<times>'sout\<times>'wstate\<times>'sstate)\<times> ('wout \<times> 'sout )) set" where
"aut_comp_init wa sa = (\<lambda>((wstate,wout),(sstate,sout)). ((wout,sout,wstate,sstate), (wout,sout))) `
                             pairwise_union (autInitConfig\<cdot>wa) (autInitConfig\<cdot>sa)"

lemma aut_comp_init_nempty: "aut_comp_init wa sa \<noteq> {}"
  apply(auto simp add: pairwise_union_def aut_comp_init_def)[1]
  using autinit_nempty by fastforce+


fun aut_comp_trans::"('wout \<Rightarrow> 'smsg option) \<Rightarrow> ('wout \<rightarrow> 'wout) \<Rightarrow> 
                     ('sout \<Rightarrow> 'wmsg option) \<Rightarrow> ('sout \<rightarrow> 'sout) \<Rightarrow> 
       ('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton 
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton  
    \<Rightarrow> ('wout\<times>'sout\<times>'wstate\<times>'sstate)
    \<Rightarrow> (('wout\<times>'sout\<times>'wstate\<times>'sstate)\<times> ('wout \<times> 'sout)) set" where
"aut_comp_trans whd wrt shd srt wa sa  (wout,sout,ws,ss) = (let (wOutNext, sTransResult) = aut_trans_one sa whd wrt wout ss;
                                               (sOutNext, wTransResult) = aut_trans_one wa shd srt sout ws
                                            in
            (\<lambda>((wstate,wout),(sstate,sout)). ((wOutNext \<Zcat>\<Zcat> wout,sOutNext \<Zcat>\<Zcat> sout,wstate,sstate),(wout,sout)))  `  pairwise_union wTransResult sTransResult)"

lemma aut_comp_trans_nempty: "aut_comp_trans whd wrt shd srt wa sa (wout,sout,ws,ss) \<noteq> {}"
  apply(auto simp add: aut_trans_one_def)[1]
  by(cases "whd wout"; cases "shd sout"; simp add: pairwise_union_nempty)

lift_definition aut_comp::"('wout \<Rightarrow> 'smsg option) \<Rightarrow> ('wout \<rightarrow> 'wout) \<Rightarrow> 
                     ('sout \<Rightarrow> 'wmsg option) \<Rightarrow> ('sout \<rightarrow> 'sout) \<Rightarrow>
       ('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton
    \<Rightarrow> (('wout\<times>'sout\<times>'wstate\<times>'sstate), unit,'wout \<times> 'sout) automaton" is
"\<lambda>whd wrt shd srt wa sa. (\<lambda>s m. aut_comp_trans whd wrt shd srt wa sa s, aut_comp_init wa sa)"
  using aut_comp_trans_nempty aut_comp_init_nempty by (metis prod_cases4)  







definition da_trans_one::"('state::type,'msg::type,'out::{conc, pcpo}) dAutomaton
  \<Rightarrow> ('in \<Rightarrow> 'msg option) \<Rightarrow> ('in::cpo \<rightarrow> 'in) \<Rightarrow> 'in \<Rightarrow> 'state \<Rightarrow> ('in \<times> (('state \<times> 'out)))" where
"da_trans_one aut shd srt input state = (case (shd input) of None \<Rightarrow> (input, (state,\<bottom>)) | 
                    Some msg \<Rightarrow> (srt\<cdot>input, ((dautTransition aut) state msg)))"


fun da_comp_trans::"('wout \<Rightarrow> 'smsg option) \<Rightarrow> ('wout \<rightarrow> 'wout) \<Rightarrow> 
                     ('sout \<Rightarrow> 'wmsg option) \<Rightarrow> ('sout \<rightarrow> 'sout) \<Rightarrow> 
       ('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton 
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton  
    \<Rightarrow> ('wout\<times>'sout\<times>'wstate\<times>'sstate) \<Rightarrow> unit
    \<Rightarrow> (('wout\<times>'sout\<times>'wstate\<times>'sstate)\<times> ('wout \<times> 'sout))" where
"da_comp_trans whd wrt shd srt wa sa  (wout,sout,ws,ss) _ = (let (wOutNext, (sNextState, sOut)) = da_trans_one sa whd wrt wout ss;
                                               (sOutNext, (wNextState, wOut)) = da_trans_one wa shd srt sout ws
                                            in
            ((wOutNext \<Zcat>\<Zcat> wOut, sOutNext \<Zcat>\<Zcat> sOut, wNextState, sNextState),((wOut,sOut))))"

definition da_comp::"('wout \<Rightarrow> 'smsg option) \<Rightarrow> ('wout \<rightarrow> 'wout) \<Rightarrow> 
                     ('sout \<Rightarrow> 'wmsg option) \<Rightarrow> ('sout \<rightarrow> 'sout) \<Rightarrow>
       ('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton
    \<Rightarrow> ('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton
    \<Rightarrow> (('wout\<times>'sout\<times>'wstate\<times>'sstate), unit,'wout \<times> 'sout) dAutomaton" where
"da_comp whd wrt shd srt wa sa = (| dautTransition = da_comp_trans whd wrt shd srt wa sa,
                                dautInitConfig = (
    let (wstate, wout) = dautInitConfig wa;
        (sstate, sout) = dautInitConfig sa in 
      ((wout, sout, wstate, sstate), (wout, sout))) |)"  

lemma da_comp_init:"dautInitConfig (da_comp whd wrt shd srt wa sa) = (let (wstate, wout) = dautInitConfig wa;
        (sstate, sout) = dautInitConfig sa in 
      ((wout, sout, wstate, sstate), (wout, sout)))"
  apply(simp add: da_comp_def)
  done

lemma da_comp_trans:"dautTransition (da_comp whd wrt shd srt wa sa) = da_comp_trans whd wrt shd srt wa sa"
  by(simp add: da_comp_def)

end