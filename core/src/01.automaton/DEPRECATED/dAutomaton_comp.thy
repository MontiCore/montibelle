theory dAutomaton_comp
  imports dAutomaton_causal spf.SPFcomp
begin


fun compTransition::"('s1::type \<Rightarrow> 'in1\<^sup>\<surd> \<Rightarrow> ('s1 \<times> 'out1\<^sup>\<surd>)) \<Rightarrow> 
                     ('s2::type \<Rightarrow> 'in2\<^sup>\<surd> \<Rightarrow> ('s2 \<times> 'out2\<^sup>\<surd>)) \<Rightarrow> 
(('s1\<times>'s2 \<times>(('out1 \<union> 'out2) - ('in1 \<union> 'in2))\<^sup>\<surd>) \<Rightarrow> 
(('in1 \<union> 'in2) -  ('out1 \<union> 'out2))\<^sup>\<surd> \<Rightarrow> 
(('s1\<times>'s2 \<times>'buf\<^sup>\<surd>) \<times> ('out1 \<union> 'out2)\<^sup>\<surd>))"where
"compTransition t1 t2 (s1,s2,buf) sbe = 
(let (s1o,sbe1o) = (t1 s1 (sbeUnion sbe buf));
     (s2o,sbe2o) = (t2 s2 (sbeUnion sbe buf))  in
          ((s1o,s2o, sbeUnion sbe1o sbe2o), sbeUnion sbe1o sbe2o))"

text\<open>The function @{term compTransition} maps two transition
functions to their composed transition function.\<close>

definition daComp::"('s1::type,'in1,'out1)dAutomaton_strong \<Rightarrow> 
('s2::type,'in2,'out2)dAutomaton_strong \<Rightarrow> 
(('s1\<times>'s2\<times>(('out1 \<union> 'out2) - ('in1 \<union> 'in2))\<^sup>\<surd>),
(('in1 \<union> 'in2) - ('out1 \<union> 'out2)),('out1 \<union> 'out2))dAutomaton_strong"
  where
"daComp \<equiv> \<lambda>aut1 aut2. 
(| dawTransition = 
          compTransition (dawTransition aut1) (dawTransition aut2), 
   dawInitState =((dawInitState aut1),(dawInitState aut2), 
                      sbeUnion (dasInitOut aut1)(dasInitOut aut2)),
   dasInitOut = sbeUnion(dasInitOut aut1) (dasInitOut aut2) |)"

(*
subsubsection\<open>Strong composition lemmas \<close>

instance %invisible union :: (chan,chan)finite (*Gilt nicht für empty domains, TODO\<And>*)
  sorry

instance %invisible minus :: (chan,chan)finite (*Gilt nicht für empty domains, TODO\<And>*)
  sorry

default_sort "{somechan,finite}"

lemma final_eval_autcomp:
"dasSem(daComp aut1 aut2) \<sqsubseteq> (dasSem aut1) \<otimes> (dasSem aut2)"
  sorry

(*TODO: something else than Rep_spfs_fun\<cdot>(semantik_strong..) *)
lemma final_eval_autcomp_eq:
  assumes "sbLen sb = \<infinity>"
  shows   "dasSem(daComp aut1 aut2)\<cdot>sb = 
           ((dasSem aut1) \<otimes> (dasSem aut2))\<cdot>sb"
  apply(rule sblen_sbeqI)
   apply (simp add: final_eval_autcomp monofun_cfun)
  by (metis assms dassem_len fold_inf sblen_empty)
*)
end
