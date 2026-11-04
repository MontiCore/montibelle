theory RemovePotEffectChannel

imports stream.Stream automaton_testing.Effect  
      automaton.RefinementSignature stream.StreamAutomaton
    EffectDemo

begin




lift_definition oldAut'::"nat \<Rightarrow> (unit, nat\<times>bool , bool stream) automaton" is
"\<lambda>n. (\<lambda> s (msg_nat, msg_bool). if (msg_nat < n) then {((), \<up>True)} else 
      if (msg_nat < 2*n) then {((), \<up>msg_bool), ((), \<up>True)} else {((), \<up>True), ((), \<up>False)}, 
    {((), \<epsilon>)})"
  by auto

lift_definition newAut'::"nat \<Rightarrow> (unit, nat , bool stream) automaton" is
"\<lambda>n. (\<lambda> s msg. if (msg < 2*n) then {((), \<up>True)} else {((), \<up>True), ((), \<up>False)}, 
    {((), \<epsilon>)})"
  by auto

thm sem_inoutref


lemma del_chan_statesem: 
  "(\<lambda>spf. ID oo spf oo smap fst) ` stateSem stream_step (newAut' n) () 
    \<subseteq> stateSem stream_step (oldAut' n) ()"
  apply(rule sem_inoutref [where msgconv="fst"]; simp)
  apply(rule cfun_eqI, rename_tac s)
   apply(induct_tac s; simp?)

  apply(simp add: autTransition.rep_eq newAut'.rep_eq oldAut'.rep_eq)
  by(auto)



theorem del_chan: 

  "{smap fst} \<then> ssem (newAut' 50)
    \<subseteq> ssem (oldAut' 50)"

  apply(auto simp add: seqcomp_image sem_def)
  apply(auto simp add: autInitConfig.rep_eq newAut'.rep_eq oldAut'.rep_eq)
  using del_chan_statesem by auto


lemma smap_fst_zip[simp]: "#xs \<le> #ys \<Longrightarrow> smap fst\<cdot>(szip\<cdot>xs\<cdot>ys) = xs"
  apply(induction xs arbitrary: ys; simp?)
  apply(rule adm_all)
  apply(rule adm_imp; simp?)
   apply (meson adm_upward mono_slen trans_lnle)
  by(case_tac ys; simp)

lemma szip_fst [simp]: "{(\<Lambda> sb . szip\<cdot>sb\<cdot>(oracle\<cdot>sb)) | oracle. \<forall>sb. #sb \<le> #(oracle\<cdot>sb)} \<then> {smap fst} = {ID}"
  apply(auto simp add: seqcomp_insert oo_def)
   apply(rule cfun_eqI, rename_tac s)
   apply(induct_tac s; simp add: ora_hd)
  apply(rule exI [where x="(\<Lambda> sb . szip\<cdot>sb\<cdot>(\<up>undefined\<^sup>\<infinity>))"]; simp add: ID_def)
  apply(rule exI [where x="(\<Lambda> sb . (\<up>undefined\<^sup>\<infinity>))"], simp)
  done  
  
lemma seqcomp_assoc: "(A \<then> B) \<then> C = A \<then> (B \<then> C)"
  apply(auto simp add: seqcomp_insert image_iff )
  by (metis (no_types, opaque_lifting) cfcomp2 cfun_eqI)+

lemma del_chan_variante_A:

        "ssem (newAut' 50)
  \<subseteq> {(\<Lambda> sb . szip\<cdot>sb\<cdot>(oracle\<cdot>sb)) | oracle. \<forall>sb. #sb \<le> #(oracle\<cdot>sb)} \<then> ssem (oldAut' 50)"

  apply(rule dual_order.trans [where b="{(\<Lambda> sb . szip\<cdot>sb\<cdot>(oracle\<cdot>sb)) | oracle. \<forall>sb. #sb \<le> #(oracle\<cdot>sb)} \<then> {smap fst} \<then> ssem (newAut' 50)"])
   apply(rule monoD [where f="\<lambda>S. {(\<Lambda> sb . szip\<cdot>sb\<cdot>(oracle\<cdot>sb)) | oracle. \<forall>sb. #sb \<le> #(oracle\<cdot>sb)} \<then> S"])
  apply (simp add: monoI seqcomp_subset)
  using del_chan apply simp
  by (simp add: seqcomp_assoc[symmetric])

end