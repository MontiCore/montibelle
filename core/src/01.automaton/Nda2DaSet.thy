theory Nda2DaSet
  imports automaton.Automaton automaton.DeterministicAutomaton
          Steps


begin



definition nda2daset::"('state::type  ,'msg::type, 'output::conc) automaton \<Rightarrow> 
                       ('state\<times>'other ,'msg      , 'output      ) dAutomaton set" where
"nda2daset nda = {(| dautTransition = trans, dautInitConfig = apfst (\<lambda>x. (x,other)) init |) 
        | trans init other. init \<in> autInitConfig\<cdot>nda 
            \<and> (\<forall>state other msg. apfst fst (trans (state,other) msg) 
                                      \<in> (autTransition\<cdot>nda) state msg)}"

lemma nda2daset_in:
  assumes "\<And>msg state other. (apfst fst) (dautTransition da (state, other) msg) \<in> (autTransition\<cdot>nda) state msg"
    and "(apfst fst) (dautInitConfig da) \<in> autInitConfig\<cdot>nda"
  shows "da \<in> nda2daset nda"
  apply(auto simp add: nda2daset_def)[1]
  apply(rule exI [where x="dautTransition da"])
  apply(rule exI [where x="fst (fst (dautInitConfig da))"])
  apply(rule exI [where x="snd (dautInitConfig da)"])
  apply auto[1]
  apply (metis(full_types) dAutomaton.surjective old.unit.exhaust prod.collapse)
   apply (metis Pair_equalI assms(2) fst_apfst snd_apfst)
  by (simp add: assms(1))

lemma nda2da_trans: assumes "da \<in> nda2daset nda" 
  shows "apfst fst (dautTransition da state msg) \<in> (autTransition\<cdot>nda) (fst state) msg"
  apply(insert assms, simp add: nda2daset_def)
  by (metis dAutomaton.select_convs(1) eq_fst_iff)

lemma nda2da_trans_snd: assumes "da \<in> nda2daset nda" 
  shows "snd (dautTransition da state msg) \<in> snd ` ((autTransition\<cdot>nda) (fst state) msg)"
  using nda2da_trans by (metis assms image_iff snd_apfst)

lemma nda2da_init: assumes "da \<in> nda2daset nda" 
  shows "apfst fst (dautInitConfig da) \<in> (autInitConfig\<cdot>nda)"
  apply(insert assms, simp add: nda2daset_def)
  by fastforce

context
begin
  lemma nda2daset_refine_statesem: assumes "da \<in> nda2daset nda"
  shows "daStateSem step da s \<in> stateSem step nda (fst s)"
  apply(rule dasseminssem_rule)
  using assms apply(simp add: nda2daset_def case_prod_beta)
  by (metis apfst_conv dAutomaton.select_convs(1) prod.collapse)

lemma nda2daset_refine_sem: assumes "da \<in> nda2daset nda"
  shows "daSem step da \<in> sem step nda"
  apply(rule daseminsem_rule [of _ "fst"])
  using assms apply(auto simp add: nda2daset_def case_prod_beta Let_def)[1]
  by (metis assms nda2daset_refine_statesem)

theorem "(\<lambda>da. daStateSem step da (state,x)) ` (nda2daset nda) \<subseteq> stateSem step nda state"
  using nda2daset_refine_statesem by fastforce

theorem nda2daset_subset:"(daSem step) ` (nda2daset nda) \<subseteq> sem step nda"
  using nda2daset_refine_sem by fastforce
end



context
begin

definition spf2da::"('msg \<Rightarrow> 'input) \<Rightarrow> ('state,'msg,'output::conc) automaton \<Rightarrow> (('msg \<Rightarrow> 'input::{cpo,conc} \<rightarrow> 'output) \<rightarrow> 'input \<rightarrow> 'output)
  \<Rightarrow> ('input \<rightarrow> 'output) \<Rightarrow> ('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton" where
"spf2da conv nda step spf = (| dautTransition = (\<lambda>(state,spf) msg. if spf\<in>stateSem step nda state 
  then (SOME ((nextState, spf2),out).  (\<forall>input. spf\<cdot>((conv msg) \<Zcat>\<Zcat> input) = out \<Zcat>\<Zcat> spf2\<cdot>input )
                                                    \<and> (nextState,out) \<in> (autTransition\<cdot>nda) state msg 
                                                    \<and> spf2\<in>stateSem step nda nextState)
  else apfst (\<lambda>x. (x,\<bottom>)) (SOME (nextState,out). (nextState,out) \<in> (autTransition\<cdot>nda) state msg)), 
                          dautInitConfig = if spf\<in>sem step nda
            then (SOME ((state, spf2),out).  (\<forall>input. spf\<cdot>input = out \<Zcat>\<Zcat> spf2\<cdot>input) 
                                                          \<and> (state,out) \<in> autInitConfig\<cdot>nda 
                                                          \<and> spf2\<in>stateSem step nda state)
            else apfst (\<lambda>x. (x,\<bottom>)) (SOME (state,out). (state,out) \<in> autInitConfig\<cdot>nda)  |)"

lemma spf2da_trans1: assumes "spf \<in> stateSem step nda state" and "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
  shows "let ((nextState,spf2),out) = dautTransition (spf2da conv nda step someSpf) (state,spf) msg in
     (\<forall>input. spf\<cdot>((conv msg) \<Zcat>\<Zcat> input) = out \<Zcat>\<Zcat> spf2\<cdot>input )
     \<and> (nextState,out) \<in> (autTransition\<cdot>nda) state msg 
     \<and> spf2\<in>stateSem step nda nextState"
  using assms(1) apply(simp add: spf2da_def Let_def case_prod_beta')
  apply(rule someI_ex)
  apply (auto)[1]
  by (metis assms(2) stateSemf_def)

lemma tuple_to_apfst:"(fst(fst P), snd P) = (apfst fst) P"
  by (simp add: prod_eqI)

lemma spf2da_trans1': assumes "spf \<in> stateSem step nda state" and "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
  shows " apfst fst (dautTransition (spf2da conv nda step someSpf) (state,spf) msg) \<in> (autTransition\<cdot>nda) state msg "
proof - 
  have "let ((nextState,spf2),out) = dautTransition (spf2da conv nda step someSpf) (state,spf) msg in
     (\<forall>input. spf\<cdot>((conv msg) \<Zcat>\<Zcat> input) = out \<Zcat>\<Zcat> spf2\<cdot>input )
     \<and> (nextState,out) \<in> (autTransition\<cdot>nda) state msg 
     \<and> spf2\<in>stateSem step nda nextState"
    by(rule spf2da_trans1; simp add: assms)
  thus ?thesis by force
qed

lemma spf2da_trans2: assumes "spf \<notin> stateSem step nda state"
  shows " apfst fst (dautTransition (spf2da conv nda step someSpf) (state,spf) msg) \<in> (autTransition\<cdot>nda) state msg "
  using assms(1)  apply(simp add: spf2da_def Let_def case_prod_beta' tuple_to_apfst apfst_compose o_def id_def[symmetric])
  apply(rule someI_ex)
  by (meson auttransition_nempty neq_emptyD)


lemma spf2da_init1: "spf \<in> sem step nda \<Longrightarrow> 
  let ((state,spf2),out) = dautInitConfig (spf2da conv nda step spf) in
          (\<forall>input. spf\<cdot>input = out \<Zcat>\<Zcat> spf2\<cdot>input) 
        \<and> (state,out) \<in> autInitConfig\<cdot>nda 
        \<and> spf2\<in>stateSem step nda state"
  apply(simp add: spf2da_def Let_def)
  apply(rule someI_ex)
  apply (auto simp add: sem_def)[1]
  by auto

lemma spf2da_init2: "spf \<notin> sem step nda \<Longrightarrow> 
  let ((state,spf2),out) = dautInitConfig (spf2da conv nda step spf) in
         (state,out) \<in> autInitConfig\<cdot>nda "
  apply(simp add: spf2da_def Let_def case_prod_beta')
  apply(rule someI_ex)
  using autinit_nempty by blast


theorem spf2da_in_nda2daset:
  assumes "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
  shows "spf2da conv nda step spf \<in> nda2daset nda"
  apply(rule nda2daset_in)
   apply (case_tac "other \<in> stateSem step nda state")
     apply (simp add: assms spf2da_trans1')
  apply(simp add: spf2da_trans2)
   apply (cases "spf\<in>sem step nda")
  using spf2da_init1 apply (auto simp add: prod_eqI case_prod_beta' Let_def)[1]
    apply(subst (asm) tuple_to_apfst, auto)
  using spf2da_init2 apply (auto simp add: prod_eqI case_prod_beta' Let_def)[1]
    apply(subst (asm) tuple_to_apfst, auto)
  done

(*
(* Outdated, gibt in Steps.thy (und weiter unten) interessantere Sachen *)
lemma spf2da_statesem_eq:  
  assumes 
    step_unfold: "\<And>input msg. shd\<cdot>((conv msg)\<Zcat>\<Zcat>input) = Def msg"
    and srt_conv: "\<And>input msg. srt\<cdot>(conv msg\<Zcat>\<Zcat>input) = input"
    and spf_in: "spf \<in> stateSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) nda s"
  shows "spf\<cdot>(input,ln) 
  = daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) (spf2da conv nda (step_create\<cdot>shd\<cdot>srt) someSpf) (s,\<Lambda> i. spf\<cdot>(i,\<infinity>))\<cdot>(input,ln)"
  using spf_in proof(induction ln arbitrary: input s spf rule: lnat_ind)
  case 1
  then show ?case by simp
next
case 2
  then show ?case by simp
next
  case (3 ln)
  then show ?case 
  proof (cases "shd\<cdot>input")
    case bottom
    then show ?thesis       
      apply(subst dastatesem_step, simp add: step_create_insert)
      sorry
  next
    case (Def msg)
    obtain nextState out spf2 where daut_def: "((nextState,spf2), out) 
      = ((dautTransition (spf2da conv nda (step_create\<cdot>shd\<cdot>srt) someSpf)) (s,\<Lambda> i. spf\<cdot>(i,\<infinity>)) msg)"
      by (metis surj_pair)

    have spfinf_in: "(\<Lambda> i. spf\<cdot>(i,\<infinity>)) \<in> stateSem ((step_create\<cdot>shd\<cdot>srt)) nda s" 
      sorry (* existiert noch nicht. Sollte in Steps.thy rein *)
    have spfcreate_f: "(\<And>input f msg. step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>(conv msg\<Zcat>\<Zcat>input) = f msg\<cdot>input)"
      by (simp add: step_create_insert step_unfold srt_conv) 
    have spf_step: "(\<forall>input. (\<Lambda> i. spf\<cdot>(i,\<infinity>))\<cdot>((conv msg) \<Zcat>\<Zcat> input) = out \<Zcat>\<Zcat> spf2\<cdot>input )"
        and "(nextState,out) \<in> (autTransition\<cdot>nda) s msg"
        and "spf2\<in>stateSem (step_create\<cdot>shd\<cdot>srt) nda nextState"
      apply(insert spf2da_trans1[of _ _ _  _ conv someSpf msg,OF spfinf_in spfcreate_f])
      using daut_def by fastforce +

    obtain spf2_lnat where spf2l_def: "(\<Lambda> i. spf2_lnat\<cdot>(i,\<infinity>)) = spf2"
          and spf_step: "spf\<cdot>(input, lnsuc\<cdot>ln) = out \<Zcat>\<Zcat> spf2_lnat\<cdot>(srt\<cdot>input, ln)" 
          and spf2l_in: "spf2_lnat \<in> stateSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) nda nextState"
      sorry
    show ?thesis
      apply(subst dastatesem_step, simp add: daut_def[symmetric] step_create_insert2[OF Def])
      apply(simp add: spf_step spf2l_def[symmetric])
      using "3.IH" spf2l_in apply fastforce
      oops
*)

lemma
  assumes shd_conv:"\<And>input msg. shd\<cdot>input = Def msg \<Longrightarrow> input = conv msg\<Zcat>\<Zcat>srt\<cdot>input"
      and "\<And>input msg. shd\<cdot>(conv msg \<Zcat>\<Zcat> input) = Def msg"
      and "\<And>input msg. srt\<cdot>(conv msg \<Zcat>\<Zcat> input) = input"
    and spf_in: "spf \<in> stateSem (step_create\<cdot>shd\<cdot>srt) nda s"
  shows "daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) (spf2da conv nda (step_create\<cdot>shd\<cdot>srt) someSpf) (s,spf)\<cdot>(input,lnsuc\<cdot>ln) 
          \<sqsubseteq> spf\<cdot>input"
  oops
(*
  using spf_in  proof(induction ln arbitrary: spf s)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case apply (subst dastatesem_step, simp)
    sorry (* ... schwer ? *)
next
  case (lnsuc ln)
  then show ?case
  proof (cases "shd\<cdot>input")
    case bottom
    then show ?thesis sorry
  next
    case (Def msg)
  obtain nextState out spf2 where daut_def: "((nextState,spf2), out) = ((dautTransition (spf2da conv nda (step_create\<cdot>shd\<cdot>srt) someSpf)) (s,spf) msg)"
    by (metis surj_pair)
  have spf_step: "(\<forall>input. out \<Zcat>\<Zcat> spf2\<cdot>input \<sqsubseteq>spf\<cdot>((conv msg) \<Zcat>\<Zcat> input) )"
      and "(nextState,out) \<in> (autTransition\<cdot>nda) s msg"
      and "spf2\<in>stateSem (step_create\<cdot>shd\<cdot>srt) nda nextState"
    using spf2da_trans1 apply (auto simp add: case_prod_conv case_prod_beta)
    sorry
    then show ?thesis oops
  *)

lemma spf2da_statesem_eq:  
  assumes step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
        and input_induction: "\<And>s P. adm P \<Longrightarrow> (\<And>xs. (\<forall>f. step\<cdot>f\<cdot>xs = \<bottom>) \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
    and spf_in: "spf \<in> stateSem step nda s"
  shows "spf\<cdot>input = daStateSem step (spf2da conv nda step someSpf) (s,spf)\<cdot>input"
  using spf_in proof(induction input arbitrary: spf s rule: input_induction )
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by(subst dastatesem_step, simp)
next
  case (3 x xs)
  obtain nextState out spf2 where daut_def: "((nextState,spf2), out) = ((dautTransition (spf2da conv nda step someSpf)) (s,spf) x)"
    by (metis surj_pair)
  hence spf_step: "(\<forall>input. spf\<cdot>((conv x) \<Zcat>\<Zcat> input) = out \<Zcat>\<Zcat> spf2\<cdot>input )"
      and "(nextState,out) \<in> (autTransition\<cdot>nda) s x"
      and "spf2\<in>stateSem step nda nextState"
    apply(insert spf2da_trans1[where spf=spf and step=step and nda=nda and conv=conv and someSpf=someSpf and msg=x and state=s], simp_all add: "3.prems"Let_def case_prod_beta')
    apply (metis fst_conv snd_conv step_unfold)+
    done
  then show ?case 
    apply(simp add: spf_step)
    apply(subst dastatesem_step, simp add: daut_def[symmetric] step_unfold)
    by (simp add: "3.IH")
qed

theorem spf2da_sem_eq:  
  assumes step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
        and input_induction: "\<And>s P. adm P \<Longrightarrow> (\<And>xs. (\<forall>f. step\<cdot>f\<cdot>xs = \<bottom>) \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
        and spf_in: "spf \<in> sem step nda"
shows "spf = daSem step (spf2da conv nda step spf)"
proof (rule cfun_eqI) 
  fix input
  obtain nextState out spf2 where daut_def: "((nextState,spf2), out) = ((dautInitConfig (spf2da conv nda step spf)))"
    by (metis surj_pair)
  hence spf_step: "(\<forall>input. spf\<cdot>input = out \<Zcat>\<Zcat> spf2\<cdot>input)" 
        and "(nextState,out) \<in> autInitConfig\<cdot>nda"
        and spf2_in: "spf2\<in>stateSem step nda nextState"
    apply (metis (mono_tags, lifting) case_prod_beta' fst_conv snd_conv spf2da_init1 spf_in) 
    apply (metis apfst_conv daut_def fst_conv nda2da_init spf2da_in_nda2daset step_unfold)
    by (metis (no_types, lifting) case_prod_conv daut_def spf2da_init1 spf_in)
  have "spf2\<cdot>input = daStateSem step (spf2da conv nda step spf) (nextState,spf2)\<cdot>input"
    apply(rule spf2da_statesem_eq)
      apply (simp add: step_unfold)
    using input_induction apply blast
    by (simp add: spf2_in)
  thus "spf\<cdot>input = daSem step (spf2da conv nda step spf)\<cdot>input" 
    using spf_in     apply(simp add: spf_step)
    apply(subst dasem_unfold, simp add: daut_def[symmetric] step_unfold)
    done
qed

theorem nda2daset_below:
  fixes step :: "('msg \<Rightarrow> 'input::{conc} \<rightarrow> 'output::{conc,cpo}) \<rightarrow> 'input \<rightarrow> 'output" 
  assumes step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
     and input_induction: "\<And>s P. adm P \<Longrightarrow> (\<And>xs. (\<forall>f. step\<cdot>f\<cdot>xs = \<bottom>) \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
  shows "sem step nda  \<le> (\<lambda>da. daSem step da) ` ((nda2daset nda)::('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton set)"
proof 
  fix spf
  assume as: "spf \<in> sem step nda"
  have "spf2da conv nda step spf \<in> nda2daset nda"
    by (simp add: spf2da_in_nda2daset step_unfold)
  hence "daSem step (spf2da conv nda step spf) \<in> (\<lambda>da. daSem step da) ` ((nda2daset nda)::('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton set)" 
    apply(rule rev_image_eqI [where x="spf2da conv nda step spf"])
    ..
  thus "spf \<in> (\<lambda>da. daSem step da) ` ((nda2daset nda)::('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton set)"
    using spf2da_sem_eq as input_induction step_unfold by metis 
qed

end


theorem nda2daset:
  fixes step :: "('msg \<Rightarrow> 'input::{conc} \<rightarrow> 'output::{conc,cpo}) \<rightarrow> 'input \<rightarrow> 'output" 
  assumes step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
     and input_induction: "\<And>s P. adm P \<Longrightarrow> (\<And>xs. (\<forall>f. step\<cdot>f\<cdot>xs = \<bottom>) \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
  shows "sem step nda  = (\<lambda>da. daSem step da) ` ((nda2daset nda)::('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton set)"
  apply(rule antisym)
  apply(rule nda2daset_below [where conv=conv])
  apply (simp add: step_unfold; fail)
  apply(rule input_induction; simp; fail) 
  by (simp add: nda2daset_subset)


lemma nda2daset_lnatadd:
  fixes shd::"'input::{conc} \<rightarrow> 'msg::type lift"
    and srt::"'input \<rightarrow> 'input"
  assumes shd_conv:"\<And>input msg. shd\<cdot>input = Def msg \<Longrightarrow> input = conv msg\<Zcat>\<Zcat>srt\<cdot>input"
      and "\<And>input msg. shd\<cdot>(conv msg \<Zcat>\<Zcat> input) = Def msg"
      and "\<And>input msg. srt\<cdot>(conv msg \<Zcat>\<Zcat> input) = input"
  shows "sem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) nda  
    = (\<lambda>da. daSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) da) ` ((nda2daset nda)::('state\<times>('input\<times>lnat\<rightarrow>'output::conc), 'msg, 'output) dAutomaton set)"
  apply(rule nda2daset [where conv="\<lambda>msg. (conv msg, lnsuc\<cdot>\<bottom>)"])
   apply(simp add: assms conc_prod_def step_create_insert; fail)
proof -
  fix s P
  assume "adm P" and p_bot:"(\<And>xs. \<forall>f. step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)\<cdot>f\<cdot>xs = \<bottom> \<Longrightarrow> P xs)"
    and p_step:"(\<And>x xs. P xs \<Longrightarrow> P ((conv x, lnsuc\<cdot>\<bottom>)\<Zcat>\<Zcat>xs))"
  have "\<And>input ln. P (input, ln)"
  proof -
    fix input ln
    show "P(input,ln)"
    proof(induction "ln" arbitrary: "input" rule:lnat_ind)
      case 1
      then show ?case apply(rule adm_all)
        by(rule adm2adm_fst [OF \<open>adm P\<close>])
    next
      case 2
      thus ?case 
        by (simp add: \<open>\<And>xs. \<forall>f. step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)\<cdot>f\<cdot>xs = \<bottom> \<Longrightarrow> P xs\<close>)
    next
      case (3 ln)
      assume as: "\<And>input. P (input, ln)"
      have split: "\<And>msg. shd\<cdot>input = Def msg \<Longrightarrow>
        (input, lnsuc\<cdot>ln) = (conv msg, lnsuc\<cdot>\<bottom>) \<Zcat>\<Zcat> (srt\<cdot>input, ln)"
        by(simp add: conc_prod_def shd_conv) 
      show ?case
        apply(cases "shd\<cdot>input")
        apply(rule p_bot, simp add: step_create_insert)
        apply(subst split, simp)
        apply(rule p_step)
        by (simp add: as)
    qed
  qed
  thus "P s"
    using prod_cases by blast
qed

end
