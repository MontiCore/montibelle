theory AutForRel
imports Nda2DaSet

begin


definition createAutForRel::
          "('input \<rightarrow> 'msg lift)
          \<Rightarrow> ('input \<rightarrow> 'input)
          \<Rightarrow> ('stateRef::type, 'msg, 'out::conc) dAutomaton 
          \<Rightarrow> ('stateOrig::type, 'msg, 'out::conc) automaton
          \<Rightarrow> ('stateRef \<Rightarrow> 'input \<Rightarrow> 'stateOrig)
          \<Rightarrow> 'input::pcpo 
          \<Rightarrow> ('stateOrig + ('stateRef \<times> 'input), 'msg, 'out::conc) dAutomaton" where
"createAutForRel myShd mySrt dAutRef ndaOrig getOrigState input = 
  \<lparr> dautTransition = (\<lambda> (state) (msg). 
          case state of (Inl origiState) \<Rightarrow> 
            apfst (\<lambda>nextOrigState.(Inl nextOrigState)) (SOME x. x\<in>(autTransition\<cdot>ndaOrig) origiState msg)
          | (Inr (stateRef, input)) \<Rightarrow> 
              if (myShd\<cdot>input \<noteq> Def msg) 
                then apfst (\<lambda>nextOrigState.(Inl (nextOrigState))) (SOME x. x\<in>(autTransition\<cdot>ndaOrig) (getOrigState stateRef input) msg)
                else apfst (\<lambda>nextState. (Inr (nextState, mySrt\<cdot>input))) ((dautTransition dAutRef) (stateRef) (msg))), 
    dautInitConfig = apfst (\<lambda>initialState. (Inr (initialState, input))) ((dautInitConfig dAutRef) ) 
  \<rparr>"

lemma autforrel_initconfig: "dautInitConfig (createAutForRel myShd mySrt daRef ndaOrig getOrigState input)
  = apfst (\<lambda>initialState. (Inr (initialState, input))) ((dautInitConfig daRef) ) "
  by(simp add: createAutForRel_def)

lemma auttrans_some_in[simp]: "(SOME x. x \<in> (autTransition\<cdot>nda) state msg)
       \<in> (autTransition\<cdot>nda) state msg"
  by (metis spf2da_trans2 stateSemf_def tfl_some; fail)

lemma autforrel_in: 
  assumes "apfst (\<lambda>s. getOrigState s input) (dautInitConfig daRef) \<in> autInitConfig\<cdot>ndaOrig"
  and "\<And>input msg refState. Inv refState input \<Longrightarrow> myShd\<cdot>input = Def msg \<Longrightarrow>
       apfst (\<lambda>x. getOrigState x (mySrt\<cdot>input)) (dautTransition daRef refState msg)
       \<in> (autTransition\<cdot>ndaOrig) (getOrigState refState input) msg"
  and "Inv (fst (dautInitConfig daRef)) input"
  and "\<And>refState input msg. Inv refState input \<Longrightarrow> myShd\<cdot>input = Def msg \<Longrightarrow> Inv (fst (dautTransition daRef refState msg)) (mySrt\<cdot>input)"
  shows "daSem (step_create\<cdot>myShd\<cdot>mySrt) (createAutForRel myShd mySrt daRef ndaOrig getOrigState input) 
        \<in> sem (step_create\<cdot>myShd\<cdot>mySrt) ndaOrig"
  apply(rule da_in_nda [where f="(\<lambda>s. case s of Inl s \<Rightarrow> s | Inr (s,input) \<Rightarrow> getOrigState s input)" 
                        and Inv="(\<lambda>s. case s of Inl s \<Rightarrow> True | Inr (s,input) \<Rightarrow> Inv s input)"]; simp?)
   apply(auto simp add: createAutForRel_def apfst_compose o_def)[4]
   apply(simp add: assms(1); fail)
  apply(rename_tac state msg)
  apply(case_tac state; simp add: apfst_compose o_def id_def[symmetric])
  apply(rename_tac oldState msg subState)
  apply(case_tac subState; rename_tac refState input)
  apply(auto simp add: apfst_compose o_def id_def[symmetric])[1]
    apply (simp add: assms(2); fail)
   apply (simp add: assms(3); fail)

  apply(rename_tac state msg)
  apply(case_tac state; simp add: apfst_compose o_def id_def[symmetric])
  apply(rename_tac oldState msg subState)
  apply(case_tac subState; rename_tac refState input)
  apply(auto simp add: apfst_compose o_def id_def[symmetric])[1]
  by (simp add: assms(4); fail)


lemma autforrel_statesem_input: "daStateSem s (createAutForRel myShd mySrt daRef ndaOrig getOrigState inputA)
  = daStateSem s (createAutForRel myShd mySrt daRef ndaOrig getOrigState inputB)"
  by(simp add: daStateSem_def createAutForRel_def)

lemma autforrel_input_statesem: 
    "daStateSem (step_lnat_add\<cdot>(step_create\<cdot>myShd\<cdot>mySrt))
          (createAutForRel myShd mySrt daRef ndaOrig getOrigState input) (Inr (s, input))\<cdot>(input, ln)
     = daStateSem (step_lnat_add\<cdot>(step_create\<cdot>myShd\<cdot>mySrt)) daRef s\<cdot>(input, ln)"
  apply(induction ln arbitrary: input s)
    apply (simp; fail)
   apply (simp; fail)

  apply(case_tac "myShd\<cdot>input")
   apply(subst dastatesem_bot2; induction ln; simp add: step_create_insert) 

     apply(subst dastatesem_step, simp add: case_prod_beta)
  apply(subst(2) dastatesem_step, simp add: case_prod_beta)
  apply(simp add: step_create_insert)
  apply(rule arg_cong2 [where f="(\<lambda>x y. x \<Zcat>\<Zcat> y)"])
   apply (subst createAutForRel_def)
   apply(auto)[1]

  apply (subst(2) createAutForRel_def; simp)
  by (metis autforrel_statesem_input)

lemma autforrel_input:
  shows "daSem (step_create\<cdot>myShd\<cdot>mySrt) (createAutForRel myShd mySrt daRef ndaOrig getOrigState input)\<cdot>input 
       = daSem (step_create\<cdot>myShd\<cdot>mySrt) daRef\<cdot>input"
  apply(simp add: dasem_unfold)
  apply(rule arg_cong2 [where f="(\<lambda>x y. x \<Zcat>\<Zcat> y)"])
   apply(simp add: createAutForRel_def)
  apply(subst(1) da_add_lnat[symmetric], subst(2) da_add_lnat[symmetric])
  apply(simp add: autforrel_initconfig)
  using autforrel_input_statesem by metis


end