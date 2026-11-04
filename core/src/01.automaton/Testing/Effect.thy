theory Effect
  imports automaton.Automaton automaton.DeterministicAutomaton 
    automaton.Steps automaton.Nda2DaSet


begin

default_sort type

locale aut_no_effect =
  fixes restrict1::"'out1::{conc,pcpo} \<rightarrow> 'common::{conc,pcpo}"
    and restrict2::"'out2::{conc,pcpo} \<rightarrow> 'common"
    and shd1::"'in1::{cpo,len} \<rightarrow> 'msg1 lift" 
    and shd2::"'in2::{cpo,len} \<rightarrow> 'msg2 lift"
    and srt1::"'in1 \<rightarrow> 'in1" 
    and srt2::"'in2 \<rightarrow> 'in2" 

    and eq_on_msg::"'msg1 \<Rightarrow> 'msg2 \<Rightarrow> bool"
    and eq_on_input::"'in1 \<Rightarrow> 'in2 \<Rightarrow> bool"
assumes 
        bot_iff:"\<And>input1 input2.  #input1 = #input2 \<Longrightarrow> shd1\<cdot>input1 = \<bottom> \<longleftrightarrow> shd2\<cdot>input2=\<bottom>"
    and eq_input2msg:"\<And>input1 input2 msg1 msg2. eq_on_input input1 input2 \<Longrightarrow> (shd1\<cdot>input1) = Def msg1 \<Longrightarrow> (shd2\<cdot>input2) = Def msg2
            \<Longrightarrow> eq_on_msg msg1 msg2"
    and eq_input_srt: "\<And>input1 input2. eq_on_input input1 input2 \<Longrightarrow> eq_on_input (srt1\<cdot>input1) (srt2\<cdot>input2)"

    and restrict1_split: "\<And>a as b bs. restrict1\<cdot>(a\<Zcat>\<Zcat>as) = restrict1\<cdot>a \<Zcat>\<Zcat> restrict1\<cdot>as"
    and restrict2_split: "\<And>a as b bs. restrict2\<cdot>(a\<Zcat>\<Zcat>as) = restrict2\<cdot>a \<Zcat>\<Zcat> restrict2\<cdot>as"

    and restrict_bot: "restrict1\<cdot>\<bottom> = restrict2\<cdot>\<bottom>"
    and len_srt:"\<And>input1 input2. #input1 = #input2 \<Longrightarrow> #(srt1\<cdot>input1) = #(srt2\<cdot>input2)"
begin


theorem no_effect_da:
      fixes aut1::"('state1::type,'msg1::type,'out1::{conc, pcpo}) dAutomaton"
        and aut2::"('state2::type,'msg2::type,'out2::{conc, pcpo}) dAutomaton"
        and eq_on_state::"'state1 \<Rightarrow> 'state2 \<Rightarrow> bool"
  assumes trans_state: "\<And>state1 state2 msg1 msg2 nextState1 out1 nextState2 out2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
            eq_on_state (fst (dautTransition aut1 state1 msg1)) 
                        (fst (dautTransition aut2 state2 msg2))"
    and trans_out:"\<And>state1 state2 msg1 msg2 nextState1 out1 nextState2 out2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
             restrict1\<cdot>(snd (dautTransition aut1 state1 msg1)) 
           = restrict2\<cdot>(snd (dautTransition aut2 state2 msg2))" 

    and len_eq: "#input1 = #input2" 
    and eq_in: "eq_on_input input1 input2"
    and eq_state:"eq_on_state s1 s2" 

shows "restrict1\<cdot>((daStateSem (step_create\<cdot>shd1\<cdot>srt1) aut1 s1)\<cdot>input1) 
     = restrict2\<cdot>((daStateSem (step_create\<cdot>shd2\<cdot>srt2) aut2 s2)\<cdot>input2)"
proof -
  have "\<And>ln. restrict1\<cdot>((daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd1\<cdot>srt1)) aut1 s1)\<cdot>(input1, ln)) 
      = restrict2\<cdot>((daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd2\<cdot>srt2)) aut2 s2)\<cdot>(input2, ln))"
  proof -
    fix ln
    show "restrict1\<cdot>((daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd1\<cdot>srt1)) aut1 s1)\<cdot>(input1, ln)) 
      = restrict2\<cdot>((daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd2\<cdot>srt2)) aut2 s2)\<cdot>(input2, ln))"
  apply(insert eq_in eq_state len_eq) 
  apply(induction ln arbitrary: input1 input2 s1 s2 rule: lnat_ind)
    apply simp
   apply (simp add: restrict_bot)

  apply(subst dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(subst(2) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)

  apply(case_tac "shd1\<cdot>input1"; case_tac "shd2\<cdot>input2"; simp)
     apply (simp add: restrict_bot)

  using bot_iff apply force
  using bot_iff apply force

    apply(subst restrict1_split | subst restrict2_split)+
    apply(rule arg_cong2 [where f="\<lambda>a b. conc a\<cdot>b"])

     apply(rule trans_out)
      apply (simp add: eq_input2msg)
     apply simp
  using eq_input2msg eq_input_srt len_srt trans_state by auto
qed
  thus ?thesis 
    apply(subst da_add_lnat[symmetric])
    apply(subst(2) da_add_lnat[symmetric])
    by simp
qed







theorem no_effect_NDA:
      fixes aut1::"('state1::type,'msg1::type,'out1::{conc, pcpo}) automaton"
        and aut2::"('state2::type,'msg2::type,'out2::{conc, pcpo}) automaton"
  assumes trans_well_state:"\<And>state1 state2 msg1 msg2 nextState1 nextState2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
              nextState1 \<in> fst ` (autTransition\<cdot>aut1) state1 msg1 \<Longrightarrow> 
              nextState2 \<in> fst ` (autTransition\<cdot>aut2) state2 msg2 \<Longrightarrow> 
            eq_on_state nextState1 nextState2"
    and trans_well_out:"\<And>state1 state2 msg1 msg2 nextState1 out1 nextState2 out2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
              out1 \<in> snd ` (autTransition\<cdot>aut1) state1 msg1 \<Longrightarrow> 
              out2 \<in> snd ` (autTransition\<cdot>aut2) state2 msg2 \<Longrightarrow> 
            restrict1\<cdot>out1 = restrict2\<cdot>out2"

    and len_eq: "#input1 = #input2" 
    and eq_in: "eq_on_input input1 input2"
    and eq_state:"eq_on_state s1 s2" 

    and spf1: "spf1 \<in> stateSem (step_create\<cdot>shd1\<cdot>srt1) aut1 s1" 
    and spf2: "spf2 \<in> stateSem (step_create\<cdot>shd2\<cdot>srt2) aut2 s2"

shows "restrict1\<cdot>(spf1\<cdot>input1) = restrict2\<cdot>(spf2\<cdot>input2)" 
proof -
  obtain da1 f1 where spf1_def: "spf1 = daStateSem (step_create\<cdot>shd1\<cdot>srt1) da1 (s1,f1::'in1\<rightarrow>'out1)"
      and da1_in: "da1 \<in> nda2daset aut1"
    using nda2daset sorry
  obtain da2 f2 where spf2_def: "spf2 = daStateSem (step_create\<cdot>shd2\<cdot>srt2) da2 (s2,f2::'in2\<rightarrow>'out2)"
      and da2_in: "da2 \<in> nda2daset aut2"
    using nda2daset sorry

  have "restrict1\<cdot>((daStateSem (step_create\<cdot>shd1\<cdot>srt1) da1 (s1,f1))\<cdot>input1) 
     = restrict2\<cdot>((daStateSem (step_create\<cdot>shd2\<cdot>srt2) da2 (s2,f2))\<cdot>input2)"
  proof(rule no_effect_da [of "\<lambda>s1 s2. eq_on_state (fst s1) (fst s2)"])
    fix state1::"'state1\<times>('in1\<rightarrow>'out1)" and state2::"'state2\<times>('in2\<rightarrow>'out2)" and msg1::'msg1
        and msg2::'msg2 and nextState1::'state1 
        and out1::'out1 and nextState2::'state2 and out2::'out1
    assume "eq_on_msg msg1 msg2" and "eq_on_state (fst state1) (fst state2)"
    show "eq_on_state (fst (fst (dautTransition da1 state1 msg1))) 
                      (fst (fst (dautTransition da2 state2 msg2)))"
      apply(rule trans_well_state [of msg1 msg2 "fst state1"  "fst state2" ])
         apply (simp_all add: \<open>eq_on_msg msg1 msg2\<close> \<open>eq_on_state (fst state1) (fst state2)\<close>)
      using nda2da_trans[OF da1_in] nda2da_trans[OF da2_in] by (metis fst_apfst image_eqI)+
    show "restrict1\<cdot>(snd (dautTransition da1 state1 msg1)) = restrict2\<cdot>(snd (dautTransition da2 state2 msg2))"
      apply(rule trans_well_out [of msg1 msg2 "fst state1"  "fst state2" ])
         apply (simp_all add: \<open>eq_on_msg msg1 msg2\<close> \<open>eq_on_state (fst state1) (fst state2)\<close>)
      using nda2da_trans[OF da1_in] nda2da_trans[OF da2_in] by (metis snd_apfst image_eqI)+
  next
    show "#input1 = #input2" by (simp add: assms)
    show "eq_on_input input1 input2" by (simp add: assms)
    show "eq_on_state (fst (s1, f1)) (fst (s2, f2))" by (simp add: assms)
  qed
  thus ?thesis 
    by (simp add: spf1_def spf2_def)
qed

theorem no_effect_NDA2:
      fixes aut1::"('state1::type,'msg1::type,'out::{conc, pcpo}) automaton"
        and aut2::"('state2::type,'msg2::type,'out::{conc, pcpo}) automaton"
  assumes trans_well_state:"\<And>state1 state2 msg1 msg2 nextState1 nextState2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
              nextState1 \<in> fst ` (autTransition\<cdot>aut1) state1 msg1 \<Longrightarrow> 
              nextState2 \<in> fst ` (autTransition\<cdot>aut2) state2 msg2 \<Longrightarrow> 
            eq_on_state nextState1 nextState2"
    and trans_well_out:"\<And>state1 state2 msg1 msg2 nextState1 out1 nextState2 out2. 
            eq_on_msg msg1 msg2 \<Longrightarrow> eq_on_state state1 state2 \<Longrightarrow>
              out1 \<in> snd ` (autTransition\<cdot>aut1) state1 msg1 \<Longrightarrow> 
              out2 \<in> snd ` (autTransition\<cdot>aut2) state2 msg2 \<Longrightarrow> 
            out1 = out2"

    and eq_state:"eq_on_state s1 s2" 


shows "{restrictInput} \<then> (stateSem (step_create\<cdot>shd1\<cdot>srt1) aut1 s1) 
       = stateSem (step_create\<cdot>shd2\<cdot>srt2) aut2 s2" 
  apply auto
  oops

end
end