theory EventAutomaton_AddChannel

imports eventcomponent.EventAutomaton 
        automaton.Nda2DaSet
        sps.SPS
        stream.StreamFilterWhile
        inc.Classes
        bundle.MsgWithChan

begin
default_sort type
(*
(* Kann man (später) verwenden, um Output-hinzuzüfgen *)
lift_definition restrictOutput::"('outOld \<rightarrow> 'outNew) \<Rightarrow> ('state::type, 'message::type, 'outOld::conc) automaton
  \<Rightarrow> ('state::type, 'message::type, 'outNew::conc) automaton" is
"\<lambda>f nda. (\<lambda>msg state. apsnd (Rep_cfun f) ` (autTransition\<cdot>nda) msg state, 
          apsnd (Rep_cfun f) ` autInitConfig\<cdot>nda)"
  by simp
lemma assumes "\<And>out1 out2. outfilter\<cdot>(out1 \<Zcat>\<Zcat> out2) = (outfilter\<cdot>out1) \<Zcat>\<Zcat> (outfilter\<cdot>out2)" 
  shows "sem step nda \<then> {outfilter} \<subseteq> sem step (restrictOutput outfilter nda)"
  apply(subst(2) sem_def, auto)
  oops
*)

lemma dastatesem_state_equiv:
  assumes "dautTransition da state1 msg = dautTransition da state2 msg"
  shows "daStateSem stream_step da state1\<cdot>(\<up>msg \<Zcat> input) 
       = daStateSem stream_step da state2\<cdot>(\<up>msg \<Zcat> input)"
  apply(subst dastatesem_step, subst(2) dastatesem_step)
  by(simp add: assms)



theorem eventaut_refine_add_channel:
  fixes ndaGreat::"('stateGreat::type, 'messageGreat::countable, 'out::conc) automaton"
     and ndaSmall::"('stateSmall::type, 'messageSmall::countable, 'out::conc) automaton"
     and f::"'stateGreat \<Rightarrow> 'stateSmall"
     and Abs_msg::"'messageGreat \<Rightarrow> 'messageSmall"
  assumes "apfst f ` autInitConfig\<cdot>ndaGreat \<subseteq> autInitConfig\<cdot>ndaSmall"
      and trans_ref:"\<And>msg state. msg\<in>S \<Longrightarrow> apfst f ` (autTransition\<cdot>ndaGreat) state msg 
                  \<subseteq> (autTransition\<cdot>ndaSmall) (f state) (Abs_msg msg)"
      and trans_new: "\<And>msg state nextState output. msg\<notin>S 
          \<Longrightarrow> (nextState,output) \<in> (autTransition\<cdot>ndaGreat) state msg
          \<Longrightarrow> output = \<bottom> \<and> f state = f nextState"
    shows "eSem ndaGreat \<subseteq> spsComplete ({sfilter S} \<then> {smap Abs_msg} \<then> eSem ndaSmall)"
proof (rule spscomplete_belowI)
  fix spfGreat::"'messageGreat stream \<rightarrow> 'out"
    and input ::"'messageGreat stream"
  assume as: "spfGreat \<in>  eSem ndaGreat"
  obtain daGreat::"('stateGreat\<times>('messageGreat stream\<rightarrow>'out), 'messageGreat, 'out) dAutomaton" 
    where dagreat_in: "daGreat \<in> nda2daset ndaGreat" 
      and spf2da: "spfGreat = daSem stream_step daGreat"
    apply(insert as, simp add: eSem_def) 
    apply(subst(asm) nda2daset [where conv="sup'"])
      apply(auto)[3] 
    using stream_step_eps streamind by blast
  have dagreat_new_msg_out:"\<And> msgGreat s spf.  msgGreat \<notin> S \<Longrightarrow>snd (dautTransition daGreat (s, spf) msgGreat) = \<bottom>"
    using dagreat_in trans_new by (metis nda2da_trans tuple_to_apfst)
  have dagreat_new_state: "\<And> msgGreat s spf.  msgGreat \<notin> S \<Longrightarrow> f (fst (fst (dautTransition daGreat (s, spf) msgGreat))) = f s"
    using dagreat_in trans_new by (metis fst_conv nda2da_trans tuple_to_apfst)
  let ?createNextSmallState = "\<lambda>(nextGreatState,nextGreatSPF) input. (f nextGreatState, nextGreatSPF, nextGreatState, input)"
   obtain daSmall::"('stateSmall\<times>('messageGreat stream\<rightarrow>'out) \<times> 'stateGreat \<times> 'messageGreat stream, 'messageSmall, 'out) dAutomaton" where 
      dasmall_def: "daSmall = (| dautTransition = (\<lambda> (stateSmall,spf, stateGreat, input) msgSmall. 
              if ((#(stakewhile (\<lambda>x. x\<notin>S)\<cdot>input) = \<infinity>) \<or> (S \<ominus> input) = \<bottom> 
                    \<or>(Abs_msg (shd (S \<ominus> input)) \<noteq>  msgSmall) \<or> stateSmall\<noteq>f stateGreat) 
                then apfst (\<lambda>nextStateSmall.(nextStateSmall, \<bottom>, undefined,\<bottom>)) (SOME x. x\<in>(autTransition\<cdot>ndaSmall) stateSmall msgSmall)
                else let ((nextStateGreat, nextSPF), output) = (multTransitionsInOne daGreat (stateGreat,spf) 
                              ((s2list(stakewhile (\<lambda>x. x\<notin>S)\<cdot>input)) @ ([shd (sdropwhile (\<lambda>x. x\<notin>S)\<cdot>input)]))) in
                  ((f nextStateGreat, nextSPF, nextStateGreat, srt\<cdot>(sdropwhile (\<lambda>x. x\<notin>S)\<cdot>input)), output)),
                 dautInitConfig = apfst (\<lambda>(s,spf). (f s, spf, s, input))  (dautInitConfig daGreat) |)"
     by simp

   have h1:"\<And>input s spf msgGreat. msgGreat\<notin>S \<Longrightarrow> 
    daStateSem (step_lnat_add\<cdot>stream_step) daSmall (f s, spf, s, \<up>msgGreat \<Zcat> input)
      \<cdot>(smap Abs_msg\<cdot>(S \<ominus> input), \<infinity>)
  = daStateSem (step_lnat_add\<cdot>stream_step) daSmall (?createNextSmallState (fst (dautTransition daGreat (s, spf) msgGreat)) input)
      \<cdot>(smap Abs_msg\<cdot>(S \<ominus> input), \<infinity>)" 
     apply(simp add: da_add_lnat)
     apply(case_tac "smap Abs_msg\<cdot>(S \<ominus> input)"; (simp add: case_prod_beta)?)
     apply(rule dastatesem_state_equiv)

     apply(auto simp add: dasmall_def case_prod_beta)[1]
          apply(rule prod_eqI, auto simp add: dagreat_new_state)
        apply(subst s2list_conc, metis inf_less_eq leI, simp)+
     by (simp add: dagreat_new_msg_out)
   have eq1: "\<And> ln. \<forall>s spf input. daStateSem (step_lnat_add\<cdot>stream_step) daGreat (s, spf)\<cdot>(input,ln) 
           \<sqsubseteq> (daStateSem (step_lnat_add\<cdot>stream_step) daSmall)(f s, spf, s, input)\<cdot>(smap Abs_msg\<cdot>(S \<ominus> input), \<infinity>)"
     apply(induct_tac ln; simp?)
     apply (rule allI)+
     apply(subst dastatesem_step, simp)
     apply(case_tac "input"; simp add: case_prod_beta)
     apply(rename_tac msgGreat linput)
     apply(case_tac "msgGreat \<in>S"; simp)
      apply(subst(2) dastatesem_step, subst fold_inf[symmetric], subst step_lnat_add_lnsuc)
      apply (simp add: case_prod_beta)
      apply(rule conc_belowI)
       apply(subst dasmall_def, simp add: case_prod_beta)
      apply(subst(2) dasmall_def, simp add: case_prod_beta)
      apply (metis prod.exhaust_sel)
     apply(simp add: dagreat_new_msg_out)

     apply(subst h1, auto simp add: case_prod_beta)
     by (metis prod.exhaust_sel)

   have eq2:"\<And>ln. \<forall>s spf input. daStateSem (step_lnat_add\<cdot>stream_step) daSmall (f s, spf, s, input)\<cdot>(smap Abs_msg\<cdot>(S \<ominus> input), ln) 
           \<sqsubseteq> (daStateSem (stream_step) daGreat (s,spf)\<cdot>(input))"
     apply(induct_tac ln; simp?)
     apply (rule allI)+
     apply(case_tac "(S \<ominus>input)"; simp add: case_prod_beta)
     apply(subst dastatesem_step, simp add: case_prod_beta)
     apply(subst(4) filtered_stream_step [where S="S"], simp)
     apply(subst(5) s2list_id[symmetric]; simp)
      defer
      apply(subst assoc_sconc[symmetric])
      apply(subst s2list_conc3)
        apply(rule stakewhile_finite, simp)
       apply simp

       apply(subst dastatesem_x_steps, simp add: Let_def case_prod_beta)
       apply(rule conc_belowI)

        apply(subst dasmall_def, auto simp add: case_prod_beta)
         defer 
         apply(subst shd_dropwhile;simp)

        apply(subst(2) dasmall_def, auto simp add: case_prod_beta)
         defer
         apply(subst shd_dropwhile;simp)+
         apply(subgoal_tac "sa =  S \<ominus> (srt\<cdot>(sdropwhile (\<lambda>x::'messageGreat. x \<notin> S)\<cdot>input))", simp del: sfilter_srtdwl3)
          apply (metis prod.exhaust_sel)
        apply simp
       apply(rule stakewhile_finite, simp)

     by (metis(mono_tags) stakewhile_finite mem_Collect_eq sconc_fst_inf sconc_neq_h sfilter_resl2 strict_sfilter)+

   have final1: "daSem stream_step daSmall\<cdot>(smap Abs_msg\<cdot>(S \<ominus> input)) 
           = (daSem stream_step daGreat\<cdot>(input))"
     apply(simp add: daSem_def case_prod_beta)+
     apply(rule arg_cong2 [where f="\<lambda>a b. a\<Zcat>\<Zcat>b"])

      apply(subst dasmall_def, simp add: case_prod_beta)

     apply(subst(1) da_add_lnat[symmetric], subst(2) da_add_lnat[symmetric])
     apply(rule below_antisym)

      apply(subst(2) dasmall_def, subst(2) da_add_lnat, simp add: case_prod_beta)
      apply (metis eq2 prod.collapse)

     apply(subst(2) dasmall_def, simp add: case_prod_beta)
     by (metis eq1 prod.collapse)

   have h4: "\<And>ls . \<forall> spf stateGreat. set ls \<inter> S = {} \<longrightarrow>
       (apfst (\<lambda>x. f (fst x)) (multTransitionsInOne daGreat (stateGreat, spf) ls))
                         = ((f stateGreat), \<bottom>)"
     apply(induct_tac "ls"; simp?)
     apply(intro allI impI, auto)
      apply (metis Pair_equalI dagreat_new_state fst_apfst fst_conv)
     by (metis Pair_equalI botconc1 dagreat_new_msg_out snd_apfst snd_conv)
   have h5: "\<And>input. S \<ominus> input \<noteq> \<epsilon> \<Longrightarrow> set (s2list (stakewhile (\<lambda>x. x \<notin> S)\<cdot>input)) \<inter> S = {}"
     apply(subst set2svalues)
      apply (simp add: stakewhile_finite)
     by fastforce
   hence h6: "\<And>spf stateGreat input. S \<ominus> input \<noteq> \<epsilon> \<Longrightarrow>
      f (fst (fst (multTransitionsInOne daGreat (stateGreat, spf)
          (s2list (stakewhile (\<lambda>x. x \<notin> S)\<cdot>input))))) = (f stateGreat)"
     using h4 h5 by (auto simp add: apfst_def map_prod_def case_prod_beta)
   have h7: "\<And>spf stateGreat input. S \<ominus> input \<noteq> \<epsilon> \<Longrightarrow>
      ((snd (multTransitionsInOne daGreat (stateGreat, spf)
          (s2list (stakewhile (\<lambda>x. x \<notin> S)\<cdot>input))))) = \<bottom>"
     using h4 h5 by (auto simp add: apfst_def map_prod_def case_prod_beta)     


   have h8:"\<And>state stateSmall spf msg.  msg \<in> S \<Longrightarrow> f (fst state) = stateSmall \<Longrightarrow>
      (f (fst (fst (dautTransition daGreat (state) msg))),
        snd (dautTransition daGreat (state) msg))
       \<in> (autTransition\<cdot>ndaSmall) stateSmall (Abs_msg msg)"
     using trans_ref case_prod_beta 
     by (metis (no_types, lifting) apfst_conv dagreat_in nda2da_trans rev_image_eqI subsetD tuple_to_apfst)
   have final2: "daSmall \<in> nda2daset ndaSmall"
     apply(rule nda2daset_in)
      apply( auto simp add: dasmall_def apfst_compose o_def id_def[symmetric])[2]
         apply(rule someI_ex, metis neq_emptyD auttrans_nempty)
        apply(rule someI_ex, metis neq_emptyD auttrans_nempty)
        apply(rule someI_ex, metis neq_emptyD auttrans_nempty)
       apply(rule someI_ex, metis neq_emptyD auttrans_nempty)
      apply(simp only: case_prod_beta')
     defer
     apply(simp add: case_prod_beta) 
     apply (metis (no_types, lifting) apfst_conv assms(1) dagreat_in image_iff nda2da_init prod.collapse subset_eq)

     apply(subst shd_dropwhile;simp?)+
     apply(rename_tac input)
      apply(subst multtransition_split, simp add: Let_def case_prod_beta)+

     apply(simp add: h7 case_prod_beta)
     apply(rule h8)
     apply (simp add: sfilter_ne_resup)
     by (simp add: h6)

  show "\<exists>spf2\<in>{sfilter S} \<then> {smap Abs_msg} \<then> eSem ndaSmall. spfGreat\<cdot>input = spf2\<cdot>input"
    apply (auto simp add: spf2da seqcomp_image seqcomp_image2)[1]
    using final1 final2 by (metis eSem_def nda2daset_refine_sem)
qed





theorem eventaut_refine_add_channel_msg:
  fixes ndaRef::"('stateRef::type, 'csRef::{chan,countable} msgWithChan event, 'out::conc) automaton"
     and ndaOrig::"('stateOrig::type, 'csOrig::{chan,countable} msgWithChan event, 'out::conc) automaton"
     and f::"'stateRef \<Rightarrow> 'stateOrig"
  assumes init_ref: "apfst f ` autInitConfig\<cdot>ndaRef \<subseteq> autInitConfig\<cdot>ndaOrig"
      and trans_ref_msg:"\<And>msg state. Rep(getChannel msg) \<in> chDom TYPE('csOrig) \<Longrightarrow> apfst f ` (autTransition\<cdot>ndaRef) state (EventMsg msg) 
                  \<subseteq> (autTransition\<cdot>ndaOrig) (f state) (EventMsg (ewcTypeCast msg))"
      and trans_ref_tick:"\<And>state.  apfst f ` (autTransition\<cdot>ndaRef) state Tick 
                  \<subseteq> (autTransition\<cdot>ndaOrig) (f state) Tick"
      and trans_new: "\<And>msg state nextState output. Rep(getChannel msg) \<notin> chDom TYPE('csOrig) 
          \<Longrightarrow> (nextState,output) \<in> (autTransition\<cdot>ndaRef) state (EventMsg msg)
          \<Longrightarrow> output = \<bottom> \<and> f state = f nextState"
    shows "eSem ndaRef \<subseteq> spsComplete ({ewcFiltercast} \<then> (eSem ndaOrig))"
proof -
  have "eSem ndaRef \<subseteq> spsComplete ({efilter (\<lambda>msg. Rep (getChannel msg) \<in> chDom TYPE('csOrig))} 
                            \<then> {emap (ewcTypeCast)} \<then> eSem ndaOrig)"
    unfolding efilter_def emap_def
    apply(rule eventaut_refine_add_channel [where f=f])
    using init_ref apply fastforce
     apply(case_tac msg; simp add: trans_ref_msg trans_ref_tick; fail)
    by(case_tac msg; simp add: trans_new; fail)
  thus ?thesis apply(simp add: ewcFiltercast_def)
    by (simp add: assoc_oo image_image seqcomp_image)
qed


end