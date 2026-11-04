theory AddChannel

imports automaton.Nda2DaSet

begin





theorem add_channel_aut:
  fixes autGreat::"('stateGreat::type,'great::type,'out::{conc}) automaton"
      and autSmall::"('stateSmall::type,'small::type,'out::{conc}) automaton"  
      and rep_msg::"'great \<Rightarrow> 'small"
      and f::"'stateGreat \<Rightarrow> 'stateSmall"
    assumes trans_ref: "\<And>stateGreat msg. apfst f ` ((autTransition\<cdot>autGreat) stateGreat msg) 
                                \<subseteq> (autTransition\<cdot>autSmall) (f stateGreat) (rep_msg msg)"
        and init_ref: "apfst f `(autInitConfig\<cdot>autGreat) \<subseteq> (autInitConfig\<cdot>autSmall)"
        and rep_surj: "surj (rep_msg)"
        and f_surj: "surj f"

        and spfgreat_in: "(spfGreat::('greatInput::{cpo,conc,len} \<rightarrow> 'out)) \<in>sem (step_create\<cdot>ghd\<cdot>grt) autGreat"

      and ghd: "\<And>msg input. ghd\<cdot>((convGreat msg)\<Zcat>\<Zcat>input) = Def msg"
      and grt: "\<And>msg input. grt\<cdot>((convGreat msg)\<Zcat>\<Zcat>input) = input"
      and case_input:"\<And>x P. \<lbrakk>#x = 0 \<Longrightarrow> P; \<And>msg input. x = (convGreat msg)\<Zcat>\<Zcat>input \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"

      and len_rep_input:"#(rep_input\<cdot>input) = #input"
      and len_rep_input_step:
        "\<And>input msg. #(rep_input\<cdot>(convGreat msg\<Zcat>\<Zcat>input)) = #(convGreat msg\<Zcat>\<Zcat>input) \<Longrightarrow> #(rep_input\<cdot>input) = #input"
      and ghd_0: "\<And>input. #input = 0 \<Longrightarrow> ghd\<cdot>input = \<bottom>"
      and stepSmall_0: "\<And>input f. #input = 0 \<Longrightarrow> stepSmall\<cdot>f\<cdot>input = \<bottom>"
      and stepSmall_step: "\<And>f msg input. stepSmall\<cdot>f\<cdot>(rep_input\<cdot>((convGreat msg)\<Zcat>\<Zcat>input))
                                  = f (rep_msg msg)\<cdot>(rep_input\<cdot>input)"
     and input_induction: "\<And>s P. adm P \<Longrightarrow> (\<And>xs. (ghd\<cdot>xs = \<bottom>) \<Longrightarrow> P xs) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (convGreat x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"

shows "\<exists>(spfSmall::('smallInput::{cpo,len} \<rightarrow> 'out)) \<in>sem stepSmall autSmall. spfGreat\<cdot>input = spfSmall\<cdot>(rep_input\<cdot>input)"
proof -
  obtain daGreat::"('stateGreat\<times>('greatInput\<rightarrow>'out), 'great, 'out) dAutomaton" 
    where dagreat_in: "daGreat \<in> nda2daset autGreat" and spf2da: "spfGreat = daSem (step_create\<cdot>ghd\<cdot>grt) daGreat"
    apply(insert spfgreat_in) 
    apply(subst(asm) nda2daset [where conv="convGreat"])
      apply(simp add: step_create_insert ghd grt)+
     apply(rule input_induction; simp)
    by blast
  have trans_ref: "\<And>s spf msg.  apfst (\<lambda>x. f (fst x)) (dautTransition daGreat (s, spf) msg)
       \<in> (autTransition\<cdot>autSmall) (f s) (rep_msg msg)"
    using dagreat_in f_surj nda2da_trans by (smt(verit) apfst_conv fst_conv image_subset_iff surj_pair trans_ref)

   obtain daSmall::"('stateSmall\<times>('greatInput\<rightarrow>'out)\<times>'greatInput\<times>'stateGreat, 'small, 'out) dAutomaton" where 
      dasmall_def: "daSmall = (| dautTransition = (\<lambda> (stateSmall,spf,inputGreat,stateGreat) msgSmall::'small.  
            let usedMsgGreat = case (ghd\<cdot>inputGreat) of Def msgGreat \<Rightarrow> 
                        (if rep_msg msgGreat = msgSmall then msgGreat else ((inv rep_msg) msgSmall)) 
                        | _ \<Rightarrow> ((inv rep_msg) msgSmall);
                usedStateGreat = if (f stateGreat) = stateSmall then stateGreat else ((inv f) stateSmall) in
                  apfst (\<lambda>(s,spf). (f s, spf, grt\<cdot>inputGreat, s))
                           (dautTransition daGreat (usedStateGreat, spf) usedMsgGreat)),
                 dautInitConfig = apfst (\<lambda>(s,spf). (f s, spf, input, s)) 
                                       (dautInitConfig daGreat) |)"
      by simp
    have da3_in: "daSmall \<in> nda2daset autSmall"
      apply(rule nda2daset_in; simp add: dasmall_def Let_def)
       apply(case_tac other, simp, rename_tac spfGreat greatInput stateGreat)
       apply(case_tac "ghd\<cdot>greatInput"; auto)
       apply(auto simp add: apfst_compose o_def case_prod_beta)[7]
      using rep_surj f_surj trans_ref  apply (smt UNIV_I f_inv_into_f)+
      using nda2da_init apfst_conv fst_conv image_subset_iff surj_pair by (smt(verit) dagreat_in init_ref)

    have dastate_eq: "\<And>stateSmall spf stateGreat. f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_create\<cdot>ghd\<cdot>grt) daGreat (stateGreat,spf))\<cdot>input 
      = (daStateSem stepSmall daSmall (stateSmall, spf, input, stateGreat))\<cdot>(rep_input\<cdot>input)" 
    proof - 
      fix stateSmall spf stateGreat 
      have h1: "\<And> ln. f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_lnat_add\<cdot>(step_create\<cdot>ghd\<cdot>grt)) daGreat (stateGreat,spf))\<cdot>(input,ln)
      = (daStateSem (step_lnat_add\<cdot>stepSmall) daSmall (stateSmall, spf, input, stateGreat))\<cdot>(rep_input\<cdot>input, ln)"
      proof - fix ln show "f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_lnat_add\<cdot>(step_create\<cdot>ghd\<cdot>grt)) daGreat (stateGreat,spf))\<cdot>(input,ln)
      = (daStateSem (step_lnat_add\<cdot>stepSmall) daSmall (stateSmall, spf, input, stateGreat))\<cdot>(rep_input\<cdot>input, ln)"
          apply(insert len_rep_input)
          apply(induction ln arbitrary: input stateSmall spf stateGreat)
          apply(intro adm_all adm_imp)+
           apply simp+
        apply(case_tac input rule: case_input)
        apply simp?
           apply (subst dastatesem_step, subst (2) dastatesem_step; simp add: case_prod_beta)
           apply(simp add: step_create_insert ghd_0)
           apply(rule stepSmall_0, simp)

           apply (subst dastatesem_step, subst (2) dastatesem_step; simp add: case_prod_beta)
          apply(subst step_create_insert3, simp add: ghd)
          apply (simp add: stepSmall_step)

         apply(rule arg_cong2 [where f="\<lambda>x. (Rep_cfun (conc x))"])
           apply(subst dasmall_def, simp add: case_prod_beta ghd)
          apply(subst (2)dasmall_def, simp add: case_prod_beta' grt ghd)
          using len_rep_input_step by (metis prod.collapse)
      qed
      thus "f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_create\<cdot>ghd\<cdot>grt) daGreat (stateGreat,spf))\<cdot>input 
      = (daStateSem stepSmall daSmall (stateSmall, spf, input, stateGreat))\<cdot>(rep_input\<cdot>input)"
         apply(rule da_lnat2eq )
        .
    qed
  have da_eq: "(daSem (step_create\<cdot>ghd\<cdot>grt) daGreat)\<cdot>input 
      = (daSem stepSmall daSmall)\<cdot>(rep_input\<cdot>input)"
    apply(simp add: daSem_def case_prod_beta)
    apply(rule arg_cong2 [where f="\<lambda>x. (Rep_cfun (conc x))"])
     apply(simp add: dasmall_def)
    apply(subst (2) dasmall_def, simp add: case_prod_beta)
    by(subst dastate_eq[symmetric]; simp)

  have da_in: "daSem stepSmall daSmall \<in> sem stepSmall autSmall"
    using da3_in  by (simp add: nda2daset_refine_sem)
  show "?thesis" 
    apply(rule bexI [where x="(daSem stepSmall daSmall)"])
    using da_in da_eq using spf2da apply blast+
    done
qed

end