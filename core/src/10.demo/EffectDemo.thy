theory EffectDemo
  imports stream.Stream automaton_testing.Effect  
      automaton.RefinementSignature stream.StreamAutomaton
    sps.SPS
begin

lemma dastatesem_add_channel:
  fixes da'::"('state'::type,'msg'::countable,'out::{conc, pcpo}) dAutomaton"
    and da ::"('state::type,'msg::countable,'out::{conc, pcpo}) dAutomaton" 
  assumes hd_bot: "\<And>input. mhd'\<cdot>input = \<bottom> \<longleftrightarrow> mhd\<cdot>(rep\<cdot>input) = \<bottom>"
        and "\<And>input. mrt\<cdot>(rep\<cdot>input) = rep\<cdot>(mrt'\<cdot>input)"
      and trans: "\<And>input msg' msg s. mhd'\<cdot>(input) = Def msg' \<Longrightarrow> mhd\<cdot>(rep\<cdot>input) = Def msg 
                \<Longrightarrow>  (dautTransition da' (f s) msg') = apfst f (dautTransition da s msg)"

  shows "daStateSem (step_create\<cdot>mhd'\<cdot>mrt') da' (f s')\<cdot>input 
       = daStateSem (step_create\<cdot>mhd\<cdot>mrt) da s'\<cdot>(rep\<cdot>input)"
proof -
  {
    fix ln
    have "daStateSem (step_lnat_add\<cdot>(step_create\<cdot>mhd'\<cdot>mrt')) da' (f s')\<cdot>(input ,ln)
        = daStateSem (step_lnat_add\<cdot>(step_create\<cdot>mhd\<cdot>mrt))   da (s')\<cdot>(rep\<cdot>input, ln)"
      apply(induction ln arbitrary: s' input rule: lnat_ind)
        apply simp+

      apply(subst dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
      apply(subst(2) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)

      apply(case_tac "mhd'\<cdot>input"; case_tac "mhd\<cdot>(rep\<cdot>input)")
      using hd_bot apply force+
      apply simp

      apply(rule arg_cong2 [where f="\<lambda>a b. conc a\<cdot>b"])
      
       apply(simp add: trans assms(2))+
      done
  }
  thus ?thesis 
    apply(subst da_add_lnat[symmetric])
    apply(subst (2) da_add_lnat[symmetric])
    by auto
qed

lemma cont_abslift[cont2cont]: "cont Abs_lift"
  by (simp add: Abs_lift_inverse below_lift_def chfindom_monofun2cont monofunI)
lift_definition cAbs_lift::"'a discr u \<rightarrow> 'a lift" is "Abs_lift"
  by (simp add: Abs_lift_inverse below_lift_def chfindom_monofun2cont monofunI cfun_def)

lemma stream_step2create: "stream_step = step_create\<cdot>(cAbs_lift oo lshd)\<cdot>srt"
  apply(intro cfun_eqI, rename_tac f input)
  apply(induct_tac input)
    apply simp+
   apply(simp add: step_create_insert cAbs_lift.rep_eq)
   apply (metis flift1_strict inst_lift_pcpo)

  apply (subst step_create_insert2)
   apply(simp add: cAbs_lift.rep_eq Def_def)
  by simp

lemma dastatesem_add_channel_SORRY:
  fixes da'::"('state'::type,'msg'::countable,'out::{conc, pcpo}) dAutomaton"
    and da ::"('state::type,'msg::countable,'out::{conc, pcpo}) dAutomaton" 
  assumes hd_bot: "\<And>input. mhd'\<cdot>input = \<bottom> \<longleftrightarrow> mhd\<cdot>(rep\<cdot>input) = \<bottom>"
        and "\<And>input. mrt\<cdot>(rep\<cdot>input) = rep\<cdot>(mrt'\<cdot>input)"
      and trans: "\<And>input msg' msg s. mhd'\<cdot>(inv_rep\<cdot>input) = Def msg' \<Longrightarrow> mhd\<cdot>(input) = Def msg 
                \<Longrightarrow>  (dautTransition da' (f s) msg') = apfst f (dautTransition da s msg)"
      and init: "(dautInitConfig da') = apfst f (dautInitConfig da)"
      and "\<And>x. rep\<cdot>(inv_rep\<cdot>x) = x"
  shows "daSem (step_create\<cdot>mhd'\<cdot>mrt') da'\<cdot>input = daSem (step_create\<cdot>mhd\<cdot>mrt) da\<cdot>(rep\<cdot>input)"
  oops

lemma da_add_channel:
  fixes da'::"('state'::type,'msg'::countable,'out::{conc, pcpo}) dAutomaton"
      and da::"('state::type,'msg::countable,'out::{conc, pcpo}) dAutomaton"  
  assumes hd_bot: "\<And>input. mhd'\<cdot>input = \<bottom> \<longleftrightarrow> mhd\<cdot>(rep\<cdot>input) = \<bottom>"
              and "\<And>input. mrt\<cdot>(rep\<cdot>input) = rep\<cdot>(mrt'\<cdot>input)"
      and trans: "\<And>input msg' msg s'. mhd'\<cdot>input = Def msg' \<Longrightarrow> mhd\<cdot>(rep\<cdot>input) = Def msg 
                \<Longrightarrow>  (dautTransition da' (f s') msg') = apfst f (dautTransition da s' msg)"
      and init: "(dautInitConfig da') = apfst f (dautInitConfig da)"
    shows  "daSem (step_create\<cdot>mhd'\<cdot>mrt') da'\<cdot>input = daSem (step_create\<cdot>mhd\<cdot>mrt) da\<cdot>(rep\<cdot>input)"
  apply(simp add: daSem_def case_prod_beta)
  apply(rule arg_cong2 [where f="\<lambda>a b. conc a\<cdot>b"])
   apply(simp add: init)+
  apply(rule dastatesem_add_channel; (simp add: assms)?)
  done

lemma srt_smap: "srt\<cdot>(smap f\<cdot>input) = smap f\<cdot>(srt\<cdot>input)"
  by(induction input; simp)

lemma "surj rep \<Longrightarrow> rep o inv rep = id"
  using surj_iff by auto

lemma fixes f::"'small \<Rightarrow> 'great"
  assumes "inj f"
  shows "daSem step ` ((nda2daset nda)::(('state\<times>'small, 'msg, 'out::conc) dAutomaton set)) 
      \<subseteq>  daSem step ` ((nda2daset nda)::(('state\<times>'great, 'msg, 'out::conc) dAutomaton set))"
proof  
  fix spf
  assume as: "spf \<in> daSem step ` ((nda2daset nda)::(('state\<times>'small, 'msg, 'out::conc) dAutomaton set))"
  obtain da::"('state\<times>'small, 'msg, 'out::conc) dAutomaton" where
    da_in: "da \<in> nda2daset nda" and spf_def: "spf = daSem step da"
    using as by blast
  obtain da'::"('state\<times>'great, 'msg, 'out::conc) dAutomaton"  where da_def: 
    "da' = (| dautTransition = (\<lambda>(state,great) msg::'msg. apfst (apsnd f) 
                                                  (dautTransition da (state,(inv f) great) ( msg))),
                 dautInitConfig = apfst (apsnd f) 
                                                  (dautInitConfig da) |)"
    by simp
  have "daSem step da = daSem step da'"
    oops


lemma cfun_fun_surj: 
  assumes "inj (Rep_cfun (g::'b::cpo \<rightarrow> 'a::cpo))"
      and "\<And>x. inv_g\<cdot>(g\<cdot>x) = x"
  shows "surj (\<lambda>f::('a \<rightarrow> 'out::cpo). f oo g)"
      apply(rule surjI [where f="\<lambda>f. f oo inv_g"])
      by(simp add: oo_def assms)

lemma surj_cfuncomp_inj:"surj f \<Longrightarrow> inj (\<lambda>g. g o f)"
  apply(simp add: o_def)
  apply(intro injI fun_eqI)
  by (metis surj_def)


lemma cfun_fun_inj: 
  assumes "surj (Rep_cfun (g::'b::cpo \<rightarrow> 'a::cpo))"
  shows "inj (\<lambda>f::('a \<rightarrow> 'out::cpo). f oo g)"
    proof(intro injI cfun_eqI)
      fix x::"('a \<rightarrow> 'out)" and y::"('a \<rightarrow> 'out)" and input::'a
      assume as: "x oo g = ((y oo g))"
      obtain z where "g\<cdot>z = input" by (metis assms surjD)
      thus "x\<cdot>input = y\<cdot>input"
        by (metis as cfcomp2)
    qed




theorem add_channel_stream_aut:
  fixes autGreat::"('stateGreat::type,'great::countable,'out::{conc, pcpo}) automaton"
      and autSmall::"('stateSmall::type,'small::countable,'out::{conc, pcpo}) automaton"  
      and rep::"'great \<Rightarrow> 'small"
      and f::"'stateGreat \<Rightarrow> 'stateSmall"
    assumes trans_ref: "\<And>stateGreat msg. apfst f ` ((autTransition\<cdot>autGreat) stateGreat msg) 
                                \<subseteq> (autTransition\<cdot>autSmall) (f stateGreat) (rep msg)"
        and init_ref: "apfst f `(autInitConfig\<cdot>autGreat) \<subseteq> (autInitConfig\<cdot>autSmall)"
        and rep_surj: "surj rep"
        and f_surj: "surj f"

        and spfgreat_in: "spfGreat \<in>sem stream_step autGreat"
      shows "\<exists>spfSmall \<in>sem stream_step autSmall. spfGreat\<cdot>input = spfSmall\<cdot>(smap rep\<cdot>input)"
proof -
  obtain daGreat::"('stateGreat\<times>('great stream\<rightarrow>'out), 'great, 'out) dAutomaton" 
    where dagreat_in: "daGreat \<in> nda2daset autGreat" and spf2da: "spfGreat = daSem stream_step daGreat"
    apply(insert spfgreat_in) 
    apply(subst(asm) nda2daset [where conv="\<lambda>s. \<up>s"]; simp)
    using stream_step_eps streamind apply blast
    by blast

  have trans_ref: "\<And>s spf msg.  apfst (\<lambda>x. f (fst x)) (dautTransition daGreat (s, spf) msg)
       \<in> (autTransition\<cdot>autSmall) (f s) (rep msg)"
    using dagreat_in f_surj nda2da_trans by (smt(verit) apfst_conv fst_conv image_subset_iff surj_pair trans_ref)
  hence trans_ref_inv: "\<And>s spf msg.  apfst (\<lambda>x. f (fst x)) (dautTransition daGreat ((inv f) s, spf) ((inv rep) msg))
       \<in> (autTransition\<cdot>autSmall) (s) msg"
    using rep_surj f_surj  by (smt UNIV_I f_inv_into_f)
   obtain daSmall::"('stateSmall\<times>('great stream\<rightarrow>'out)\<times>'great stream\<times>'stateGreat, 'small, 'out) dAutomaton" where 
      dasmall_def: "daSmall = (| dautTransition = (\<lambda> (stateSmall,spf,inputGreat,stateGreat) msg::'small.  
                    if (inputGreat\<noteq>\<epsilon> \<and> rep(shd inputGreat) = msg \<and> f stateGreat = stateSmall) 
                     then apfst (\<lambda>(s,spf). (f s, spf, srt\<cdot>inputGreat, s))
                             (dautTransition daGreat (stateGreat, spf) (shd inputGreat))
                     else apfst (\<lambda>(s,spf). (f s, spf, \<bottom>, s)) 
                            (dautTransition daGreat ((inv f) stateSmall, spf) ((inv rep) msg))),
                 dautInitConfig = apfst (\<lambda>(s,spf). (f s, spf, input, s)) 
                                       (dautInitConfig daGreat) |)"
      by simp
    have da3_in: "daSmall \<in> nda2daset autSmall"
      apply(rule nda2daset_in; simp add: dasmall_def)
       apply(case_tac other, auto simp add: apfst_compose o_def case_prod_beta)
      using trans_ref trans_ref_inv apply simp+
      using nda2da_init apfst_conv fst_conv image_subset_iff surj_pair by (smt(verit) dagreat_in init_ref)
    have dastate_eq: "\<And>stateSmall spf stateGreat. f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem stream_step daGreat (stateGreat,spf))\<cdot>input 
      = (daStateSem stream_step daSmall (stateSmall, spf, input, stateGreat))\<cdot>(smap rep\<cdot>input)"
    proof - 
      fix stateSmall spf stateGreat 
      have h1: "\<And> ln. f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_lnat_add\<cdot>stream_step) daGreat (stateGreat,spf))\<cdot>(input,ln)
      = (daStateSem (step_lnat_add\<cdot>stream_step) daSmall (stateSmall, spf, input, stateGreat))\<cdot>(smap rep\<cdot>input, ln)"
      proof - fix ln show "f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem (step_lnat_add\<cdot>stream_step) daGreat (stateGreat,spf))\<cdot>(input,ln)
      = (daStateSem (step_lnat_add\<cdot>stream_step) daSmall (stateSmall, spf, input, stateGreat))\<cdot>(smap rep\<cdot>input, ln)"
        apply(induction ln arbitrary: input stateSmall spf stateGreat)
          apply(intro adm_all adm_imp)+
           apply simp+
        apply(case_tac input)
        apply simp+
         apply (subst dastatesem_step, subst (2) dastatesem_step; simp add: case_prod_beta)
         apply(rule arg_cong2 [where f="\<lambda>x. (Rep_cfun (conc x))"])
          apply(simp add: dasmall_def)
          apply(subst dasmall_def, simp add: case_prod_beta)
          by (metis prod.exhaust_sel)
      qed
      thus "f stateGreat = stateSmall \<Longrightarrow> 
        (daStateSem stream_step daGreat (stateGreat,spf))\<cdot>input 
      = (daStateSem stream_step daSmall (stateSmall, spf, input, stateGreat))\<cdot>(smap rep\<cdot>input)"
         apply(rule da_lnat2eq )
        .
    qed
  have da_eq: "(daSem stream_step daGreat)\<cdot>input 
      = (daSem stream_step daSmall)\<cdot>(smap rep\<cdot>input)"
    apply(simp add: daSem_def case_prod_beta)
    apply(rule arg_cong2 [where f="\<lambda>x. (Rep_cfun (conc x))"])
     apply(simp add: dasmall_def)
    apply(subst (2) dasmall_def, simp add: case_prod_beta)
    by(subst dastate_eq[symmetric]; simp)

  have da_in: "daSem stream_step daSmall \<in> sem stream_step autSmall"
    using da3_in  by (simp add: nda2daset_refine_sem)
  show "?thesis" 
    apply(rule bexI [where x="(daSem stream_step daSmall)"])
    using da_in da_eq using spf2da apply blast+
    done
qed



lemma "undefined \<subseteq> (\<lambda>spf. spf oo f) ` stateSem stream_step aut s"
  unfolding stateSem_def
  oops


lift_definition oldAut::"nat \<Rightarrow> (unit, nat , bool stream) automaton" is
"\<lambda>n. (\<lambda> s msg. if (msg < n) then {((), \<up>True)} else {((), \<up>True), ((), \<up>False)}, 
    {((), \<epsilon>)})"
  by auto

lift_definition newAut::"nat \<Rightarrow> (unit, nat\<times>bool , bool stream) automaton" is
"\<lambda>n. (\<lambda> s (msg_nat, msg_bool). if (msg_nat < n) then {((), \<up>True)} else 
      if (msg_nat < 2*n) then {((), \<up>msg_bool)} else {((), \<up>True), ((), \<up>False)}, 
    {((), \<epsilon>)})"
  by auto

thm sem_inoutref

lemma ora_hd: assumes "\<And>sb. #sb \<le> #(oracle\<cdot>sb)"
     shows "szip\<cdot>(\<up>a \<Zcat> sa)\<cdot>(oracle\<cdot>(\<up>a \<Zcat> sa)) = \<up>(a, shd (oracle\<cdot>(\<up>a))) \<Zcat> szip\<cdot>sa\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>a \<Zcat> sa)))"
  apply(cases "oracle\<cdot>(\<up>a \<Zcat> sa)"; simp)
  apply(insert assms [of "(\<up>a \<Zcat> sa)"], simp)
  apply(rule arg_cong2 [where f= "\<lambda>s. Rep_cfun (sconc s)"]; simp?)
  apply(subgoal_tac "\<up>a  \<sqsubseteq> \<up>a \<Zcat> sa")
   apply(subgoal_tac "oracle\<cdot>(\<up>a)\<noteq>\<epsilon> ")
    apply (metis below_shd monofun_cfun_arg shd1)
   apply(insert assms [of "(\<up>a)"], fastforce)
  by simp



lemma statesem_ref: "(\<lambda>s. ({(\<Lambda> sb . szip\<cdot>sb\<cdot>(f\<cdot>sb)) | f. \<forall>sb. #sb \<le>#(f\<cdot>sb)} \<then> (stateSem stream_step (newAut n) s)))
        \<le>  stateSem stream_step (oldAut n)" (is "?L \<le> _")
  unfolding stateSem_def
  apply(rule gfp_parallel_induct [where f="stateSem_step stream_step (newAut n)"
        and g="stateSem_step stream_step (oldAut n)"])
  unfolding stateSem_def[symmetric]
     apply auto
   defer
   apply(intro le_funI, auto )
proof -
  fix x a b M
  assume as1:"\<forall>m::(unit \<Rightarrow> ((nat \<times> bool) stream \<rightarrow> bool stream) set) \<times> (unit \<Rightarrow> (nat stream \<rightarrow> bool stream) set)\<in>M.
          (\<lambda>s::unit.
              {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
              fst m ())
          \<le> snd m 
        \<and>stateSem stream_step (newAut n) \<le> fst m \<and> stateSem stream_step (oldAut n) \<le> snd m"
       and as2:"x \<in> {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
            (\<Inter>x::(unit \<Rightarrow> ((nat \<times> bool) stream \<rightarrow> bool stream) set) \<times> (unit \<Rightarrow> (nat stream \<rightarrow> bool stream) set)\<in>M.
                fst x ())"
       and as3: "(a, b) \<in> M"
  have h1: " {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
              a ()\<le> b ()" using as1 as3 
    by (metis (mono_tags, lifting) fst_conv le_fun_def snd_conv)
  have "(\<Inter>x\<in>M. fst x ()) \<subseteq> a ()" using as3 by fastforce
  hence "{\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
            (\<Inter>x::(unit \<Rightarrow> ((nat \<times> bool) stream \<rightarrow> bool stream) set) \<times> (unit \<Rightarrow> (nat stream \<rightarrow> bool stream) set)\<in>M.
                fst x ())
  \<subseteq> {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
              a ()"  by (meson seqcomp_subset subset_refl)
  hence "x\<in>{\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
              a ()" using as2 by blast
  thus "x \<in> b ()" using h1 by blast
next
  fix x::"unit \<Rightarrow> ((nat \<times> bool) stream \<rightarrow> bool stream) set"
    and y::"unit \<Rightarrow> ((nat ) stream \<rightarrow> bool stream) set"
  assume as1:"(\<lambda>s::unit.
           {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then> x ())
       \<le> y"
  show "(\<lambda>s::unit.
           {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then>
           stateSem_step stream_step (newAut n) x ())
       \<le> stateSem_step stream_step (oldAut n) y"
    apply(intro le_funI, auto simp add: stateSem_step_def seqcomp_insert)
    apply(rename_tac f "oracle")
    apply(auto simp add: image_iff)
    apply(rule_tac x= "\<lambda>msg. \<Lambda> input. f (msg, shd (oracle\<cdot>(\<up>msg)))\<cdot>(szip\<cdot>input\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> input))))" in exI)
    apply auto
     defer
     apply(rule cfun_eqI)+
     apply(simp add: oo_def case_prod_beta)
     apply(rename_tac s, case_tac s; simp)
    apply(subgoal_tac "(szip\<cdot>(\<up>a \<Zcat> sa)\<cdot>(oracle\<cdot>(\<up>a \<Zcat> sa))) = \<up>(a, shd (oracle\<cdot>(\<up>a))) \<Zcat> szip\<cdot>sa\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>a \<Zcat> sa)))"; simp?)
     apply(rule arg_cong)
     apply(simp add: ora_hd)
  proof - 
    fix f::"nat \<times> bool \<Rightarrow> (nat \<times> bool) stream \<rightarrow> bool stream"
      and "oracle"::"nat stream \<rightarrow> bool stream"
      and msg::nat
    assume as11:"\<forall>(a::nat) b::bool.
          \<exists>output::bool stream.
             ((), output) \<in> (autTransition\<cdot>(newAut n)) () (a, b) \<and>
             (\<exists>nextSPF::(nat \<times> bool) stream \<rightarrow> bool stream.
                 nextSPF \<in> x () \<and> (\<forall>input::(nat \<times> bool) stream. f (a, b)\<cdot>input = output \<Zcat> nextSPF\<cdot>input))"
      and as22: "\<forall>sb::nat stream. #sb \<le> #(oracle\<cdot>sb)"
    obtain out nextSPF where in_trans:"((), out) \<in> (autTransition\<cdot>(newAut n)) () (msg, shd (oracle\<cdot>(\<up>msg)))"
      and nextspf_in: "nextSPF \<in> x ()" and 
      input:"(\<forall>input::(nat \<times> bool) stream. f (msg, shd (oracle\<cdot>(\<up>msg)))\<cdot>input = out \<Zcat> nextSPF\<cdot>input)"
      using as11 by blast
    have h11: "(\<Lambda> (x::nat stream). nextSPF\<cdot>(szip\<cdot>x\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> x))))) 
      \<in> {\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then> x ()"
      apply(auto simp add: seqcomp_insert)
      apply(rule exI [where x="(\<Lambda> input. szip\<cdot>input\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> input))))"])
      apply(rule exI [where x="nextSPF"])
      apply (auto simp add: nextspf_in)
       apply(simp add: oo_def)
      apply(rule exI [where x="\<Lambda> input. (srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> input)))"], auto simp add: as22)
      by (smt as22 less_lnsuc lnsuc_lnle_emb slen_scons srt_decrements_length stream.sel_rews(2) trans_lnle)
      
    show "\<exists>output::bool stream.
          ((), output) \<in> (autTransition\<cdot>(oldAut n)) () msg \<and>
          (\<exists>nextSPF::nat stream \<rightarrow> bool stream.
              nextSPF \<in> y () \<and>
              (\<forall>input::nat stream.
                  f (msg, shd (oracle\<cdot>(\<up>msg)))\<cdot>(szip\<cdot>input\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> input)))) = output \<Zcat> nextSPF\<cdot>input))"
      apply(rule exI [where x= "out"], auto)
       apply(insert in_trans,auto simp add: autTransition.rep_eq newAut.rep_eq oldAut.rep_eq)
      apply (metis (full_types) Pair_inject insertE singletonD)?
      apply(rule exI [where x= "nextSPF oo (\<Lambda> input. szip\<cdot>input\<cdot>(srt\<cdot>(oracle\<cdot>(\<up>msg \<Zcat> input))))"], auto simp add: input)
      apply(simp add: oo_def) 
      apply(rule set_mp [where A="{\<Lambda> (sb::nat stream). szip\<cdot>sb\<cdot>(f\<cdot>sb) |f::nat stream \<rightarrow> bool stream. \<forall>sb::nat stream. #sb \<le> #(f\<cdot>sb)} \<then> x ()"])
       apply( intro h11  as1[THEN le_funD])+
      done
  qed
qed




theorem "sem stream_step (newAut n) \<subseteq> spsComplete({smap fst} \<then> (sem stream_step (oldAut n))) "
  apply(rule spscomplete_belowI, simp)
  apply(rule add_channel_stream_aut [where f=id and autGreat = "newAut n"])
      apply(auto simp add: autTransition.rep_eq autInitConfig.rep_eq newAut.rep_eq oldAut.rep_eq)
  by (metis(full_types) Pair_inject insertE singletonD)



abbreviation  "ssem\<equiv>sem stream_step"

theorem
 "{(\<Lambda> sb . szip\<cdot>sb\<cdot>(oracle\<cdot>sb)) | oracle. \<forall>sb. #sb \<le> #(oracle\<cdot>sb)} \<then> ssem  (newAut 50)
     \<subseteq>  sem stream_step (oldAut 50)"

  apply(auto simp add: sem_def autInitConfig.rep_eq newAut.rep_eq oldAut.rep_eq)
  using statesem_ref[THEN le_funD] 
  by blast


(*
corollary "sem stream_step (newAut n) \<subseteq> (\<lambda>spf. spf oo smap fst) ` sem stream_step (oldAut n)"
proof - 
  have  "{(\<Lambda> sb . szip\<cdot>sb\<cdot>something) | something. #something=\<infinity>} \<then> sem stream_step (newAut n) 
        \<subseteq>  sem stream_step (oldAut n)" (is "?L \<subseteq> ?R") sorry
  hence "(\<lambda>spf. spf oo smap fst) ` ?L \<subseteq> (\<lambda>spf. spf oo smap fst) ` ?R"
    by blast
  moreover have "sem stream_step (newAut n) \<subseteq> (\<lambda>spf. spf oo smap fst) ` ?L"
    apply auto
    apply(auto simp add: image_iff seqcomp_insert)
    sorry (* ... und hier ist das problem *)
  ultimately show ?thesis apply fastforce
    oops
*)







lemma 
  assumes "b1\<noteq>b2"
  shows "(autTransition\<cdot>(newAut 50)) () (n, b1) 
       \<inter> (autTransition\<cdot>(newAut 50)) () (n, b2) 
         \<noteq> {}"
  apply(simp add: autTransition.rep_eq newAut.rep_eq)
  nitpick[expect=genuine]
  oops



default_sort "{countable,pcpo}"
thm spsComplete_def


lemma fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" 
        and  spsOriginal::"('a stream \<rightarrow> 'out stream) set"

  assumes "spfWithNewChannel \<in> spsWithNewChannel"
  shows "\<exists>spfOriginal \<in> spsOriginal. 
            spfWithNewChannel\<cdot>input = spfOriginal\<cdot>(fst input)"
  oops


lemma fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" 
        and  spsOriginal::"('a stream \<rightarrow> 'out stream) set"

shows "spsWithNewChannel \<subseteq> spsComplete({cfst} \<then> spsOriginal)"
  apply(intro spscomplete_belowI)
  apply(simp )
  oops





















lemma fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" 
        and  spsOriginal::"('a stream \<rightarrow> 'out stream) set"

shows "spsWithNewChannel \<subseteq> {spfWithNewChannel. \<forall>input. \<exists>spfOriginal\<in>spsOriginal. 
                                                  spfWithNewChannel\<cdot>input = spfOriginal\<cdot>(fst input)}"
  oops


















definition isRefinementAfterChannelAdding::"('inputWithNewChannel \<rightarrow> 'output) set \<Rightarrow> 
                                            ('inputOriginal \<rightarrow> 'output) set \<Rightarrow>
                                            ('inputWithNewChannel \<rightarrow> 'inputOriginal) set \<Rightarrow> 
                                            bool" where
"isRefinementAfterChannelAdding spsWithNewChannel spsOriginal rep = (spsWithNewChannel \<subseteq> spsComplete (rep \<then> spsOriginal))"



lemma "(spsWithNewChannel \<subseteq> {spfWithNewChannel. \<forall>input. \<exists>spfOriginal\<in>spsOriginal. spfWithNewChannel\<cdot>input = spfOriginal\<cdot>(fst input)})
      \<longleftrightarrow> isRefinementAfterChannelAdding spsWithNewChannel spsOriginal {cfst}"
  by(simp add: isRefinementAfterChannelAdding_def spsComplete_def)




lemma fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" 
        and  spsOriginal::"('a stream \<rightarrow> 'out stream) set"
      shows "spsWithNewChannel \<subseteq> \<Union>((\<lambda>spf. {(\<Lambda> (oldInput,newInput). spf\<cdot>oldInput) | oracle. True}) ` spsOriginal)"
  oops





lemma fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" 
        and  spsOriginal::"('a stream \<rightarrow> 'out stream) set"

shows "({spfWithNewChannel. \<exists>spfOriginal\<in>spsOriginal. \<forall>input. spfWithNewChannel\<cdot>input = spfOriginal\<cdot>(fst input)} 
     = {cfst} \<then> spsOriginal)"
  apply(auto simp add: oo_def image_def)
  apply(rule_tac x="spfOriginal" in bexI, auto)
  apply(intro cfun_eqI, simp)
  by force



lemma "\<not>\<Union>((\<lambda>spf. {b | b. \<forall>i. \<exists>j. spf\<cdot>i=b\<cdot>(i,j)}) ` {\<bottom>})
  \<subseteq> ((spsComplete ({cfst} \<then> {\<bottom>}))::((bool stream \<times> bool stream) \<rightarrow> bool stream) set)"
  apply(auto simp add: spsComplete_def)
proof -
  assume as: "{spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. spf\<cdot>(i, j) = \<epsilon>}
    \<subseteq> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>(a::bool stream) b::bool stream. spf\<cdot>(a, b) = \<epsilon>}"
  let ?spf = "((\<Lambda> (s1,s2) . (smap (\<lambda>(a,b). a\<and>b))\<cdot>(szip\<cdot>s1\<cdot>s2)))"
  have "?spf \<in> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. spf\<cdot>(i, j) = \<epsilon>}"
    by(auto, rule exI [where x="\<epsilon>"]; simp) 
  moreover have "?spf \<notin>{spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>(a::bool stream) b::bool stream. spf\<cdot>(a, b) = \<epsilon>}"
    apply auto
    apply(rule exI [where x="\<up>True"])+
    by simp
  ultimately show False
    using as by blast
qed

lemma "\<not>(spsComplete ({cfst} \<then> {ID,\<bottom>})
  \<subseteq> ((\<Union>((\<lambda>spf. {b | b. \<forall>i. \<exists>j. spf\<cdot>i=b\<cdot>(i,j)}) `  {ID,\<bottom>})) ::((bool stream \<times> bool stream) \<rightarrow> bool stream) set ))"
  apply(auto simp add: spsComplete_def)
proof -
  assume as: "{spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>(a::bool stream) b::bool stream. spf\<cdot>(a, b) = a \<or> spf\<cdot>(a, b) = \<epsilon>}
    \<subseteq> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. i = spf\<cdot>(i, j)} \<union>
       {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. spf\<cdot>(i, j) = \<epsilon>}"
  let ?spf = "(\<Lambda> (s1,s2). if srt\<cdot>s1 =\<bottom> then \<bottom> else s1)"
  have "Rep_cfun ?spf = (\<lambda>(s1,s2). if srt\<cdot>s1 =\<bottom> then \<bottom> else s1)"
    by(intro fun_eqI, rename_tac a, case_tac "a"; simp?)
    
  have "?spf \<in> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>(a::bool stream) b::bool stream. spf\<cdot>(a, b) = a \<or> spf\<cdot>(a, b) = \<epsilon>}"
    by(simp)
  moreover have"?spf \<notin> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. i = spf\<cdot>(i, j)}"
    apply simp
    apply(rule exI [where x="\<up>True"])+
    by simp
  moreover have "?spf \<notin> {spf::bool stream \<times> bool stream \<rightarrow> bool stream. \<forall>i::bool stream. \<exists>j::bool stream. spf\<cdot>(i, j) = \<epsilon>}"
    apply simp
    apply(rule exI [where x="<[True,False]>"])+
    by simp
  ultimately show False
    using as by blast
qed


lemma "({cfst} \<then> (UNIV ) ::((bool stream \<times> bool stream) \<rightarrow> (bool stream \<times> bool stream)) set )
         \<noteq> spsComplete ({cfst} \<then> (UNIV ))" 
  (is "?L \<noteq> _")
proof - 
  have "ID \<in> (spsComplete ({cfst} \<then> UNIV)::((bool stream \<times> bool stream) \<rightarrow> (bool stream \<times> bool stream)) set )"
    apply(auto simp add: spsIsComplete_def spsComplete_def oo_def)
    by(rule_tac x = "\<Lambda> a. (a,b)" in exI; simp)
  moreover have "ID \<notin> ({cfst} \<then> (UNIV ::((bool stream) \<rightarrow> (bool stream \<times> bool stream)) set ))"
  proof(auto simp add: oo_def)
    fix x::"(bool stream) \<rightarrow>  (bool stream \<times> bool stream)"
    assume id_def: "ID = (\<Lambda> (xa). x\<cdot>(fst xa))"
    have "x\<cdot>\<epsilon>=(\<epsilon>,\<epsilon>)"
      apply(subgoal_tac "ID\<cdot>(\<epsilon>,\<epsilon>) = (\<epsilon>,\<epsilon>)")
       apply(subst(asm) id_def, simp)
      by simp
    moreover have "x\<cdot>\<epsilon>=(\<epsilon>,\<up>True)"
      apply(subgoal_tac "ID\<cdot>(\<epsilon>,\<up>True) = (\<epsilon>,\<up>True)")
       apply(subst(asm) id_def, simp)
      by simp  
    ultimately show False
      by auto
  qed
  ultimately show "?L \<noteq> spsComplete ?L"
    apply simp by blast
qed

context 
begin
private lemma h1: "({cfst} \<then> spsOriginal) \<subseteq> \<Union>((\<lambda>spf. {b | b. \<forall>i. \<forall>j. spf\<cdot>i=b\<cdot>(i,j)}) ` spsOriginal)"
   by(auto simp add: spsComplete_def  image_iff)

private lemma all_all_fst [simp]: "(\<lambda>spf. {b | b. \<forall>i. \<forall>j. spf\<cdot>i=b\<cdot>(i,j)}) = (\<lambda>spf . {spf oo cfst})"
  apply(intro fun_eqI, simp)
  apply auto
  by(intro cfun_eqI, auto)
  
private lemma h2:"\<Union>((\<lambda>spf. {b | b. \<forall>i. \<forall>j. spf\<cdot>i=b\<cdot>(i,j)}) ` spsOriginal)
      \<subseteq> ({cfst} \<then> spsOriginal)"
  apply(subst all_all_fst)
  by(auto simp add: spsComplete_def  image_iff)
  
theorem "\<Union>((\<lambda>spf. {b | b. \<forall>i. \<forall>j. spf\<cdot>i=b\<cdot>(i,j)}) ` spsOriginal)
      = ({cfst} \<then> spsOriginal)" 
  using h1 h2 by blast
end

lemma "spsComplete ({cfst} \<then> spsOriginal)
  = \<Union>((\<lambda>spf. {b | b. \<forall>i. \<exists>j. spf\<cdot>i=b\<cdot>(i,j)}) ` spsOriginal)"
  oops
  
  (*defer
   apply(rule spscomplete_belowI, simp add: seqcomp_image)
   apply auto[1] 
   apply(rename_tac spfOriginal)
  apply( rule_tac x="spfOriginal" in bexI; simp?) 
    (* SSt: Klappt nicht. Man muss "spf" in exI verwenden, und abhängig von der Eingabe ein "j" auswählen
            ... stetigkeit? *)
   defer

   apply(auto simp add: seqcomp_image spsComplete_def)
   apply(rename_tac spfNew)
  apply auto[1]

  oops
*)
  

definition f::"('a stream \<rightarrow> 'out stream) 
    \<Rightarrow> (('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" where
"f a = {b | b. \<forall>i. \<exists>j. a\<cdot>i=b\<cdot>(i,j)}" 

definition g::"(('a stream\<times> 'b stream) \<rightarrow> 'out stream) set 
    \<Rightarrow> (('a stream) \<rightarrow> 'out stream) set" where
"g B = {a | a. \<forall>i. \<exists>j.\<exists>b\<in>B. a\<cdot>i=b\<cdot>(i,j)}"

definition F::"('a stream \<rightarrow> 'out stream) set
    \<Rightarrow> (('a stream \<times> 'b stream) \<rightarrow> 'out stream) set" where
"F B = \<Union>(f ` B)" 





lemma 
  fixes spsWithNewChannel::"(('a stream \<times> 'b stream) \<rightarrow> 'out stream) set"
    and spsOriginal::"('a stream \<rightarrow> 'out stream) set"
  shows "spsWithNewChannel \<subseteq> {spf | spf. \<forall>j. (#j = \<infinity> 
                                    \<longrightarrow> (\<exists>spfOriginal\<in>spsOriginal . \<forall>i. spf\<cdot>(i,j)=spfOriginal\<cdot>i))}"
  oops

lemma fixes spsOriginal::"('i stream \<rightarrow> 'out stream) set"
  shows  "{spf | spf. \<forall>j::'j stream. ( (\<exists>spfOriginal\<in>spsOriginal . \<forall>i. #i \<le>#j \<longrightarrow> spf\<cdot>(i,j)=spfOriginal\<cdot>i))}
  \<subseteq> spsComplete ({cfst} \<then> spsOriginal)"
proof(rule spscomplete_belowI, auto)
  fix spf::"'i stream \<times> 'j stream \<rightarrow> 'out stream"
    and i::"'i stream" 
    and j::"'j stream"
  assume as: "\<forall>j::'j stream. ( (\<exists>spfOriginal\<in>spsOriginal . \<forall>i. #i \<le>#j \<longrightarrow> spf\<cdot>(i,j)=spfOriginal\<cdot>i))"
  let ?jInf = "j \<Zcat>\<Zcat> ((\<up>(undefined))\<^sup>\<infinity>)"
  have "#?jInf = \<infinity>" apply simp
    by (metis s2sinftimes sconc_fst_empty shd1 sinftimes_unfold slen_sconc_snd_inf slen_sinftimes snNEqSinf sntimes_stake stream.take_strict strict_icycle) 
  from this obtain spfOriginal where "spfOriginal\<in>spsOriginal" and "\<forall>i::'i stream. spf\<cdot>(i, ?jInf) = spfOriginal\<cdot>i"
    using as apply auto 
    by (metis inf_ub)
  have "spf\<cdot>(i, ?jInf) = spf\<cdot>(i, j)"
    
    oops (*
  show "\<exists>spf2::'i stream \<rightarrow> 'out stream\<in>spsOriginal. spf\<cdot>(i, j) = spf2\<cdot>i"
*)

end