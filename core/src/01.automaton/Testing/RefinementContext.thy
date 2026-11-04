theory RefinementContext

imports automaton.Nda2DaSet SimpleComp automaton.Steps AutComp

begin
default_sort type

(*
lemma prod_conc_join: "(a \<Zcat>\<Zcat> as, b \<Zcat>\<Zcat> bs) = (a,b) \<Zcat>\<Zcat> (as, bs)"
  by (simp)
use "conc_prod_apply [symmetric]" instead
*)

lemma lnat_must_be_bot: assumes "(\<And>f::unit \<Rightarrow> lnat \<rightarrow> 'a::pcpo. step_lnat\<cdot>f\<cdot>ln = \<bottom>)"
  and ex_output: "\<exists>a::'a. a \<noteq> \<bottom>"
shows "ln = \<bottom>"
  apply(rule ccontr)
  apply(insert assms(1) [where f="\<lambda> _ . (\<Lambda> asd. SOME x. x\<noteq>\<bottom>)"], simp add: step_lnat_def)
  using assms(2) verit_sko_ex' by fastforce



theorem 
  fixes step :: "('msg \<Rightarrow> 'input::{conc} \<rightarrow> 'output::{conc,cpo}) \<rightarrow> 'input \<rightarrow> 'output" 
  assumes step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"
     and input_induction: "\<And>s P. adm P \<Longrightarrow> ((\<forall>f. step\<cdot>f\<cdot>s = \<bottom>) \<Longrightarrow> P s) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
   shows "sem step nda  = (\<lambda>da. daSem step da) ` ((nda2daset nda)::('state\<times>('input\<rightarrow>'output), 'msg, 'output) dAutomaton set)"
  oops
thm nda2daset

declare[[show_types]]
declare[[show_consts]]
declare[[show_sorts]](*
lemma fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
    and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  shows  "daStateSem step_lnat (da_comp (uncont whd) wrt (uncont shd) srt wda sda)(wout, sout, wstate, sstate)\<cdot>ln
    = (simpleComp_lnat2\<cdot>(daStateSem (step_lnat_add\<cdot>(step_prefix wout\<cdot>(step_create\<cdot>whd\<cdot>wrt))) sda sstate)
                        \<cdot>(daStateSem (step_lnat_add\<cdot>(step_prefix sout\<cdot>(step_create\<cdot>shd\<cdot>srt))) wda wstate))\<cdot>ln"
  apply(induction ln arbitrary: wout sout wstate sstate)
    apply simp

   apply simp
   apply(subst dastatesem_step, simp)
   apply(subst dastatesem_step, simp)
   apply(subst dastatesem_step, simp)

  apply(subst simplecomp_lnat2_unfold, simp)
  apply(subst dastatesem_step, simp add: case_prod_beta)
  apply(subst (2) dastatesem_step, simp add: case_prod_beta step_prefix_def)

  apply(subst step_lnat_bot)
  apply(subst inst_prod_pcpo)
  oops*)

  
lemma dastatesem_stuck: assumes "\<And>msg. dautTransition da state msg = (state, \<bottom>)" 
     and input_induction: "\<And>s P. adm P \<Longrightarrow> ((\<And>f. step\<cdot>f\<cdot>s = \<bottom>) \<Longrightarrow> P s) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (conv x \<Zcat>\<Zcat> xs)) \<Longrightarrow> P s"
     and step_unfold: "\<And>input f msg. step\<cdot>f\<cdot>((conv msg)\<Zcat>\<Zcat>input) = f msg\<cdot>input"   
   shows "daStateSem step da state\<cdot>input = \<bottom>"
  apply(induct_tac input rule: input_induction)
    apply simp
   apply(subst dastatesem_step, simp)
  by(subst dastatesem_step, simp add: case_prod_beta assms)


lemma step_unit2lnat: "daStateSem step_unit da state\<cdot>() = daStateSem step_lnat da state\<cdot>\<infinity>"
  oops

context
begin
private lemma help_1:"simpleComp\<cdot>(conc fout oo f)\<cdot>(conc gout oo g) \<sqsubseteq> 
      (gout,fout) \<Zcat>\<Zcat> (simpleComp\<cdot>(f oo conc gout)\<cdot>(g oo conc fout))"
  unfolding simpleComp_def
  apply simp
  apply(rule parallel_fix_ind [where P="\<lambda>a b. a \<sqsubseteq>  (gout,fout) \<Zcat>\<Zcat>  b"])
    apply auto[3]
  by (simp add: conc_prod_apply monofun_cfun_arg)

private lemma help_2:"(gout,fout) \<Zcat>\<Zcat> (simpleComp\<cdot>(f oo conc gout)\<cdot>(g oo conc fout))
        \<sqsubseteq> simpleComp\<cdot>(conc fout oo f)\<cdot>(conc gout oo g)"
  unfolding simpleComp_def
  apply(subst (2) fix_eq, simp)
  apply(subst conc_prod_apply [symmetric])+
  apply(rule monofun_cfun_arg)
  apply(rule fix_least_below)
  apply(subst beta_cfun, intro cont2cont)+
  apply(subst (5) fix_eq, simp add: conc_prod_apply)
  apply(subst (2) fix_eq, simp add: conc_prod_apply)
  done

theorem simpleComp_conc:"simpleComp\<cdot>(conc fout oo f)\<cdot>(conc gout oo g)
    = (gout,fout) \<Zcat>\<Zcat> (simpleComp\<cdot>(f oo conc gout)\<cdot>(g oo conc fout))"
  apply(rule below_antisym)
  by (simp add: help_1 help_2)+

lemma simpleComp_conc_1:"simpleComp\<cdot>f\<cdot>(conc gout oo g)
    = (gout,\<bottom>) \<Zcat>\<Zcat> (simpleComp\<cdot>(f oo conc gout)\<cdot>g)"
  apply(subst (1) conc_bot2[symmetric], subst (11) conc_bot1[symmetric])
  by(rule simpleComp_conc)

lemma simpleComp_conc_2:"simpleComp\<cdot>(conc fout oo f)\<cdot>g
    = (\<bottom>,fout) \<Zcat>\<Zcat> (simpleComp\<cdot>f\<cdot>(g oo conc fout))"
  apply(subst (5) conc_bot2[symmetric], subst (8) conc_bot1[symmetric])
  by(rule simpleComp_conc)

end

lemma lnat_step_induct: assumes "adm P" and "(\<And>f::unit \<Rightarrow> lnat \<rightarrow> 'a::pcpo. step_lnat\<cdot>f\<cdot>s = \<bottom> \<Longrightarrow> P s)"
  and "(\<And>xs::lnat. P xs \<Longrightarrow> P (lnsuc\<cdot>xs))"
   and ex_output: "\<exists>a::'a. a \<noteq> \<bottom>"
 shows " P s"
  oops

lemma fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
    and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  assumes "shd\<cdot>sout = \<bottom>" and  "whd\<cdot>wout = \<bottom>"
  and ex_output: "\<exists>a::('wout\<times>'sout). a \<noteq> \<bottom>"

shows "daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate) = \<bottom>"
  apply(rule cfun_eqI, simp)
  oops (*
  apply(subst step_unit2lnat)
  apply(rule dastatesem_stuck [where conv="\<lambda>_. lnsuc\<cdot>\<bottom>"])
   apply(auto simp add: da_comp_def Let_def case_prod_beta)
        apply(subst da_trans_one_def, simp add: uncont_def assms)+
  oops*)

lemma conc_prod_apply_l: 
  shows "(\<bottom>,s2) \<Zcat>\<Zcat> (s3,s4) = (s3, s2 \<Zcat>\<Zcat> s4)"
    and "(s1,\<bottom>) \<Zcat>\<Zcat> (s3,s4) = (s1 \<Zcat>\<Zcat> s3,  s4)"
  by(simp add: conc_prod_apply)+


lemma aut_comp_below_comp:
      fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
        and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
      and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"

  shows  "daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) 
    \<sqsubseteq> (\<lambda>(wout, sout, wstate, sstate) . \<Lambda> _ . simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout))"
  apply(subst daStateSem_def)
  apply(rule fix_least_below)
  apply(rule cfun_belowI | rule fun_belowI)+
  apply(simp add: case_prod_beta)
  apply(subst (2) simplecomp_unfold)
  apply(auto)[1]
   apply(auto simp add: da_comp_def Let_def case_prod_beta)[1]

  apply(rename_tac wout sout wstate sstate)
  apply(case_tac "shd\<cdot>sout"; case_tac "whd\<cdot>wout";
    (subst da_trans_one_def, simp add: uncont_def)+)
     apply(subst simplecomp_unfold, simp)

    apply(subst (6) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert  whd_conc)
    apply(subst conc_prod_apply_l[symmetric])
    apply(rule monofun_cfun_arg)

    apply(subst(1) simplecomp_unfold, auto)
    apply(rule monofun_cfun_arg, (subst assoc)?)+
    apply(subst(2) simplecomp_unfold, auto)
    apply(subst (3) dastatesem_step; simp add: Let_def case_prod_beta step_create_insert  whd_conc whd_rt)
     apply(rule monofun_cfun_arg, (subst assoc)?)+
     apply(subst(1) simplecomp_unfold, auto)
     apply(rule monofun_cfun_arg, (subst assoc)?)+
     apply(subst(2) comp_step_l; (simp add: assms)?)
     apply(simp add: conc_prod_def)

     apply(simp add:  assoc whd_conc whd_rt)
     apply(rule monofun_cfun_arg, (subst assoc)?)+
     apply(subst(2) comp_step_l; (simp add: assms)?)
    apply(simp add: conc_prod_def)

    apply(subst (3) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert  shd_conc)
    apply(subst conc_prod_apply_l[symmetric])
    apply(rule monofun_cfun_arg)

   apply(subst(1) simplecomp_unfold, auto simp add: shd_rt)
    apply(rule monofun_cfun_arg, (subst assoc)?)+
    apply(subst(2) comp_step_r; (simp add: assms)?)
    apply(simp add: conc_prod_def)

    apply(rule monofun_cfun_arg, (subst assoc)?)+
    apply(subst(2) comp_step_r; (simp add: assms)?)
    apply(simp add: conc_prod_def)

  apply(subst (3) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert  shd_conc)
  apply(subst (6) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert  whd_conc)
  apply(subst conc_prod_apply[symmetric])
  apply(rule monofun_cfun_arg, (subst assoc)?)+
  apply(subst(1) simplecomp_unfold, auto simp add: shd_rt whd_rt)
   apply(rule monofun_cfun_arg, (subst assoc)?)+
   apply(subst(2) comp_step_lr; (simp add: assms)?)
   apply(auto simp add: conc_prod_def)[1]

  apply(subst(2) comp_step_lr; (simp add: assms)?)
  apply(rule monofun_cfun_arg, (subst assoc)?)+
  by(auto simp add: conc_prod_def)


(*
lemma "daStateSem (step_lnat_add\<cdot>(step_create\<cdot>shd\<cdot>srt)) wda wstate\<cdot>
    (sout\<Zcat>\<Zcat>snd (daStateSem step_lnat (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate)\<cdot>ln), ln) \<sqsubseteq>
    fst (daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate)\<cdot>())"
  apply(induction ln arbitrary: sout wout sstate wstate, simp)
   apply(subst dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)

  apply(subst dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(subst(2) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(subst(3) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(subst(4) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(simp add: da_comp_trans Let_def case_prod_beta da_trans_one_def)

  apply(case_tac "shd\<cdot>sout"; case_tac "whd\<cdot>wout"; (simp add: uncont_def)?)

  apply(subst(4) dastatesem_step, simp add: Let_def case_prod_beta step_create_insert)
  apply(simp add: da_comp_trans Let_def case_prod_beta da_trans_one_def uncont_def)

  oops (* Klappt nicht *)

lemma comp_below_aut_comp_SORRY:
      fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
        and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
      and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"
  
(*        and input_induction: "\<And>s P. adm P \<Longrightarrow> ((shd\<cdot>s = \<bottom>) \<Longrightarrow> P s) \<Longrightarrow> (shd\<cdot>s\<noteq>\<bottom> \<Longrightarrow> P (srt\<cdot>s) \<Longrightarrow> P s) \<Longrightarrow> P s" *)
shows  "simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>
                   (daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout) 
    \<sqsubseteq> daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate)\<cdot>()"
  apply(subst simpleComp_def, simp)
(*  apply(subst daStateSem_def, simp add: case_prod_beta)+ *)
  apply(rule fix_least_below)
  apply simp
  apply(auto simp add: below_prod_def)

   apply(subst daStateSem_def, simp add: case_prod_beta)

   (* apply(induction sout rule: input_induction; (simp)?)*)
      (* "adm" *KÖNNTE* Problematisch sein :D *)

(* Alternativ: Kausalität? *)
  sorry
*)

lemma meta_all_cfun: assumes "f \<sqsubseteq> (\<Lambda> x . g)"
  shows "(f\<cdot>x \<sqsubseteq>g)"
proof -
  have "\<And>x. f\<cdot>x \<sqsubseteq> (\<Lambda> x . g)\<cdot>x"
    using assms cfun_below_iff by blast
  moreover have "(\<Lambda> x . g)\<cdot>x = g" by simp
  ultimately show ?thesis
    by auto
qed

lemma comp_eq_aut_comp:
      fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
        and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
      and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"
  
shows  "daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate)\<cdot>()
  \<sqsubseteq> simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout)"
proof -
  have h0: "daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) 
    \<sqsubseteq> (\<lambda>(wout, sout, wstate, sstate) . \<Lambda> _ . simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout))"
    by(rule aut_comp_below_comp;simp only: assms) 
  have h1: "(\<Lambda> _ . simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate oo conc sout))
  = (\<lambda>(wout, sout, wstate, sstate) . \<Lambda> _ . simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)
      \<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout)) (wout, sout, wstate, sstate)"
    by simp
  show " daStateSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda) (wout, sout, wstate, sstate)\<cdot>() \<sqsubseteq>
    simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate oo conc sout)"
    apply(rule meta_all_cfun)
    apply(subst h1)
    apply(rule fun_belowD [where
           g="(\<lambda>(wout, sout, wstate, sstate) . \<Lambda> _ . simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda sstate oo conc wout)\<cdot>(daStateSem (step_create\<cdot>shd\<cdot>srt) wda wstate  oo conc sout))"])
    by(rule aut_comp_below_comp; simp only: assms) 
qed


lemma sem_autcomp_below_comp:
      fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo}) dAutomaton"
        and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) dAutomaton"
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
      and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"
  shows "daSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda)\<cdot>() 
    \<sqsubseteq> simpleComp\<cdot>(daSem (step_create\<cdot>whd\<cdot>wrt) sda)\<cdot>(daSem (step_create\<cdot>shd\<cdot>srt) wda)"
  apply(auto simp add: daSem_def Let_def case_prod_beta da_comp_init)[1]
  apply(subst cfcomp1[symmetric])+
  apply(subst simpleComp_conc)
  apply(rule monofun_cfun_arg)
  apply(rule comp_eq_aut_comp)
  using assms by auto


lemma sem_autcomp_eq_comp:
      fixes wda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo, len_max}) dAutomaton"
        and sda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo, len_max}) dAutomaton"
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
      and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"

        and "# (daSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda)\<cdot>()) = \<infinity>"
  shows "daSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda)\<cdot>() 
    = simpleComp\<cdot>(daSem (step_create\<cdot>whd\<cdot>wrt) sda)\<cdot>(daSem (step_create\<cdot>shd\<cdot>srt) wda)"
  apply(rule len_max)
  apply(simp add: assms)
  by(rule sem_autcomp_below_comp; simp add: assms)



lemma autcomp2dacomp:
    "daSem step_unit ` nda2daset (aut_comp whd wrt shd srt nda1 nda2)
    = daSem step_unit ` (\<lambda>(wa,sa). da_comp whd wrt shd srt wa sa) ` (pairwise_union (nda2daset nda1) (nda2daset nda2))"
  sorry


theorem fixes wnda::"('wstate::type,'wmsg::type,'wout::{conc, pcpo, len_max}) automaton"
        and snda:: "('sstate::type,'smsg::type,'sout::{conc, pcpo, len_max}) automaton"

assumes "\<And>msg input. shd\<cdot>((sconv msg)\<Zcat>\<Zcat>input) = Def  msg"
      and "\<And>msg input. srt\<cdot>((sconv msg)\<Zcat>\<Zcat>input) = input"
      and "\<And>P s. adm P \<Longrightarrow>
       (\<forall>f::'wmsg \<Rightarrow> 'sout \<rightarrow> 'wout. step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>s = \<bottom> \<Longrightarrow> P s) \<Longrightarrow>
       (\<And>(x::'wmsg) xs::'sout. P xs \<Longrightarrow> P (sconv x\<Zcat>\<Zcat>xs)) \<Longrightarrow> P s"

      and "\<And>msg input. whd\<cdot>((wconv msg)\<Zcat>\<Zcat>input) = Def  msg"
      and "\<And>msg input. wrt\<cdot>((wconv msg)\<Zcat>\<Zcat>input) = input"
      and "\<And>(s::'wout) P::'wout \<Rightarrow> bool.
       adm P \<Longrightarrow>
       (\<forall>f::'smsg \<Rightarrow> 'wout \<rightarrow> 'sout. step_create\<cdot>whd\<cdot>wrt\<cdot>f\<cdot>s = \<bottom> \<Longrightarrow> P s) \<Longrightarrow>
       (\<And>(x::'smsg) xs::'wout. P xs \<Longrightarrow> P (wconv x\<Zcat>\<Zcat>xs)) \<Longrightarrow> P s"

        and whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
        and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"
      shows
"SimpleComp (sem (step_create\<cdot>whd\<cdot>wrt) snda) (sem (step_create\<cdot>shd\<cdot>srt) wnda) 
    = (\<lambda>k. k\<cdot>())` sem step_unit (aut_comp (uncont whd) wrt (uncont shd) srt wnda snda)"
proof -
  let ?sDAs = "((nda2daset snda)::('sstate\<times>('wout\<rightarrow>'sout), 'smsg, 'sout) dAutomaton set)"
  let ?wDAs = "((nda2daset wnda)::('wstate\<times>('sout\<rightarrow>'wout), 'wmsg, 'wout) dAutomaton set)"
  have "SimpleComp (sem (step_create\<cdot>whd\<cdot>wrt) snda) (sem (step_create\<cdot>shd\<cdot>srt) wnda) 
          = SimpleComp 
              (daSem (step_create\<cdot>whd\<cdot>wrt)` ?sDAs)
              (daSem (step_create\<cdot>shd\<cdot>srt)` ?wDAs)"
    apply(subst nda2daset [of _ sconv], simp add: assms step_create_insert )
     apply (metis assms(3))
    apply(subst nda2daset [of _ wconv], simp add: assms step_create_insert )
     apply (metis assms(6))
    by simp

  have "SimpleComp 
              (daSem (step_create\<cdot>whd\<cdot>wrt)` ?sDAs)
              (daSem (step_create\<cdot>shd\<cdot>srt)` ?wDAs)
      = {simpleComp\<cdot>(daSem (step_create\<cdot>whd\<cdot>wrt)sda)\<cdot>(daSem (step_create\<cdot>shd\<cdot>srt) wda) | sda wda. sda \<in> ?sDAs \<and> wda \<in>?wDAs}"
    by(auto simp add: SimpleComp_def image_iff)
  have "{simpleComp\<cdot>(daSem (step_create\<cdot>whd\<cdot>wrt)sda)\<cdot>(daSem (step_create\<cdot>shd\<cdot>srt) wda) | sda wda. sda \<in> ?sDAs \<and> wda \<in>?wDAs}
    = {daSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda)\<cdot>() | sda wda. sda \<in> ?sDAs \<and> wda \<in>?wDAs}"
    apply(subst sem_autcomp_eq_comp; simp add: assms) 
    sorry
  have "{daSem step_unit (da_comp (uncont whd) wrt (uncont shd) srt wda sda)\<cdot>() | sda wda. sda \<in> nda2daset snda \<and> wda \<in>nda2daset wnda}
    = (\<lambda>k. k\<cdot>())` (daSem step_unit ` (nda2daset (aut_comp (uncont whd) wrt (uncont shd) srt wnda snda)))"
    using autcomp2dacomp sorry
  have "(daSem step_unit ` (nda2daset (aut_comp (uncont whd) wrt (uncont shd) srt wnda snda)))
      = sem step_unit (aut_comp (uncont whd) wrt (uncont shd) srt wnda snda)"
    apply(subst nda2daset) sorry

  show ?thesis sorry
qed


lemma "SimpleComp (sem step1 nda1') (sem step2 nda2') 
  \<subseteq> SimpleComp (sem step1 nda1) (sem step2 nda2)"
oops



(*

(*****************************************************)
(*****************************************************)
  section \<open>ALTE VERSUCHE / KLAPPEN NICHTMEHR\<close>
(*****************************************************)
(*****************************************************)






lemma lnatinf_not_zero: "(\<infinity>::lnat) \<noteq> \<bottom>"
  using Inf'_neq_0_rev lnzero_def by auto

lemma cfun_below_switch: assumes "f \<sqsubseteq> (\<Lambda> x. z)" shows "f\<cdot>x \<sqsubseteq> z"
proof -
  have "Rep_cfun f \<sqsubseteq> (Rep_cfun (\<Lambda> x. z))"
    by (metis assms below_cfun_def)
  moreover have "Rep_cfun (\<Lambda> x. z) = (\<lambda>x. z)"
    apply(subst Abs_cfun_inverse2)
    by auto
  finally show ?thesis 
    by (simp add: fun_below_iff)
qed



section\<open>Versuch mit Induction über LNAT\<close>
lemma statesem_lnat_bot [simp]: "spf \<in> stateSem step_lnat aut s  \<Longrightarrow> spf\<cdot>\<bottom> = \<bottom>"
  apply(rule stateSem_bot [where step=step_lnat and aut=aut and s=s])
  by simp_all

lemma statesem_lnat_add_bot [simp]: "spf \<in> stateSem (step_lnat_add\<cdot>step) aut s \<Longrightarrow> spf\<cdot>(x,\<bottom>) = \<bottom>"
  apply(rule stateSem_bot [where step="step_lnat_add\<cdot>step" and aut=aut and s=s])
  by simp_all

lemma statesem_lnat_step: assumes "spf \<in> stateSem step_lnat nda s"
  shows "\<exists>spf2 output nextState. ((\<forall>ln. spf\<cdot>(lnsuc\<cdot>ln) = output \<Zcat>\<Zcat> (spf2\<cdot>ln)) 
    \<and> spf2 \<in> (stateSem step_lnat nda ) nextState
    \<and> (nextState,output) \<in> (autTransition\<cdot>nda) s ())"
proof-
  have spf_in_step: "spf\<in>stateSem_step step_lnat nda (stateSem step_lnat nda) s"
    by (simp add: assms stateSem_stepI)
  thus ?thesis
    apply(auto simp add: assms stateSem_step_def)
    by (metis step_lnat_lnsuc)
qed

lemma lnat_finsuc_nbot[simp]: "Fin (Suc n) \<noteq> \<bottom>"
  using Fin_0 lnzero_def by auto

(* Die Quantorenreihenfolge ist falsch. Eigentlich will ist: \<exists>f g. \<forall>n. *)
(* und es ist nur endlich tief ... *)
lemma context_eq_fin: 
      fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
        and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
      assumes "spf \<in> stateSem step_lnat (aut_comp (uncont whd) wrt (uncont shd) srt wa sa) (wout, sout, ws, ss)"
  shows "\<exists>f g. spf\<cdot>(Fin n) = simpleComp_lnat2\<cdot>f\<cdot>g\<cdot>(Fin n) 
               \<and> f \<in> stateSem (step_lnat_add\<cdot>(step_prefix wout\<cdot>(step_create\<cdot>whd\<cdot>wrt))) sa ss 
               \<and> g \<in> stateSem (step_lnat_add\<cdot>(step_prefix sout\<cdot>(step_create\<cdot>shd\<cdot>srt))) wa ws"
proof(insert assms, induction n arbitrary: ss sa wout wa ws sout spf)
  case 0
  obtain f where f_in: "f \<in> stateSem (step_lnat_add\<cdot>(step_prefix wout\<cdot>(step_create\<cdot>whd\<cdot>wrt))) sa ss"  
    by (meson ex_in_conv statesem_notempty)
  have "f\<cdot>\<bottom> = \<bottom>" by (metis inst_prod_pcpo statesem_lnat_add_bot f_in)

  obtain g where g_in: "g \<in> stateSem (step_lnat_add\<cdot>(step_prefix sout\<cdot>(step_create\<cdot>shd\<cdot>srt))) wa ws"  
    by (meson ex_in_conv statesem_notempty)
  have "g\<cdot>\<bottom> = \<bottom>" by (metis inst_prod_pcpo statesem_lnat_add_bot g_in)

  show ?case apply (auto simp add: lnzero_def) apply (subst inst_prod_pcpo)+ 
    using statesem_lnat_add_bot by (metis "0.prems" f_in g_in inst_prod_pcpo statesem_lnat_bot)  
next
  case (Suc n)
  (* Die "Prime" Version soll für "Fin n" gelten, sodass man die Induktionsannahmen verwenden kann. 
    \<open>spf'\<close> == Nachdem \<open>spf\<close> einen Schritt gemacht hat. (Ist über den Komponierten Automaten) *)
  obtain spf' "output" nextState where spf_step:"\<forall>ln. spf\<cdot>(lnsuc\<cdot>ln) = output \<Zcat>\<Zcat> (spf'\<cdot>ln)" 
     and spf'_in: "spf' \<in> (stateSem step_lnat (aut_comp (uncont whd) wrt (uncont shd) srt wa sa)) nextState"
     and trans: "(nextState,output) \<in> (autTransition\<cdot>(aut_comp (uncont whd) wrt (uncont shd) srt wa sa)) (wout, sout, ws, ss) ()"
    by (meson Suc.prems statesem_lnat_step)

  (* Mapping von der Transitionsfunktion des Komponierten Automatens zu den Transitionen der Teilautomaten *)
  obtain woutNext sout' wout' soutNext wsNext ssNext 
    where nextState_def: "nextState = (wout' \<Zcat>\<Zcat> woutNext, sout' \<Zcat>\<Zcat> soutNext, wsNext, ssNext)"
      and output_def: "output = (woutNext, soutNext)" 
      and sa_trans_fst: "wout' = fst (aut_trans_one sa (uncont whd) wrt wout ss)"
      and sa_trans_h: "(wsNext,woutNext) \<in> snd (aut_trans_one wa (uncont shd) srt sout ws)"
      and wa_trans_fst: "sout' = fst (aut_trans_one wa (uncont shd) srt sout ws)"
      and wa_trans_h: "(ssNext,soutNext) \<in> snd (aut_trans_one sa (uncont whd) wrt wout ss)"
    apply(insert trans) unfolding aut_comp.rep_eq autTransition.rep_eq by (auto simp add: pairwise_union_def)

  have "(uncont whd) wout \<noteq> None \<Longrightarrow> (ssNext,soutNext) \<in> (autTransition\<cdot>sa) ss (the ((uncont whd) wout))"
    apply(insert wa_trans_h) unfolding aut_trans_one_def by auto
  have "(uncont shd) sout \<noteq> None \<Longrightarrow> sout' = srt\<cdot>sout"
    apply(insert wa_trans_fst)unfolding aut_trans_one_def by auto
  have whd_bot: "(uncont whd) wout = None \<Longrightarrow> ssNext = ss \<and> soutNext = \<bottom> \<and> wout' = wout"
    apply(insert wa_trans_h sa_trans_fst) unfolding aut_trans_one_def by auto
  have "(uncont shd) sout \<noteq> None \<Longrightarrow> (wsNext,woutNext) \<in> (autTransition\<cdot>wa) ws (the ((uncont shd) sout))"
    apply(insert sa_trans_h) unfolding aut_trans_one_def by auto
  have "(uncont whd) wout \<noteq> None \<Longrightarrow> wout' = wrt\<cdot>wout"
    apply(insert sa_trans_fst) unfolding aut_trans_one_def by auto
  have shd_bot: "(uncont shd) sout = None \<Longrightarrow> wsNext = ws \<and> woutNext = \<bottom> \<and> sout' = sout"
    apply(insert sa_trans_h wa_trans_fst) unfolding aut_trans_one_def by auto

  
  obtain f' g' where spf2_n: "spf'\<cdot>(Fin n) = simpleComp_lnat2\<cdot>f'\<cdot>g'\<cdot>(Fin n)"
          and "f' \<in> stateSem (step_lnat_add\<cdot>(step_prefix (wout' \<Zcat>\<Zcat> woutNext)\<cdot>(step_create\<cdot>whd\<cdot>wrt))) sa ssNext"
          and "g' \<in> stateSem (step_lnat_add\<cdot>(step_prefix (sout' \<Zcat>\<Zcat> soutNext)\<cdot>(step_create\<cdot>shd\<cdot>srt))) wa wsNext"
    using Suc.IH nextState_def spf'_in by blast


  obtain f where f_step: "\<forall>input. (whd\<cdot>wout = whd\<cdot>(wout \<Zcat>\<Zcat> input) \<longrightarrow> f\<cdot>(input, lnsuc\<cdot>(Fin n)) = soutNext \<Zcat>\<Zcat> f'\<cdot>(input,(Fin n)) )"  (* stimmt für shd sout = None nicht *)
    and f_in: "f \<in> stateSem (step_lnat_add\<cdot>(step_prefix wout\<cdot>(step_create\<cdot>whd\<cdot>wrt))) sa ss"
    sorry
  obtain g where g_step: "\<forall>input. (shd\<cdot>sout = shd\<cdot>(sout \<Zcat>\<Zcat> input) \<longrightarrow> g\<cdot>(input, lnsuc\<cdot>(Fin n)) = woutNext \<Zcat>\<Zcat> g'\<cdot>(input,(Fin n)) )"
    and g_in: "g \<in> stateSem (step_lnat_add\<cdot>(step_prefix sout\<cdot>(step_create\<cdot>shd\<cdot>srt))) wa ws"
    sorry
  show ?case using spf_step  apply (simp only: Fin_Suc [symmetric] simplecomp_lnat2_step)  
    apply (auto)?
    apply(rule_tac exI [where x=f])
    apply(rule_tac exI [where x=g])
    apply(auto simp add: g_in f_in)
    apply(auto simp add: output_def spf2_n)
    apply (simp only: Fin_Suc [symmetric])
    apply(subst g_step) defer (* Das was ich "defer" gilt nicht *)
     apply(subst f_step) defer
      apply(subst conc_prod_def, auto)
       apply(rule cfun_arg_cong)

       apply(cases "(uncont shd) sout", simp add: shd_bot)

    apply(cases n; simp add: lnzero_def) defer (* Das würd sogar gelten, aber das "srt" ist vermutlich eine falsche annahme (siehe sorry oben) *)
        apply (simp only: Fin_Suc [symmetric], subst simplecomp_lnat2_step)+
        apply simp
       apply(rule cfun_arg_cong, simp)

        apply(cases "(uncont shd) sout"; cases "(uncont whd) wout"; simp?)

       apply(simp add: shd_bot whd_bot)
       apply(simp add: f_bot_def g_bot_def)
       apply(cases "Fin n = \<bottom>")
        apply auto 
         defer defer
    apply(subst spf2_n[symmetric])+

    sorry
qed 
lemma "Fin (Suc n) = lnsuc\<cdot>(Fin n)"
  by (metis Fin_Suc)

(*
  Stark Causal: -1 (initial Ausgabe 0)
  Weak Causal: +1 
*)

lemma 
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(stateSem step_lnat (aut_comp (uncont whd) wrt (uncont shd) srt  wa sa) (wout,sout,ws,ss)) 
      \<subseteq>  SimpleComp_lnat2 ((stateSem (step_lnat_add\<cdot>(step_prefix wout\<cdot>(step_create\<cdot>whd\<cdot>wrt)))) sa ss) 
                            (stateSem (step_lnat_add\<cdot>(step_prefix sout\<cdot>(step_create\<cdot>shd\<cdot>srt))) wa ws)"
(* Stimmt vermutlich nicht, weil "step_create" den buffer sofort auffrisst *)
proof
  fix spf
  assume as: "spf \<in> stateSem step_lnat (aut_comp whd wrt shd srt wa sa) (wout, sout, ws, ss)"
  have "\<And>n. \<exists>f g.
       spf\<cdot>(Fin n) = simpleComp_lnat\<cdot>f\<cdot>g\<cdot>(Fin n) \<and>
       f \<in> stateSem (step_create whd wrt) sa ss ooo {conc wout} \<and> g \<in> stateSem (step_create shd srt) wa ws ooo {conc sout}"
    apply(rule context_eq_fin)
    using as by auto
  have "\<exists>f g. 
        (\<forall> n. spf\<cdot>(Fin n) = simpleComp_lnat\<cdot>f\<cdot>g\<cdot>(Fin n)) \<and>
       f \<in> stateSem (step_create whd wrt) sa ss ooo {conc wout} \<and> g \<in> stateSem (step_create shd srt) wa ws ooo {conc sout}"
    sorry (* all-quantor durchziehen *)
  have "\<exists>f g. 
        (\<forall> ln. spf\<cdot>ln = simpleComp_lnat\<cdot>f\<cdot>g\<cdot>ln) \<and>
       f \<in> stateSem (step_create whd wrt) sa ss ooo {conc wout} \<and> g \<in> stateSem (step_create shd srt) wa ws ooo {conc sout}"
    apply(rule ccontr, auto)
    sorry (* Zu \<infinity> erweitern *)
  thus "spf \<in> SimpleComp_lnat (stateSem (step_create whd wrt) sa ss ooo {conc wout})
               (stateSem (step_create shd srt) wa ws ooo {conc sout})"
    apply (simp add: SimpleComp_lnat_def)
    using cfun_eqI by blast
qed

lemma 
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(stateSem step_lnat (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss)) 
      =  SimpleComp_lnat (stateSem (step_create whd wrt) sa ss ooo {conc wout} ) (stateSem (step_create shd srt) wa ws ooo {conc sout} )"




section\<open>Alter Versuch\<close>

lemma
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(\<lambda>(wout,sout,ws,ss). ((\<lambda>sb. (\<Lambda> _ . sb)) ` SimpleComp (stateSem (step_create whd wrt) sa ss ooo {conc wout} ) (stateSem (step_create shd srt) wa ws ooo {conc sout} ))) 
      \<le> ((stateSem step_unit (aut_comp whd wrt shd srt  wa sa))) "
  oops
lemma statesem_step_less: assumes "\<And> s a. a \<in> A s \<Longrightarrow> \<exists>f. a = step\<cdot>f \<and> undefined f"
  shows "A \<le> stateSem_step step aut A"
  apply(rule le_funI)
  apply(auto simp add: stateSem_step_def)
  sorry

lemma
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(\<lambda>(wout,sout,ws,ss). ((\<lambda>sb. (\<Lambda> _ . sb)) ` SimpleComp (stateSem (step_create whd wrt) sa ss ooo {conc wout} ) (stateSem (step_create shd srt) wa ws ooo {conc sout} ))) 
      \<le> ((stateSem step_unit (aut_comp whd wrt shd srt  wa sa))) "
  unfolding stateSem_def
  apply(rule gfp_upperbound, (subst stateSem_def[symmetric])+)
  apply(rule statesem_step_less)
  apply auto
  apply(rename_tac sout wout ss ws input "output" )
  apply(auto simp add: step_unit_def SimpleComp_def)
  apply(rule_tac x="\<lambda>_. (\<Lambda> _. (input, output))" in exI) 
  ..

lemma assumes "spf \<in> stateSem step nda state"
  shows "\<exists>da moreState. daStateSem step da (state,moreState) = spf
    \<and> (\<forall>moreState state msg. ((apfst fst) ((dautTransition da) (state,moreState) msg)) \<in> ((autTransition\<cdot>nda) state msg))"
  oops


lemma aut_comp_trace2spf_HELP:
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  assumes "spf \<in> (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))"
    assumes my_ind:  "\<And>P x. adm P \<Longrightarrow> (\<And>input. shd input = None \<Longrightarrow> P input)
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((conv msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
 shows "(\<exists>spf2. (spf2\<in>stateSem (step_create shd srt) wa ws  \<and> spf2\<cdot>(sout \<Zcat>\<Zcat> snd (spf\<cdot>())) = (fst (spf\<cdot>()))))"
  using assms apply(induction "sout \<Zcat>\<Zcat> snd (spf\<cdot>())" arbitrary: spf sout wout ws ss rule: my_ind)
  
    apply(rule adm_all)+
    apply(rule admI, auto)
  oops

lemma "adm (\<lambda>x. (output,input) \<in> (\<lambda>f. f\<cdot>x) ` A \<longrightarrow>
                  (\<exists>spf. spf \<in> B \<and> spf\<cdot>input = output))"
  apply(rule admI)
  oops
lemma aut_comp_trace2spf_HELP:
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(output,input) \<in> (\<lambda>f. f\<cdot>ln)` (stateSem step_lnat (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))
 \<longrightarrow> (\<exists>spf. (spf\<in>stateSem (step_create shd srt) wa ws ooo {conc sout} \<and> spf\<cdot>input = output))"
  apply(induction ln arbitrary: input "output" sout wout ws ss)
    apply(rule adm_all)+
  apply(rule admI)
     apply auto
    apply(insert adm_notin [where f = "(\<Lambda> x . (\<lambda>f. f\<cdot>x) ` stateSem step_lnat (aut_comp whd wrt shd srt wa sa) (wout, sout, ws, ss))"])
    apply(subst (asm) beta_cfun)
     defer
  apply simp

(* Erstelle eine SPF, welche sich genauso verhält und in einem dekomponierten automaten liegt *)
lemma aut_comp_trace2spf:
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  assumes "(output,input) \<in> (\<lambda>f. f\<cdot>())` (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))"
  shows "\<exists>spf. (spf\<in>stateSem (step_create shd srt) wa ws ooo {conc sout} \<and> spf\<cdot>input = output)"
proof - 
  obtain spf where "spf \<in> (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))" 
      and "spf\<cdot>() = (output,input)" using assms by force
  thus ?thesis sorry
qed
(* Beweisidee SSt: Induktion machen :D 
    Das "unit" ersetzen durch "lnat" und ein step_lemma über lnat machen
      -- Damit kann man nur prefix-machen ...
ODER: 
  Als Automatenverfeinerung beweisen. (Mit typ-änderung (und zustandsinvariante?))
     -- Nee, klappt vermutlich nicht
*)

lemma aut_comp_trace2spf___STUPID:  (* So nicht machen, sondern kommutativität verwenden! *)
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  assumes "(input,output) \<in> (\<lambda>f. f\<cdot>())` (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))"
  shows "\<exists>spf. spf\<in>(stateSem (step_create whd wrt) sa ss ooo {conc wout} ) \<and> spf\<cdot>input = output"
  sorry

thm gfp_def
lemma 
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "((\<lambda>f. f\<cdot>())` (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss)))
        \<subseteq> (SimpleComp (stateSem (step_create whd wrt) sa ss ooo {conc wout} ) (stateSem (step_create shd srt) wa ws ooo {conc sout} ))"
  apply(auto simp add: image_def)
proof -
  fix win sin comp
  assume as1: "comp \<in> stateSem step_unit (aut_comp whd wrt shd srt wa sa) (wout, sout, ws, ss)"
     and  as2: "(win, sin) = comp\<cdot>()"

  have as:"(win,sin) \<in> (\<lambda>f. f\<cdot>())` (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss))"
    by (simp add: as1 as2)
  have f_ex: "\<exists>f. (f\<in>(stateSem (step_create whd wrt) sa ss ooo {conc wout} ) \<and> f\<cdot>win = sin)"
    by (meson as aut_comp_trace2spf___STUPID) 
  have g_ex: "\<exists>g. (g\<in>(stateSem (step_create shd srt) wa ws ooo {conc sout} ) \<and> g\<cdot>sin = win)"
    by (meson as aut_comp_trace2spf) 
  obtain f where f_in: "f\<in>(stateSem (step_create whd wrt) sa ss ooo {conc wout} )" and "f\<cdot>win = sin"
    using f_ex by blast
  obtain g where g_in: "g\<in>(stateSem (step_create shd srt) wa ws ooo {conc sout} )" and "g\<cdot>sin = win" 
    using g_ex by blast
  have is_fix: "simpleComp\<cdot>f\<cdot>g = (win,sin)"
    unfolding simpleComp_def
    apply(subst beta_cfun, intro cont2cont)+
    apply(rule fix_eqI; simp)
     apply (simp add: \<open>f\<cdot>win = sin\<close> \<open>g\<cdot>sin = win\<close>)
    sorry (* SSt: Kann man mit Kausalität lösen *)

  show "comp\<cdot>() \<in> SimpleComp (stateSem (step_create whd wrt) sa ss ooo {conc wout}) (stateSem (step_create shd srt) wa ws ooo {conc sout})" 
      unfolding SimpleComp_def 
      apply auto
      apply(rule_tac x="f" in exI, rule_tac x="g" in exI) 
      using f_in g_in is_fix as2 by simp
  qed




lemma 
  fixes  wa:: "('wstate::type,'wmsg::type,'wout::{conc, pcpo}) automaton"
    and  sa:: "('sstate::type,'smsg::type,'sout::{conc, pcpo}) automaton"
  shows "(\<lambda>f. f\<cdot>())` (stateSem step_unit (aut_comp whd wrt shd srt  wa sa) (wout,sout,ws,ss)) 
      =  SimpleComp (stateSem (step_create whd wrt) sa ss ooo {conc wout} ) (stateSem (step_create shd srt) wa ws ooo {conc sout} )"
  oops

lemma "(stateSem step (aut_comp whd wrt shd srt aut' contextAut) s) \<subseteq> (stateSem step (aut_comp whd wrt shd srt aut contextAut) s)"
  oops




(* Alter Versuch:
  Nicht über Automaten-Komposition, sondern direkt als lemma über Komposition



(*
definition create_spf::"(('msg \<Rightarrow> 'in::cpo \<rightarrow> 'out) \<rightarrow> 'in \<rightarrow> 'out)
  \<Rightarrow> ('state::type,'msg::type,'out::{conc, pcpo}) automaton 
  \<Rightarrow> ('in \<rightarrow> 'out) \<rightarrow> ('state \<Rightarrow> 'in \<rightarrow> 'out)" where
"create_spf step aut = fix\<cdot>(\<Lambda> h spf. (\<lambda> state . undefined))" 


(* Create a new automaton from two others.
1. Automat: Refined Version of 2. Automat. only refined under the invariant!
2. Automat: Original Automat
*)
lift_definition inv_normalize_aut::"('state \<Rightarrow> 'msg \<Rightarrow> bool) \<Rightarrow> 
  ('state::type,'msg::type,'out::{conc, pcpo}) automaton \<Rightarrow>
  ('state::type,'msg::type,'out::{conc, pcpo}) automaton" is
"\<lambda> Inv aut. ((\<lambda>s m. if (Inv s m) then ((autTransition\<cdot>aut) s m) else UNIV), 
        autInitConfig\<cdot>aut)"
  by simp
*)


(* TODO:
  check "cout\<noteq>\<bottom>" durch was anderes ersetzen. Wird für Bündel probleme machen 
*)
lemma fixes aut and aut'::"('state::type,'msg::type,'out::{conc, pcpo}) automaton"
      and cAut::"('cstate::type,'cmsg::type,'cout::{conc, pcpo}) automaton"
      and Inv::"(('cstate\<times>'cout)\<times>('state\<times>'out)) \<Rightarrow> bool"

      and hd::"'cout \<Rightarrow> 'msg" and rt::"'cout \<rightarrow> 'cout"
      and chd::"'out \<Rightarrow> 'cmsg" and crt::"'out \<rightarrow> 'out"

assumes inv_init: "\<And>x. x \<in> pairwise_union (autInitConfig\<cdot>cAut) (autInitConfig\<cdot>aut')   
      \<Longrightarrow> Inv x"                                                                        (* Nur für "sem" notwendig *)
  and inv_step: "\<And>cs cout s out nextS nextOut. Inv ((cs,cout),(s,out)) \<Longrightarrow> cout\<noteq>\<bottom> \<Longrightarrow>
                    (nextS, nextOut) \<in> (autTransition\<cdot>aut') s (hd cout) \<Longrightarrow>
                     Inv ((cs,rt\<cdot>cout),(nextS, nextOut \<Zcat>\<Zcat> out))"
  and inv_cstep: "\<And>cs cout s out nextCS nextCOut. Inv ((cs,cout),(s,out)) \<Longrightarrow> out\<noteq>\<bottom> \<Longrightarrow>
                    (nextCS, nextCOut) \<in> (autTransition\<cdot>cAut) cs (chd out) \<Longrightarrow>
                     Inv ((nextCS,nextCOut \<Zcat>\<Zcat> cout),(s, crt\<cdot>out))"

  and aut_init_ref:"autInitConfig\<cdot>aut' \<subseteq> autInitConfig\<cdot>aut"                       (* Nur für "sem" notwendig *)
  and aut_trans_ref: "\<And>cs cout s out.  Inv ((cs,cout),(s,out)) \<Longrightarrow> cout\<noteq>\<bottom> \<Longrightarrow>  
    (autTransition\<cdot>aut') s (hd cout) \<subseteq> (autTransition\<cdot>aut) s (hd cout)"             (* Nur für "sem" notwendig *)

  and step_def:"\<And>f input. input \<noteq> \<bottom> \<Longrightarrow> step\<cdot>f\<cdot>input = f (hd input)\<cdot>(rt\<cdot>input)"
  and step2_def:"\<And>f input. input \<noteq> \<bottom> \<Longrightarrow> step2\<cdot>f\<cdot>input = f (chd input)\<cdot>(crt\<cdot>input)"

  and inv: "Inv ((cs,cout),(s,out))"
shows "SimpleComp (stateSem step aut' s ooo {conc cout} ) (stateSem step2 cAut cs ooo {conc out}) 
    \<subseteq> SimpleComp (stateSem step aut s ooo {conc cout}) (stateSem step2 cAut cs ooo {conc out})"
  unfolding SimpleComp_def simpleComp_def 
  apply(subst beta_cfun, intro cont2cont)+
  apply auto
  apply(rename_tac f g)
  apply(subst ex_comm, rule_tac x="g" in exI, simp?) 
(*  apply(subst stateSem_def | subst (asm) stateSem_def)+ *)
proof - 
  fix f_conc g_conc
  assume as_g:"g_conc \<in> (stateSem step2 cAut cs) ooo {conc out} " 
     and as_f:"f_conc \<in> (stateSem step aut' s)  ooo {conc cout} "

  obtain f where f_in: "f \<in> (stateSem step aut' s)" and f_conc_def: "f_conc = f oo (conc cout)"
    apply(insert as_f) unfolding nondet_comp_def by blast

  obtain g where g_in: "g \<in> (stateSem step2 cAut cs)" and g_conc_def: " g_conc = g oo (conc out)"
    apply(insert as_g) unfolding nondet_comp_def by blast


  obtain f_step where f_step: "\<forall>msg. \<exists>output nextState. 
     (nextState,output) \<in> (autTransition\<cdot>aut') s msg
      \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step aut') nextState 
         \<and>  (\<forall>input. f_step msg\<cdot>input = output \<Zcat>\<Zcat> nextSPF\<cdot>input))"
    and f_def: "f = step\<cdot>f_step"
    by(insert f_in, subst (asm)(2) stateSem_unfold, auto simp add: stateSem_step_def)

  have h: "\<exists>f_trans. \<forall>msg. ((f_trans msg) \<in> (autTransition\<cdot>aut') s msg \<and> (\<exists> nextSPF. nextSPF \<in> (stateSem step aut') (fst (f_trans msg))
         \<and>  (\<forall>input. f_step msg\<cdot>input = (snd (f_trans msg)) \<Zcat>\<Zcat> nextSPF\<cdot>input)))"
    apply(rule choice)
    using f_step by fastforce
  obtain f_trans where f_trans:"\<forall>msg. 
      (f_trans msg) \<in> (autTransition\<cdot>aut') s msg
    \<and> (\<exists> nextSPF. nextSPF \<in> (stateSem step aut') (fst (f_trans msg)) 
         \<and>  (\<forall>input. f_step msg\<cdot>input = (snd (f_trans msg)) \<Zcat>\<Zcat> nextSPF\<cdot>input))"
    using h by auto (* Bescheuert *)


  let ?g_trans = "\<lambda>msg. if (f_trans msg \<in> (autTransition\<cdot>aut) s msg) then f_trans msg 
                                else (SOME x. x\<in>(autTransition\<cdot>aut) s msg)"
  have "\<And>msg. ?g_trans msg \<in> (autTransition\<cdot>aut) s msg"
    apply auto apply(rule someI_ex)
    by (meson auttransition_nempty neq_emptyD)
  
  let ?g_step = "\<lambda>h msg. if (f_trans msg \<in> (autTransition\<cdot>aut) s msg) then f_step msg 
                              else (\<Lambda> input. snd (?g_trans msg) \<Zcat>\<Zcat> (SOME nextSPF. nextSPF\<in>(h) (fst (?g_trans msg)))\<cdot>input)"
  obtain g_step where g_step_def: "g_step = ?g_step" by simp
  have "\<And>h. step\<cdot>(g_step h) \<in> stateSem_step step aut h s"
    apply(auto simp add: stateSem_step_def image_def)
    apply(rule_tac x="g_step h" in exI, auto)
    apply(case_tac "f_trans msg \<in> (autTransition\<cdot>aut) s msg")
        apply (auto simp add: g_step_def) 


    apply(rule_tac x="snd (?g_trans msg)" in exI)
    apply(rule_tac x="fst (?g_trans msg)" in exI)
     apply (auto simp add: g_step_def) 
    sorry


  have "\<forall>cs cout s out. (Inv ((cs,cout),(s,out)) \<longrightarrow> 
    f \<in> (gfp (stateSem_step step aut') s) \<longrightarrow> 
  (\<exists>f'. (\<mu> output. f\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output))) = (\<mu> output. f'\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output))) \<and> f' \<in> gfp (stateSem_step step aut) s))" 
    apply(rule gfp_parallel_induct 
          [where f="stateSem_step step aut'"
             and g="stateSem_step step aut" ])
    apply simp+
     apply((rule allI | rule impI)+)
     apply(rule_tac x="step\<cdot>(g_step y)" in exI) (* Könnte klappen *)
     apply auto
    apply(rule cfun_arg_cong, rule cfun_eqI, simp)
    sorry

  hence "(\<exists>f'. (\<mu> output. f\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output))) = (\<mu> output. f'\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output))) \<and> f' \<in> (stateSem step aut) s)" 
    by (metis f_in inv stateSem_def)

  obtain f' where f'_def: "(\<mu> output. f\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output))) = (\<mu> output. f'\<cdot>(cout \<Zcat>\<Zcat> g\<cdot>(out \<Zcat>\<Zcat> output)))" and f'_in: "f' \<in> (stateSem step aut) s"
    using \<open>\<exists>f'. (\<mu> x. f\<cdot>(cout\<Zcat>\<Zcat>g\<cdot>(out\<Zcat>\<Zcat>x))) = (\<mu> x. f'\<cdot> (cout\<Zcat>\<Zcat>g\<cdot>(out\<Zcat>\<Zcat>x))) \<and> f' \<in> stateSem step aut s\<close> by auto

  show "\<exists>x. (\<mu> out. f_conc\<cdot>(g_conc\<cdot>out)) = (\<mu> out. x\<cdot>(g_conc\<cdot>out)) \<and> x \<in> stateSem step aut s ooo {conc cout}"
    apply(rule_tac x="f' oo conc cout" in exI, auto simp add: f_conc_def g_conc_def) 
     apply (simp add: f'_def f_conc_def)
    unfolding nondet_comp_def apply auto
    using f'_in by auto
  qed



(*
(* Anderer Versuch *)
proof 
  let ?system = "\<lambda>aut. SimpleComp (stateSem step aut s) (stateSem step2 cAut cs)"

  let ?aut' = "?system aut'"
(*  let ?normalized = "?system (inv_normalize_aut (\<lambda>s m. \<exists>cs cout out. cout \<noteq> \<bottom> \<and> fst cout = m\<and> Inv ((cs,cout),(s,out))) aut')" *)
  let ?aut = "?system aut"


  fix x
  assume "x \<in> ?aut'"


  have "?aut' \<subseteq> ?aut"
  apply(auto simp add: SimpleComp_def)
    apply(subst ex_comm, rule_tac x="g" in exI, simp)

    apply(rule_tac x="undefined" in exI)  (* nur mal testen *)
    apply auto
    unfolding SimpleComp_def simpleComp_def
     apply(subst beta_cfun, intro cont2cont)+
     apply(rule parallel_fix_ind, auto)

    apply(induct_tac y)
      sorry  (* sollte gehen ... *)



  have "x \<in> ?aut" 
    oops
  qed

*)




  section \<open>Tests\<close>

(*
definition wtrans::"unit \<Rightarrow> nat \<Rightarrow> (unit\<times>bool stream) set" where
"wtrans state input = {((), \<up>(even input))}"

definition strans::"unit \<Rightarrow> bool \<Rightarrow> (unit\<times>nat stream) set" where
"strans state input = {((), \<up>n) | n. even n}"

definition winit::"(unit\<times>bool stream) set" where
"winit = {((),\<epsilon>)}"

definition sinit::"(unit\<times>(nat stream)) set" where
"sinit = ({((), \<up>n) | n. even n})"




lift_definition waut::"(unit, nat, bool stream) automaton" is
"(wtrans, winit)"
  by(simp add: winit_def wtrans_def)

lift_definition saut::"(unit, bool, nat stream) automaton" is
"(strans, sinit)"
  apply(simp add: sinit_def strans_def)
  by arith


lemma "aut_comp waut saut = undefined"
  oops
*)
*)
*)
end