theory Steps
  imports inc.LNat inc.Prelude inc.Classes 
      automaton.DeterministicAutomaton 

begin

definition step_unit::"(unit \<Rightarrow> unit \<rightarrow> 'out) \<rightarrow> unit \<rightarrow> 'out::cpo" where
"step_unit = (\<Lambda> f _. f ()\<cdot>())"

lemma step_unit_insert[simp]: "step_unit\<cdot>f\<cdot>() = f ()\<cdot>()"
  by (simp add: step_unit_def)




definition step_create::"('in \<rightarrow> 'msg lift) \<rightarrow> ('in \<rightarrow> 'in) \<rightarrow> ('msg \<Rightarrow> 'in::cpo \<rightarrow> 'out) \<rightarrow> 'in \<rightarrow> 'out::pcpo" where
"step_create = (\<Lambda> shd srt f input. flift1 (\<lambda>msg. f msg\<cdot>(srt\<cdot>input))\<cdot>(shd\<cdot>input))"

lemma step_create_insert: "step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>input = flift1 (\<lambda>msg. f msg\<cdot>(srt\<cdot>input))\<cdot>(shd\<cdot>input)"
  unfolding step_create_def
  apply(subst beta_cfun, intro cont2cont)+
  ..

lemma step_create_insert2: assumes "shd\<cdot>input = Def msg"
  shows "step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>input = f msg\<cdot>(srt\<cdot>input)"
  by(simp add: step_create_insert assms)

lemma step_create_bot[simp]: assumes "shd\<cdot>input = \<bottom>"
  shows "step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>input = \<bottom>"
  by(simp add: step_create_insert assms)

lemma step_create_insert3: assumes "shd\<cdot>input \<noteq> \<bottom>"
  shows "step_create\<cdot>shd\<cdot>srt\<cdot>f\<cdot>input = f ((inv Def)(shd\<cdot>input))\<cdot>(srt\<cdot>input)"
proof - 
  obtain msg where as: "shd\<cdot>input = Def msg" 
    by (meson assms not_Undef_is_Def)
  have "((inv Def) (Def msg)) = msg"
    by (meson f_inv_into_f lift.inject rangeI)
  thus ?thesis using step_create_insert2 as by auto
qed


definition uncont::"('a::cpo \<rightarrow> 'b::type lift) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"uncont f a = (case (f\<cdot>a) of \<bottom> \<Rightarrow> None | Def x \<Rightarrow> Some x)"




definition step_lnat::"(unit \<Rightarrow> lnat \<rightarrow> 'out) \<rightarrow> lnat \<rightarrow> 'out::pcpo" where
"step_lnat = (\<Lambda> f. strictify\<cdot>(\<Lambda> ln. f ()\<cdot>(lnpred\<cdot>ln)))"

lemma step_lnat_bot[simp]: "step_lnat\<cdot>f\<cdot>\<bottom> = \<bottom>" 
  and step_lnat_lnsuc[simp]: "step_lnat\<cdot>f\<cdot>(lnsuc\<cdot>ln) = f ()\<cdot>ln"
  unfolding step_lnat_def
   by(subst beta_cfun, intro cont2cont; simp?)+



definition step_lnat_add::"(('msg \<Rightarrow> 'in::cpo \<rightarrow> 'out) \<rightarrow> 'in \<rightarrow> 'out::pcpo) \<rightarrow> ('msg \<Rightarrow> ('in\<times>lnat) \<rightarrow> 'out) \<rightarrow> ('in\<times>lnat) \<rightarrow> 'out::pcpo" where
"step_lnat_add = (\<Lambda> step f input. (strictify\<cdot>(\<Lambda> _. step\<cdot>(\<lambda>msg. \<Lambda> innerInput. f msg\<cdot>(innerInput,lnpred\<cdot>(snd input)))\<cdot>(fst input)))\<cdot>(snd input))"

lemma step_lnat_add_bot[simp]: "step_lnat_add\<cdot>step\<cdot>f\<cdot>(as,\<bottom>) = \<bottom>"
 and step_lnat_add_lnsuc[simp]: "step_lnat_add\<cdot>step\<cdot>f\<cdot>(as, lnsuc\<cdot>ln) = step\<cdot>(\<lambda>msg. \<Lambda> innerInput. f msg\<cdot>(innerInput,ln))\<cdot>as"
  unfolding step_lnat_add_def
   apply(subst beta_cfun, intro cont2cont)+
  apply (simp; fail)
  apply(subst beta_cfun, intro cont2cont)+
  apply(subst strictify2, simp)
  apply(subst beta_cfun, intro cont2cont)+
  by simp

lemma step_lnat_add_zero[simp]: "step_lnat_add\<cdot>step\<cdot>f\<cdot>(as,0) = \<bottom>"
  using lnzero_def by simp

lemma step_lnat_add_bot2[simp]: "step_lnat_add\<cdot>step\<cdot>f\<cdot>\<bottom> = \<bottom>"
  by (metis Pair_bottom_iff step_lnat_add_bot)

lemma statesem_lnat0 [simp]:"spf \<in> stateSem (step_lnat_add\<cdot>step) nda s \<Longrightarrow> spf\<cdot>(input, 0) = \<bottom>"
  apply(subst (asm) stateSem_unfold, subst (asm) stateSem_step_def)
  by auto

lemma dastatesem_lnat0[simp]: "daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input,0) = \<bottom>"
  by(subst dastatesem_step, simp)
lemma statesem_step_bot [simp]: "daStateSem (step_lnat_add\<cdot>stream_step) da s oo (\<Lambda> x. (x, \<bottom>)) = \<bottom>"
  by(intro cfun_eqI, simp)

lemma dastatesem_step_lnat: "daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input, lnsuc\<cdot>ln)
 = step\<cdot>(\<lambda>sbe. \<Lambda> sb.
           let (nextState, output) = (dautTransition da) s sbe in
                output \<Zcat>\<Zcat> (daStateSem (step_lnat_add\<cdot>step) da) nextState\<cdot>(sb,ln))\<cdot>input"
  by(subst dastatesem_step, simp)

context
begin
  private lemma below1:  "daStateSem (step_lnat_add\<cdot>step) da \<sqsubseteq> (\<lambda>s. \<Lambda> input. daStateSem step da s\<cdot>(fst input))"
  unfolding daStateSem_def
  apply(rule fix_least_below)
  apply(rule fun_belowI, rule cfun_belowI)
  apply(rename_tac outer_input, case_tac outer_input, rename_tac stream lnat)
  apply simp
  apply(case_tac lnat rule: lnat.exhaust; simp)
  by(subst(2) fix_eq, simp)

  private lemma below2: "daStateSem step da \<sqsubseteq>  (\<lambda>s. \<Lambda> input. daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input,\<infinity>))"
  unfolding daStateSem_def
  apply(rule fix_least_below)
  apply(rule fun_belowI, rule cfun_belowI)
  apply simp
  apply(subst(2) fix_eq, simp)
  apply(subst(2) fold_inf[symmetric], simp only: step_lnat_add_lnsuc)
  by simp

  theorem da_add_lnat:
    "daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input,\<infinity>) = daStateSem step da s\<cdot>input"
  proof (rule below_antisym)
    have "daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input,\<infinity>) \<sqsubseteq> (\<lambda>s. \<Lambda> input. daStateSem step da s\<cdot>(fst input)) s\<cdot>(input,\<infinity>)"
      apply(rule monofun_cfun_fun [where x="(input,\<infinity>)"])
      apply(rule fun_belowD [where x="s"])
      by(rule below1)
    thus "daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input,\<infinity>) \<sqsubseteq> daStateSem step da s\<cdot>input"
      apply(subst (asm) beta_cfun, intro cont2cont)
      by simp
  next
    have "daStateSem step da s\<cdot>input \<sqsubseteq> (\<Lambda> i. daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(i, \<infinity>))\<cdot>input" 
      apply(rule monofun_cfun_fun [where x="input"])
      apply(rule fun_belowD [where x="s"])
      by(rule below2)

    thus "daStateSem step da s\<cdot>input \<sqsubseteq> daStateSem (step_lnat_add\<cdot>step) da s\<cdot>(input, \<infinity>)" 
      apply(subst (asm) beta_cfun, intro cont2cont)
      .
  qed

  theorem da_lnat2eq:
    assumes "\<And>ln. daStateSem (step_lnat_add\<cdot>step1) da1 s1\<cdot>(input1,ln) = daStateSem (step_lnat_add\<cdot>step2) da2 s2\<cdot>(input2,ln)"
    shows "daStateSem step1 da1 s1\<cdot>input1 = daStateSem step2 da2 s2\<cdot>input2"
    apply(subst da_add_lnat[symmetric])
    apply(subst(2) da_add_lnat[symmetric])
    using assms by auto
end




(*
lemma "\<forall>s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) ` stateSem (step_lnat_add\<cdot>step) nda s \<le> stateSem step nda s"
  apply(rule statesem_input_convert [where rep_msg="id"])
   apply(simp add: oo_def)
   apply(subst fold_inf[symmetric], subst step_lnat_add_lnsuc)
  by auto
*)
(*
SSt: Der Rest ist ein Versuch
    \<open>stateSem step nda s \<le> (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) ` stateSem (step_lnat_add\<cdot>step) nda s\<close>
zu zeigen


declare[[show_sorts]]
lemma assumes "\<And>sb. stake\<cdot>sb\<cdot>\<bottom> = \<bottom>" 
    shows  "\<forall>s. (\<lambda>f .f oo (\<Lambda> sb. stake\<cdot>(fst sb)\<cdot>(snd sb))) ` stateSem step nda s \<le> stateSem (step_lnat_add\<cdot>step) nda s"
  apply(rule statesem_input_convert [where rep_msg="id"])
   apply simp
   apply(rule cfun_eqI, rename_tac input)
  apply(case_tac "snd input" rule: lnat.exhaust)
    apply (auto simp add: assms)
  oops  (* würde funktionieren, aber die Annahme \<open>step\<cdot>f\<cdot>\<bottom> = \<bottom>\<close> gilt nicht für den leeren kanal (unit) *)


(* Cooles ding, hilft für das <stateSem step = stateSem (add_lnat step)> aber nicht*)
thm gfp_rolling
(* g: (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s)) *)
(* f: (stateSem_step (step_lnat_add\<cdot>step) nda) o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s)) *)



lemma "gfp ((\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s)) 
    o (stateSem_step (step_lnat_add\<cdot>step) nda)
    o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s)))
  = (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s)) 
        (gfp (stateSem_step (step_lnat_add\<cdot>step) nda))"
  oops

lemma " (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s)) 
      o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s))
      = id"
  apply(intro fun_eqI)
  apply(auto simp add: oo_def image_iff)
  oops

lemma " (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s))
      o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s)) 
      = id"
  apply(intro fun_eqI cfun_eqI)
  by(auto simp add: oo_def image_iff)



lemma step2lnatstep: "stateSem_step step nda \<le> (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s)) 
    o (stateSem_step (step_lnat_add\<cdot>step) nda)
    o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s))"
  apply(rule le_funI)+
  apply(auto simp add: stateSem_step_def o_def oo_def image_iff)
  apply(subst fold_inf[symmetric], subst step_lnat_add_lnsuc)
  apply simp
  apply(rename_tac f)
  apply(rule_tac x="\<lambda>s. (f s) oo (\<Lambda> i. fst i)" in exI)
  apply auto
  by fastforce

lemma surj_inj_ccomp: 
  assumes "surj (Rep_cfun rep)"
  shows "inj (\<lambda>f .f oo rep)"
  apply(simp add: inj_def) 
  using cfun_eqI cfcomp2
  by (metis (no_types, opaque_lifting) assms surj_def)

lemma "inj f \<Longrightarrow> inj (\<lambda>A . f ` A)"
  by (simp add: inj_on_image)
lemma inj_d: "inj f \<Longrightarrow> inj (\<lambda> A s. f (A s))"
  apply(intro injI fun_eqI)
  by (meson injD)


thm fix_const
lemma assumes "\<And>x z. z x = g x (z x) \<Longrightarrow> g x (z x) \<le> z x"
  shows "gfp (\<lambda>S. \<lambda>x. g x (S x)) = (\<lambda> x. (gfp (\<lambda>S. g x S)))"
  oops

lemma gfp_const: (* bringt nichts / schlecht anwendbar*)
  assumes g_mono: "mono g" and g_mono2:"\<And>x. mono (g x)"
  shows "gfp (\<lambda>S. \<lambda>x. g x (S x)) const = gfp (\<lambda>S. g const S)"
  apply(rule gfp_parallel_induct [of "\<lambda>S. \<lambda>x. g x (S x)"])
     apply (metis (mono_tags, lifting) g_mono2 le_fun_def monoD monoI)
    apply (simp add: g_mono2)
   apply simp 
  by (metis (mono_tags, lifting) INF_apply image_cong)

lemma
  assumes "g o P o P = P"
  shows "P (gfp g) \<le> gfp (\<lambda>S. g (P S))"
  apply(rule gfp_upperbound)
  by (metis assms comp_apply order_class.order_eq_iff)

lemma gfp_mono2: "mono x \<Longrightarrow> mono y \<Longrightarrow> x \<le> y \<Longrightarrow> gfp x \<le> gfp y"
  by (simp add: gfp_mono le_fun_def)


lemma fixes M::"'a::po set set"
  assumes "\<And>m. m\<in>M \<Longrightarrow> P m"
  and "(\<Inter>M) \<noteq> {}" and "M\<noteq>{}"
  and "\<And>a b. a\<in>M  \<Longrightarrow> b\<in>M \<Longrightarrow> (a \<sqsubseteq> b \<or> b\<sqsubseteq>a)"
shows "P (\<Inter>M)"
  oops

definition longChain :: "'a::po set \<Rightarrow> bool" where
"longChain S \<equiv> S={} \<and> (\<forall>a b. (a\<in>S \<and> b\<in>S) \<longrightarrow> (a \<sqsubseteq> b \<or> b\<sqsubseteq>a))"

lemma assumes "\<forall>m\<in>M. fst m \<le> (\<lambda>s. (\<lambda>f. f oo (\<Lambda> i. (i, \<infinity>))) ` snd m s)"
       and "\<forall>m\<in>M. f \<in> fst m x"
      and "longChain (snd ` M)" and "M\<noteq>{}"
     shows "f \<in> (\<lambda>x. x oo (\<Lambda> i. (i, \<infinity>))) ` (\<Inter>m\<in>M. snd m x)"
  oops (* \<Inter>m\<in>M ist das problem *)


lemma
  shows    "stateSem step nda \<le> (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s))  
                (stateSem (step_lnat_add\<cdot>step) nda)"
  apply(subst stateSem_def) +
  apply(rule gfp_parallel_induct [where f="stateSem_step step nda" and 
                                        g="(stateSem_step (step_lnat_add\<cdot>step) nda)"])
     apply simp+
   defer
   apply simp
  apply(intro le_funI)
   apply auto[1]
  oops (*

  apply(rule order_trans[where x="gfp (stateSem_step step nda)" and y="gfp ((\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. (i,\<infinity>))) `(A s)) 
    o (stateSem_step (step_lnat_add\<cdot>step) nda)
    o (\<lambda>A s. (\<lambda>f .f oo (\<Lambda> i. fst i)) `(A s)))"])
   apply(rule gfp_mono2)
     apply simp+
    defer
    apply (simp add: step2lnatstep)


  oops (*

  apply(rule gfp_3roll [where f="stateSem_step (step_lnat_add\<cdot>step) nda"])
     apply(intro monoI fun_belowI le_funI)
     apply auto[1]
     apply (meson image_iff in_mono le_fun_def)
    apply simp
   apply(intro monoI le_funI)
   apply (simp add: image_mono le_funD)

  apply (auto simp add: o_def id_def)
  apply(intro monoI le_funI)
    apply(auto simp add: stateSem_step_def image_iff)


    defer
  apply (auto simp add: image_comp oo_def)
  oops
*)
*)


(* Anwendungsfall: "rep" = tsynAbs  ... nicht injektiv!
                  "nda1" = timed Automaton
                  "nda2" = untimed Automaton *)
theorem
  assumes (*"surj (Rep_cfun rep)"
  and*) rep_inv: "rep oo invRep = ID"
  and "inj (Rep_cfun invRep)"
  shows "stateSem step1 nda1 s \<le> (\<lambda>f .f oo rep) ` stateSem step2 nda2 s"
proof -
(*  have inj: "inj (\<lambda>f .f oo rep)"
    using UNIV_I assms cfcomp2 cfun_eqI image_iff inj_def
    by (simp add: surj_inj_ccomp)
  *)  
  have main: "\<forall>s. (\<lambda>f .f oo invRep) ` stateSem step1 nda1 s \<le> stateSem step2 nda2 s"
  unfolding stateSem_def
     apply(rule gfp_parallel_induct [of "(stateSem_step step1 nda1)" "stateSem_step step2 nda2"])
     apply simp+
   defer
   apply auto[1]
   apply fastforce
  sorry (* Unten ist es problematisch: *)
  have "(\<lambda>f .f oo invRep) o (\<lambda>f .f oo rep) = id"
    apply(simp add: o_def id_def)
    apply(subst assoc_oo[symmetric], subst rep_inv)
    by simp
  have "(\<lambda>f .f oo invRep) ` stateSem step1 nda1 s \<subseteq> (\<lambda>f .f oo invRep) ` (\<lambda>f. f oo rep) ` stateSem step2 nda2 s"
    apply(rule image_subsetI)
    apply(simp add: image_comp assoc_oo[symmetric] rep_inv) 
    using main by fastforce
  thus ?thesis 
    using inj_image_subset_iff(* ... problematisch *)
    
    oops




(*
lemma assumes "\<forall>m\<in>M. (\<forall>s. fst m s \<subseteq> (\<lambda>f. f o rep) ` snd m s)"
          and "\<forall>m\<in>M. x \<in> fst m s" 
          and "surj (rep)"
        shows "x \<in> (\<lambda>f. f o rep) ` (\<Inter>x\<in>M. snd x s)"
proof -
  have "\<forall>m\<in>M. x \<in> (\<lambda>f. f o rep) ` snd m s" 
    using assms(1) assms(2) by blast
  have "\<And>f Z. surj f \<Longrightarrow> inj f \<Longrightarrow> f ` (\<Inter>Z) =  \<Inter>((\<lambda>a. f ` a) ` Z)"
    apply auto
    apply (simp add: image_iff)
    by (metis InterI iso_tuple_UNIV_I range_ex1_eq)
  have "inj (\<lambda>f. f o rep)" 
    apply(rule injI, rule fun_eqI)
    apply(simp add: o_def) 
    by (metis assms(3) imageE iso_tuple_UNIV_I)
   

  have "\<And> Z. (\<lambda>f. f o rep) ` (\<Inter>Z) =  \<Inter>((\<lambda>a. (\<lambda>f. f o rep) ` a) ` Z)"
    apply (auto simp add: o_def image_iff)
    using assms(3) oops
    *)

*)
end