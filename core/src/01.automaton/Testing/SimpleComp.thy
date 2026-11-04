theory SimpleComp

imports HOLCF inc.Prelude inc.LNat inc.Classes 
  automaton.DeterministicAutomaton
  automaton.Steps

begin


declare[[show_types]]
declare[[show_consts]]
declare[[show_sorts]]



definition simpleComp::"('in::pcpo \<rightarrow> 'out::pcpo) \<rightarrow> ('out \<rightarrow> 'in) \<rightarrow> ('in \<times> 'out)" where
"simpleComp = (\<Lambda> f g. fix\<cdot>(\<Lambda> prev. (g\<cdot>(snd prev), f\<cdot>(fst prev))))"

lemma simplecomp_unfold:"simpleComp\<cdot>f\<cdot>g = (g\<cdot>(snd (simpleComp\<cdot>f\<cdot>g)), f\<cdot>(fst (simpleComp\<cdot>f\<cdot>g)))"
  unfolding simpleComp_def
  apply(subst beta_cfun, intro cont2cont)+
  apply(subst fix_eq)
  apply(subst beta_cfun, intro cont2cont)+
  ..



lemma comp_step_l:
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
        and "whd\<cdot>input = Def wmsg"
      shows "simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda state oo (conc input))\<cdot>spf2 
      = (\<bottom>,((snd (dautTransition sda state wmsg)))) \<Zcat>\<Zcat>
        (simpleComp\<cdot>(
          daStateSem (step_create\<cdot>whd\<cdot>wrt) sda (fst (dautTransition sda state wmsg)) oo (conc (wrt\<cdot>input)))\<cdot>
          (spf2 oo (conc (snd (dautTransition sda state wmsg)))))" (is "?L = ?RProd \<Zcat>\<Zcat> ?R")
proof - 
  have "?L \<sqsubseteq> ?RProd \<Zcat>\<Zcat> ?R"
  apply(subst (1) simpleComp_def, simp)
  apply(rule fix_least_below; simp)
  apply(simp add: conc_prod_def)
     apply(subst (2) simplecomp_unfold, simp add: conc_prod_def)
    apply(subst (2) simplecomp_unfold, simp add: conc_prod_def)
    by(subst (1) dastatesem_step; simp add: Let_def case_prod_beta step_create_insert  whd_conc whd_rt assms assoc)
  moreover have "?RProd \<Zcat>\<Zcat> ?R \<sqsubseteq> ?L"
    apply(subst (1) simpleComp_def, simp)
    apply(rule fix_ind; simp)
    apply(subst(1) simplecomp_unfold, simp)
     apply(subst (1) dastatesem_step; simp add: Let_def case_prod_beta step_create_insert  whd_conc whd_rt assms assoc)
     apply (metis botconc2 cont_pref_eq1I minimal)
    apply (auto simp add: below_prod_def conc_prod_def)[1]

     apply(subst(1) simplecomp_unfold, simp)
     apply(rule monofun_cfun_arg, (subst assoc)?)+
    apply simp

    apply(subst(1) simplecomp_unfold, simp)
     apply(subst(2) dastatesem_step; simp add: Let_def case_prod_beta step_create_insert  whd_conc whd_rt assms assoc)
     apply(rule monofun_cfun_arg, (subst assoc)?)+
    by simp
  ultimately show ?thesis
    using below_antisym by blast
qed

lemma simplecomp_commutative: 
    "simpleComp\<cdot>spf1\<cdot>spf2 = (\<lambda>(a,b). (b,a)) (simpleComp\<cdot>spf2\<cdot>spf1)"
  unfolding simpleComp_def
  apply(auto simp add: case_prod_beta)[1]
  by(rule parallel_fix_ind; simp)

lemma comp_step_r:
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
        and "whd\<cdot>input = Def wmsg"
      shows "simpleComp\<cdot>spf2\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda state oo (conc input))
      = ((snd (dautTransition sda state wmsg)), \<bottom>) \<Zcat>\<Zcat>
        (simpleComp\<cdot>
          (spf2 oo (conc (snd (dautTransition sda state wmsg))))\<cdot>
          (daStateSem (step_create\<cdot>whd\<cdot>wrt) sda (fst (dautTransition sda state wmsg)) oo (conc (wrt\<cdot>input)))
        )"
  apply(subst simplecomp_commutative)
  apply(subst comp_step_l; (simp add: assms)?)
  apply(subst simplecomp_commutative)
  by(auto simp add: case_prod_beta assms conc_prod_def)

lemma oo_and_conc[simp]: "(f oo (conc sb1)) oo (conc sb2) = f oo (conc (sb1 \<Zcat>\<Zcat>sb2))"
  apply(rule cfun_eqI)
  by(simp add: oo_def assoc)

lemma comp_step_lr:
  assumes whd_conc: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> whd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and whd_rt: "\<And>a b ac. whd\<cdot>a = Def b \<Longrightarrow> wrt\<cdot>(a \<Zcat>\<Zcat> ac) = (wrt\<cdot>a) \<Zcat>\<Zcat> ac"
        and shd_conc: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> shd\<cdot>(a \<Zcat>\<Zcat> ac) = Def b"
        and shd_rt: "\<And>a b ac. shd\<cdot>a = Def b \<Longrightarrow> srt\<cdot>(a \<Zcat>\<Zcat> ac) = (srt\<cdot>a) \<Zcat>\<Zcat> ac"
        and "whd\<cdot>winput = Def wmsg"
        and "shd\<cdot>sinput = Def smsg"
      shows "simpleComp\<cdot>(daStateSem (step_create\<cdot>whd\<cdot>wrt) sda state oo (conc winput))\<cdot>
                        (daStateSem (step_create\<cdot>shd\<cdot>srt) wda wtate oo (conc sinput)) 
      = ((snd (dautTransition wda wtate smsg)),((snd (dautTransition sda state wmsg)))) \<Zcat>\<Zcat>
        (simpleComp\<cdot>(
          daStateSem (step_create\<cdot>whd\<cdot>wrt) sda (fst (dautTransition sda state wmsg)) oo (conc ((wrt\<cdot>winput) \<Zcat>\<Zcat> (snd (dautTransition wda wtate smsg)))))\<cdot>
          ((daStateSem (step_create\<cdot>shd\<cdot>srt) wda (fst (dautTransition wda wtate smsg)) oo (conc ((srt\<cdot>sinput) \<Zcat>\<Zcat> (snd (dautTransition sda state wmsg)))))))"
  apply(subst comp_step_l; (simp add: assms)?)
  apply(subst comp_step_r; (simp add: assms)?)
  by(auto simp add: conc_prod_def assoc)





lemma simplecomp_causality:
  assumes "\<And>x. #x \<le> #(f\<cdot>x)" and "\<And>x. lnsuc\<cdot>(#x) \<le> #(g\<cdot>x)"
  shows "#(simpleComp\<cdot>f\<cdot>g) = \<infinity>"
  apply(auto simp add: len_prod_def min_def)[1]
  apply( subst simplecomp_unfold; simp)
   apply (metis assms(2) fstI inf_ub le2lnle leD less_lnsuc neqE simplecomp_unfold)
  by (metis assms(1) simplecomp_unfold snd_conv)



(*
(* SSt: In der Hoffnung, dass man so Induktion verwenden kann (über lnat) *)
definition simpleComp_lnat::"('in::pcpo \<rightarrow> 'out::pcpo) \<rightarrow> ('out \<rightarrow> 'in) \<rightarrow> lnat \<rightarrow> ('in \<times> 'out)" where
"simpleComp_lnat = (\<Lambda> f g. fix\<cdot>(\<Lambda> prev ln. (g\<cdot>(snd ((strictify\<cdot>prev)\<cdot>(lnpred\<cdot>ln))), f\<cdot>(fst (((strictify\<cdot>prev)\<cdot>(lnpred\<cdot>ln)))))))"

(* SSt: In der Hoffnung, dass man so Induktion verwenden kann (über lnat) *)
definition simpleComp_lnat2::"('in::pcpo\<times>lnat \<rightarrow> 'out::pcpo) \<rightarrow> ('out\<times>lnat \<rightarrow> 'in) \<rightarrow> lnat \<rightarrow> ('in \<times> 'out)" where
"simpleComp_lnat2 = (\<Lambda> f g. fix\<cdot>(\<Lambda> prev ln. (g\<cdot>(snd ((strictify\<cdot>prev)\<cdot>(lnpred\<cdot>ln)), ln), f\<cdot>(fst (((strictify\<cdot>prev)\<cdot>(lnpred\<cdot>ln))),ln))))"

lemma simplecomp_lnat_unfold:"simpleComp_lnat\<cdot>f\<cdot>g\<cdot>ln = 
  (g\<cdot>(snd ((strictify\<cdot>(simpleComp_lnat\<cdot>f\<cdot>g))\<cdot>(lnpred\<cdot>ln))), f\<cdot>(fst (((strictify\<cdot>(simpleComp_lnat\<cdot>f\<cdot>g))\<cdot>(lnpred\<cdot>ln)))))"
  unfolding simpleComp_lnat_def
  apply(subst beta_cfun, intro cont2cont)+
  apply(subst fix_eq)
  apply(subst beta_cfun, intro cont2cont)+
  by simp

lemma simplecomp_lnat_bot[simp]: "simpleComp_lnat\<cdot>f\<cdot>g\<cdot>\<bottom> = (g\<cdot>\<bottom>,f\<cdot>\<bottom>)"
  apply(subst simplecomp_lnat_unfold)
  by simp
lemma simplecomp_lnat_zero[simp]: "simpleComp_lnat\<cdot>f\<cdot>g\<cdot>0 = (g\<cdot>\<bottom>,f\<cdot>\<bottom>)"
  by (simp add: lnzero_def)

lemma simplecomp_lnat_step: "simpleComp_lnat\<cdot>f\<cdot>g\<cdot>(lnsuc\<cdot>ln) = (g\<cdot>(snd (strictify\<cdot>(simpleComp_lnat\<cdot>f\<cdot>g)\<cdot>ln)), f\<cdot>(fst (strictify\<cdot>(simpleComp_lnat\<cdot>f\<cdot>g)\<cdot>ln)))"
  apply(subst simplecomp_lnat_unfold)
  by simp


lemma simplecomp_lnat2_unfold:"simpleComp_lnat2\<cdot>f\<cdot>g\<cdot>ln = 
  (g\<cdot>(snd (((strictify\<cdot>(simpleComp_lnat2\<cdot>f\<cdot>g)))\<cdot>(lnpred\<cdot>ln)), ln), f\<cdot>(fst (((strictify\<cdot>(simpleComp_lnat2\<cdot>f\<cdot>g))\<cdot>(lnpred\<cdot>ln))), ln))"
  unfolding simpleComp_lnat2_def
  apply(subst beta_cfun, intro cont2cont)+
  apply(subst fix_eq)
  apply(subst beta_cfun, intro cont2cont)+
  by simp

lemma simplecomp_lnat2_bot[simp]: "simpleComp_lnat2\<cdot>f\<cdot>g\<cdot>\<bottom> = (g\<cdot>(\<bottom>,\<bottom>),f\<cdot>(\<bottom>,\<bottom>))"
  by(subst simplecomp_lnat2_unfold, simp)
lemma simplecomp_lnat2_step: "simpleComp_lnat2\<cdot>f\<cdot>g\<cdot>(lnsuc\<cdot>ln) = (g\<cdot>(snd (strictify\<cdot>(simpleComp_lnat2\<cdot>f\<cdot>g)\<cdot>ln), lnsuc\<cdot>ln), f\<cdot>(fst (strictify\<cdot>(simpleComp_lnat2\<cdot>f\<cdot>g)\<cdot>ln), lnsuc\<cdot>ln))"
  apply(subst simplecomp_lnat2_unfold)
  by simp



lemma simpcomp_lnat_to_normal: "simpleComp_lnat\<cdot>f\<cdot>g\<cdot>\<infinity> = simpleComp\<cdot>f\<cdot>g"
  oops  
*)


definition SimpleComp::"('in::pcpo \<rightarrow> 'out::pcpo) set \<Rightarrow> ('out \<rightarrow> 'in) set \<Rightarrow> ('in \<times> 'out) set" where
"SimpleComp = (\<lambda> F G . {simpleComp\<cdot>f\<cdot>g | f g. 
                                f \<in> F \<and> g \<in> G})"
(*
definition SimpleComp_gfp::"('in::pcpo \<rightarrow> 'out::pcpo) set \<Rightarrow> ('out \<rightarrow> 'in) set \<Rightarrow> ('in \<times> 'out) set" where
"SimpleComp_gfp F G = gfp (\<lambda> S. { (g\<cdot>b, f\<cdot>a) | f g a b. f\<in>F \<and> g\<in>G \<and> (a,b)\<in>S})"

lemma simplecomp_gfp_mono: "mono (\<lambda> S. { (g\<cdot>b, f\<cdot>a) | f g a b. f\<in>F \<and> g\<in>G \<and> (a,b)\<in>S})"
  apply(rule monoI)
  by blast

lemma "SimpleComp F G \<subseteq> SimpleComp_gfp F G"
  unfolding SimpleComp_def SimpleComp_gfp_def
  apply(rule gfp_upperbound)
  apply(subst simplecomp_unfold)
  apply auto
  using prod.collapse by blast

lemma "SimpleComp_gfp F G \<subseteq> SimpleComp F G"
  unfolding SimpleComp_def SimpleComp_gfp_def
  apply(rule gfp_least)
  apply auto
  oops (* SSt: Das sollte nicht gelten (denke ich) *)

lemma assumes "(a,b) \<in> SimpleComp_gfp F G"
  shows "\<exists>f. f\<in>F \<and> f\<cdot>a=b"
  apply(insert assms)
  apply(subst (asm) SimpleComp_gfp_def; subst (asm) gfp_unfold)
  apply (simp add: simplecomp_gfp_mono)
  apply(subst (asm) SimpleComp_gfp_def [symmetric])
  apply auto
  oops
*)


(*
lemma "x \<in> SimpleComp F G \<Longrightarrow> (\<exists>f g. (f \<in>F \<and> g\<in> G \<and> (f\<cdot>(g\<cdot>x) = x)))"
  unfolding SimpleComp_def simpleComp_def
  apply(subst (asm) beta_cfun, intro cont2cont)+
  using fix_eq4 by force
*)


end