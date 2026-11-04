theory eventMerge

imports stream.eventStream 
begin

default_sort countable

lemma mono2monofun: fixes f::"'a::type set \<Rightarrow> 'a set" shows "monofun f \<longleftrightarrow> mono f"
  by(simp add: mono_def monofun_def less_set_def)



(* datatype 'a event = Event 'a | Tick

instance event :: (countable) countable
  by(countable_datatype)
*)

text\<open>Liste der Sachen, die Scheiße/Falsch sind:
\<^item> Reihenfolge der Quantoren. Ist (glaube ich) nur ein kleiner Fehler. Zwar ist es eine echte Teilmenge
  zu der "gewünschten" Spezifikation, aber \<open>spsComplete\<close> kann es fixen.
  \<^item> original: \<open>\<exists>merge2. \<forall>xs,ys.   \<forall>a\<in>M.\<close>
  \<^item> besser:   \<open>\<forall>a\<in>M.    \<exists>merge2.  \<forall>xs,ys.\<close>
\<^item> Das der \<open>\<epsilon>\<close> Fall nicht draufsteht ist nervig
  \<^item> Begründung Rumpe: "Specifications are monotonic, and such no need to explicitly specify reaction on \<open>\<epsilon>\<close> here"
  \<^item> Stimmt ja auch, aber wäre schon interessant! 
    Oder weißt du, geneigter Leser, was die Ausgabe von \<open>merge \<epsilon> (Event a)\<close> ist?
    (Nicht was sie sein SOLLTE... sondern was alles möglich ist?)
\<^item> Die konstruktive Art die Eingabe zu bauen! Und das noch abgekürzt! Das ist ein echter Fehler (denke ich)
\<close>


definition br_merge_pred:: "(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set
  \<Rightarrow> (('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) \<Rightarrow> bool" where
"br_merge_pred Merge merge \<equiv> \<exists>merge2. merge2\<in>Merge \<and> 
                            (\<forall>xs::'M event stream. 
                             \<forall>ys::'M event stream. 
                             \<forall>a ::'M .  
                                merge\<cdot>(\<up>Tick    \<Zcat> xs, \<up>Tick    \<Zcat> ys) = \<up>Tick \<Zcat> merge2\<cdot>(xs,ys)  \<and> (
                                  merge\<cdot>(\<up>(Event a) \<Zcat> xs,            ys) = \<up>(Event a) \<Zcat> merge2\<cdot>(xs,ys) \<or>
                                  merge\<cdot>(           xs,\<up>(Event a) \<Zcat>  ys) = \<up>(Event a) \<Zcat> merge2\<cdot>(xs,ys)
                            ) )"

definition br_merge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set
                    \<Rightarrow> (('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set" where
"br_merge Merge = {merge | merge.  br_merge_pred Merge merge}"

lemma br_monofun: "monofun br_merge"
  apply(rule monofunI, auto simp add: br_merge_def br_merge_pred_def less_set_def)
  by (meson subset_iff)?

lemma br_mono: "mono br_merge"
  using mono2monofun br_monofun by blast

definition brMerge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set" where
"brMerge = gfp br_merge"


definition errorMerge::"('M event stream\<times>'M event stream) \<rightarrow> 'M event stream" where
"errorMerge \<equiv> \<Lambda>(s1, s2). s1"

lemma error_step: assumes "errorMerge \<in> M"
  shows "br_merge_pred M errorMerge"
  apply(simp add: br_merge_pred_def)
  apply(rule exI [of _ errorMerge])
  apply(auto simp add: assms errorMerge_def)
  by (metis assms errorMerge_def)

theorem "errorMerge \<in> brMerge"
  apply(subst brMerge_def)
  apply(rule weak_coinduct [of _  "{errorMerge}"])
   apply simp
  by (simp add: error_step br_merge_def)






definition stepMerge_pred:: "(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set
  \<Rightarrow> (('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) \<Rightarrow> bool" where
"stepMerge_pred Merge merge \<equiv> \<forall>x ::'M. \<forall>y ::'M . 
         \<exists>merge2. merge2\<in>Merge \<and> 
        (\<forall>xs::'M event stream. 
         \<forall>ys::'M event stream. 
            merge\<cdot>(\<up>Tick    \<Zcat> xs,\<up>Tick    \<Zcat>  ys) = \<up>Tick    \<Zcat> merge2\<cdot>(xs,ys)  \<and> 
            merge\<cdot>(\<up>Tick    \<Zcat> xs,\<up>(Event y) \<Zcat>  ys) = \<up>(Event y) \<Zcat> merge2\<cdot>(\<up>Tick \<Zcat> xs,ys)\<and>
            merge\<cdot>(\<up>(Event x) \<Zcat> xs,\<up>Tick    \<Zcat>  ys) = \<up>(Event x) \<Zcat> merge2\<cdot>(xs,\<up>Tick \<Zcat> ys)  \<and>(
              merge\<cdot>(\<up>(Event x) \<Zcat> xs,\<up>(Event y) \<Zcat>  ys) = \<up>(Event x) \<Zcat> merge2\<cdot>(xs,\<up>(Event y) \<Zcat> ys) \<or>
              merge\<cdot>(\<up>(Event x) \<Zcat> xs,\<up>(Event y) \<Zcat>  ys) = \<up>(Event y) \<Zcat> merge2\<cdot>(\<up>(Event x) \<Zcat> xs,ys)
        ) )"

definition stepMerge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set 
                    \<Rightarrow> (('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set" where
"stepMerge Merge = {merge | merge.  stepMerge_pred Merge merge}"

lemma sm_monofun: "monofun stepMerge"
  apply(rule monofunI, auto simp add: stepMerge_def stepMerge_pred_def less_set_def)
  by (meson subset_iff)

lemma sm_mono[simp]: "mono stepMerge"
  using mono2monofun sm_monofun by blast

definition myMerge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) set" where
"myMerge = gfp stepMerge"





fun fstTransition::"('M event\<times>'M event) \<Rightarrow> ('M event stream \<times> 'M event stream) \<Rightarrow>
  ('M event \<times> ('M event stream \<times> 'M event stream))" where
"fstTransition (Tick, Tick) (xs, ys) = (Tick, xs, ys)" |
"fstTransition (Tick, Event y) (xs, ys) = (Event y, \<up>Tick \<Zcat> xs, ys)" |
"fstTransition (Event x, Tick) (xs, ys) = (Event x, xs, \<up>Tick \<Zcat> ys)" |
"fstTransition (Event x, Event y) (xs, ys) = (Event x, xs, \<up>(Event y) \<Zcat> ys)"

definition fstTransition_cont::"('M event discr \<times>'M event discr) \<rightarrow> ('M event stream \<times> 'M event stream) \<rightarrow>
  ('M event discr \<times> ('M event stream \<times> 'M event stream))" where 
"fstTransition_cont \<equiv> \<Lambda> (input1, input2) rest. apfst Discr (fstTransition (undiscr input1, undiscr input2) rest)"

lemma fstTransition_insert:
"fstTransition_cont\<cdot>(input1, input2)\<cdot>rest = apfst Discr (fstTransition (undiscr input1, undiscr input2) rest)"
  apply(simp add: fstTransition_cont_def)
  apply(rule beta_cfun)
   apply(cases input1; rename_tac x1; case_tac x1; cases input2; rename_tac x2; case_tac x2; simp)
      apply(subst(4) surjective_pairing; simp only: fstTransition.simps; simp )+
  done

fixrec onefstMerge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) \<rightarrow>('M event stream\<times>'M event stream) \<rightarrow> 'M event stream" where
"onefstMerge\<cdot>f\<cdot>((up\<cdot>X && xs), (up\<cdot>Y && ys)) =
  (let (output, nextInput) = fstTransition_cont\<cdot>(X,Y)\<cdot>(xs,ys)
   in (up\<cdot>output) && f\<cdot>nextInput)"

lemma onefstmerge_pred: "f\<in>A \<Longrightarrow> stepMerge_pred A (onefstMerge\<cdot>f)"
  by(auto simp add: stepMerge_pred_def fstTransition_insert lscons_conv[symmetric])
  
lemma oneMerge_in [simp]: "f\<in>myMerge \<Longrightarrow> onefstMerge\<cdot>f\<in>myMerge"
    apply(subst myMerge_def,subst gfp_fixpoint [symmetric], simp, subst stepMerge_def)
  by (simp add: onefstmerge_pred myMerge_def)



fun sndTransition::"('M event\<times>'M event) \<Rightarrow> ('M event stream \<times> 'M event stream) \<Rightarrow>
  ('M event \<times> ('M event stream \<times> 'M event stream))" where
"sndTransition (Tick, Tick) (xs, ys) = (Tick, xs, ys)" |
"sndTransition (Tick, Event y) (xs, ys) = (Event y, \<up>Tick \<Zcat> xs, ys)" |
"sndTransition (Event x, Tick) (xs, ys) = (Event x, xs, \<up>Tick \<Zcat> ys)" |
"sndTransition (Event x, Event y) (xs, ys) = (Event y, \<up>(Event x) \<Zcat> xs, ys)"

definition sndTransition_cont::"('M event discr \<times>'M event discr) \<rightarrow> ('M event stream \<times> 'M event stream) \<rightarrow>
  ('M event discr \<times> ('M event stream \<times> 'M event stream))" where 
"sndTransition_cont \<equiv> \<Lambda> (input1, input2) rest. apfst Discr (sndTransition (undiscr input1, undiscr input2) rest)"

lemma sndTransition_insert:
"sndTransition_cont\<cdot>(input1, input2)\<cdot>rest = apfst Discr (sndTransition (undiscr input1, undiscr input2) rest)"
  apply(simp add: sndTransition_cont_def)
  apply(rule beta_cfun)
   apply(cases input1; rename_tac x1; case_tac x1; cases input2; rename_tac x2; case_tac x2; simp)
      apply(subst(4) surjective_pairing; simp only: sndTransition.simps; simp )+
  done

fixrec onesndMerge::"(('M event stream\<times>'M event stream) \<rightarrow> 'M event stream) \<rightarrow>('M event stream\<times>'M event stream) \<rightarrow> 'M event stream" where
"onesndMerge\<cdot>f\<cdot>((up\<cdot>X && xs), (up\<cdot>Y && ys)) =
  (let (output, nextInput) = sndTransition_cont\<cdot>(X,Y)\<cdot>(xs,ys)
   in (up\<cdot>output) && f\<cdot>nextInput)"

lemma onesndmerge_pred: "f\<in>A \<Longrightarrow> stepMerge_pred A (onesndMerge\<cdot>f)"
  by(auto simp add: stepMerge_pred_def sndTransition_insert lscons_conv[symmetric])
  
lemma onesndmerge_in [simp]: "f\<in>myMerge \<Longrightarrow> onesndMerge\<cdot>f\<in>myMerge"
    apply(subst myMerge_def,subst gfp_fixpoint [symmetric], simp, subst stepMerge_def)
  by (simp add: onesndmerge_pred myMerge_def)





theorem fst_in: "fix\<cdot>onefstMerge \<in> myMerge"
  apply(subst myMerge_def)
  apply(rule weak_coinduct [of _  "{fix\<cdot>onefstMerge}"])
  apply (auto simp add: stepMerge_def)
  apply(subst (2) fix_eq)
  apply(rule onefstmerge_pred)
  by simp

theorem mymerge_nempty [simp]: "myMerge \<noteq> {}"
  using fst_in by blast

theorem merge_event_event: assumes "f\<in>myMerge"
  shows "\<exists>f2 \<in> myMerge. 
      f\<cdot>(\<up>(Event m) \<Zcat> xs, \<up>(Event n) \<Zcat> ys) = \<up>(Event m) \<Zcat> f2\<cdot>(xs, \<up>(Event n) \<Zcat> ys)
    \<or> f\<cdot>(\<up>(Event m) \<Zcat> xs, \<up>(Event n) \<Zcat> ys) = \<up>(Event n) \<Zcat> f2\<cdot>(\<up>(Event m) \<Zcat> xs, ys)"
  apply(insert assms, simp add: myMerge_def)
  apply(subst (asm) gfp_unfold, simp)
  apply(auto simp add: stepMerge_def stepMerge_pred_def myMerge_def[symmetric])
  by blast

theorem merge_event_tick: assumes "f\<in>myMerge"
  shows "\<exists>f2 \<in> myMerge. f\<cdot>(\<up>(Event m) \<Zcat> xs, \<up>Tick \<Zcat> ys) = \<up>(Event m) \<Zcat> f2\<cdot>(xs, \<up>Tick \<Zcat> ys)"
  apply(insert assms, simp add: myMerge_def)
  apply(subst (asm) gfp_unfold, simp)
  apply(auto simp add: stepMerge_def stepMerge_pred_def myMerge_def[symmetric])
  by blast

theorem merge_tick_event: assumes "f\<in>myMerge"
  shows "\<exists>f2 \<in> myMerge. f\<cdot>(\<up>Tick \<Zcat> xs, \<up>(Event m) \<Zcat> ys) = \<up>(Event m) \<Zcat> f2\<cdot>(\<up>Tick \<Zcat> xs, ys)"
  apply(insert assms, simp add: myMerge_def)
  apply(subst (asm) gfp_unfold, simp)
  apply(auto simp add: stepMerge_def stepMerge_pred_def myMerge_def[symmetric])
  by blast

lemma merge_tick_tick: assumes "f\<in>myMerge"
  shows "\<exists>f2 \<in> myMerge. f\<cdot>(\<up>Tick \<Zcat> input1, \<up>Tick \<Zcat> input2) = \<up>Tick \<Zcat> f2\<cdot>(input1, input2)"
    apply(insert assms, simp add: myMerge_def)
  apply(subst (asm) gfp_unfold, simp)
  apply(auto simp add: stepMerge_def stepMerge_pred_def myMerge_def[symmetric])
  by blast

lemma merge_shd_eq: assumes "f\<in>myMerge"
  shows "shd (f\<cdot>(\<up>m \<Zcat> input1, \<up>m \<Zcat> input2)) = m"
    apply(insert assms, simp add: myMerge_def)
  apply(subst (asm) gfp_unfold, simp)
  apply(auto simp add: stepMerge_def stepMerge_pred_def myMerge_def[symmetric])
  apply(cases m, auto)
  apply (metis shd1)+
  done

lemma merge_eps_eps[simp]: assumes "f\<in>myMerge"
  shows "f\<cdot>(\<epsilon>, \<epsilon>) = \<epsilon>"
proof(rule ccontr)
  assume a:"f\<cdot>(\<epsilon>, \<epsilon>) \<noteq> \<epsilon>"
  let ?fstOut = "shd (f\<cdot>(\<epsilon>, \<epsilon>))"
  obtain otherElem where other_def: "otherElem \<noteq> ?fstOut" 
    by(cases ?fstOut, auto)
  have "shd (f\<cdot>(\<up>otherElem, \<up>otherElem)) = otherElem"
    by (metis assms merge_shd_eq sconc_snd_empty)
  moreover have "(\<epsilon>, \<epsilon>) \<sqsubseteq> (\<up>otherElem, \<up>otherElem)" by auto
  thus False 
    by (metis a below_shd_alt calculation monofun_cfun_arg other_def)
qed

lemma merge_eps_event: assumes "f\<in>myMerge"
  shows "(\<exists>f2 \<in> myMerge. f\<cdot>(\<epsilon>, \<up>(Event m) \<Zcat> input2) = \<up>(Event m) \<Zcat> f2\<cdot>(\<epsilon>, input2))
        \<or> f\<cdot>(\<epsilon>, \<up>(Event m) \<Zcat> input2) = \<epsilon>"
proof(rule ccontr, auto)
  assume *:"\<forall>f2\<in>myMerge. f\<cdot>(\<epsilon>, \<up>(Event m) \<Zcat> input2) \<noteq> \<up>(Event m) \<Zcat> f2\<cdot>(\<epsilon>, input2)"
    and **:"f\<cdot>(\<epsilon>, \<up>(Event m) \<Zcat> input2) \<noteq> \<epsilon>"
  have "shd (f\<cdot>(\<epsilon>, \<up>(Event m) \<Zcat> input2)) \<noteq> Event m"
    using * ** apply auto oops

lemma mymerge_eps_tick: assumes"f \<in> myMerge"
  shows" f\<cdot>(\<epsilon>,\<up>Tick \<Zcat> input) = \<epsilon>"
proof (rule ccontr)
  fix s::"'a event stream" and a::"'a event"
  assume a2:"f\<cdot>(\<epsilon>, \<up>Tick \<Zcat> s) \<noteq> \<epsilon>"
  then obtain x xs where x_def: "\<up>x \<Zcat> xs = f\<cdot>(\<epsilon>, \<up>Tick \<Zcat> s)"
    by (metis streamcases)
  have h:"\<And>y ys. \<up>x \<Zcat> xs \<sqsubseteq> f\<cdot>(\<up>y \<Zcat> ys, \<up>Tick \<Zcat> s)"
    by(simp add: x_def monofun_cfun_arg)
  have "\<exists>f2\<in>myMerge. f\<cdot>(\<up>Tick, \<up>Tick \<Zcat> s) = \<up>Tick \<Zcat> f2\<cdot>(\<epsilon>,s)"
    using merge_tick_tick[of f \<epsilon> s] assms by simp
  hence h1: "x = Tick"
    using x_def h by (metis less_all_sconsD sconc_snd_empty)
  have "\<And>y. \<exists>f2\<in>myMerge. f\<cdot>(\<up>(Event y), \<up>Tick \<Zcat> s) = \<up>(Event y) \<Zcat> f2\<cdot>(\<epsilon>,\<up>Tick \<Zcat> s)"
    using merge_event_tick assms by (metis sconc_snd_empty)
  hence "\<exists>y. x= (Event y)"
    using x_def h by (metis less_all_sconsD sconc_snd_empty)
  thus "False"
    using h1 by simp
qed

lemma mymerge_tick_eps: assumes"f \<in> myMerge"
  shows" f\<cdot>(\<up>Tick \<Zcat> input,\<epsilon>) = \<epsilon>"
proof(rule ccontr)
  fix s::"'a event stream" and a::"'a event"
  assume a2:"f\<cdot>(\<up>Tick \<Zcat> s,\<epsilon>) \<noteq> \<epsilon>"
  then obtain x xs where x_def: "\<up>x \<Zcat> xs = f\<cdot>(\<up>Tick \<Zcat> s,\<epsilon>)"
    by (metis streamcases)
  have h:"\<And>y ys. \<up>x \<Zcat> xs \<sqsubseteq> f\<cdot>(\<up>Tick \<Zcat> s,\<up>y \<Zcat> ys)"
    by(simp add: x_def monofun_cfun_arg)
  have "\<exists>f2\<in>myMerge. f\<cdot>(\<up>Tick \<Zcat> s,\<up>Tick) = \<up>Tick \<Zcat> f2\<cdot>(s,\<epsilon>)"
    using merge_tick_tick[of f s \<epsilon>] assms by simp
  hence h1: "x = Tick"
    using x_def h by (metis less_all_sconsD sconc_snd_empty)
  have "\<And>y. \<exists>f2\<in>myMerge. f\<cdot>(\<up>Tick \<Zcat> s,\<up>(Event y)) = \<up>(Event y) \<Zcat> f2\<cdot>(\<up>Tick \<Zcat> s,\<epsilon>)"
    using merge_tick_event assms by (metis sconc_snd_empty)
  hence "\<exists>y. x= (Event y)"
    using x_def h by (metis less_all_sconsD sconc_snd_empty)
  thus "False"
    using h1 by simp
qed


lemma mymerge_eps_x: "f \<in> myMerge \<Longrightarrow> \<exists>f2\<in>myMerge. f\<cdot>(\<epsilon>,\<up>(Event a) \<Zcat> s) = \<up>(Event a) \<Zcat> f2\<cdot>(\<epsilon>,s)" 
  oops

theorem 
  assumes "merge\<cdot>(\<up>(Event m), \<epsilon>) = \<up>(Event m)" 
      and "merge\<cdot>(\<epsilon>, \<up>(Event n)) = \<up>(Event n)"
      and "merge\<cdot>(\<up>(Event m), \<up>(Event n)) = \<up>(Event n) \<Zcat> \<up>(Event m) 
         \<or> merge\<cdot>(\<up>(Event m), \<up>(Event n)) = \<up>(Event m) \<Zcat> \<up>(Event n)"
      and "m\<noteq>n"
    shows False
proof -
  have "(\<up>(Event m), \<epsilon>) \<sqsubseteq> (\<up>(Event m), \<up>(Event n))" by simp
  moreover have "\<not>(\<up>(Event m) \<sqsubseteq> \<up>(Event n) \<Zcat> \<up>(Event m))" by (simp add: assms)
  moreover have "\<not>(\<up>(Event n) \<sqsubseteq> \<up>(Event m) \<Zcat> \<up>(Event n))" using assms(4) by auto
  moreover have "monofun (Rep_cfun merge)" by (simp add: monofunI monofun_cfun_arg) 
  ultimately show False using assms monofun_def
    by (metis (no_types, lifting) Pair_below_iff less_all_sconsD sconc_prefix sconc_snd_empty)
qed






definition relMerge::"('M event stream\<times>'M event stream) \<Rightarrow> ('M event stream set)" where
"relMerge input = {spf\<cdot>input | spf. spf\<in>myMerge}"

lemma mymerge_tick_tick: "f \<in> myMerge \<Longrightarrow> \<exists>f2. f2\<in>myMerge \<and> \<up>Tick \<Zcat> f\<cdot>(input1, input2) = f2\<cdot>(\<up>Tick \<Zcat> input1, \<up>Tick \<Zcat> input2)"
  apply(rule exI [where x="onefstMerge\<cdot>f"])
  by(auto simp add: fstTransition_insert lscons_conv[symmetric])

lemma mymerge_event_tick: "f \<in> myMerge \<Longrightarrow> \<exists>f2. f2\<in>myMerge \<and> \<up>(Event m) \<Zcat> f\<cdot>(input1,  \<up>Tick \<Zcat> input2) = f2\<cdot>(\<up>(Event m) \<Zcat> input1, \<up>Tick \<Zcat> input2)"
  apply(rule exI [where x="onefstMerge\<cdot>f"])
  by(auto simp add: fstTransition_insert lscons_conv[symmetric])

lemma mymerge_tick_event: "f \<in> myMerge \<Longrightarrow> \<exists>f2. f2\<in>myMerge \<and> \<up>(Event m) \<Zcat> f\<cdot>( \<up>Tick \<Zcat> input1, input2) = f2\<cdot>( \<up>Tick \<Zcat> input1, \<up>(Event m) \<Zcat>input2)"
  apply(rule exI [where x="onefstMerge\<cdot>f"])
  by(auto simp add: fstTransition_insert lscons_conv[symmetric])

lemma mymerge_event_event_fst: "f \<in> myMerge \<Longrightarrow> \<exists>f2. f2\<in>myMerge \<and> \<up>(Event i1) \<Zcat> f\<cdot>(input1,  \<up>(Event i2) \<Zcat> input2) = f2\<cdot>(\<up>(Event i1) \<Zcat> input1, \<up>(Event i2) \<Zcat>input2)"
  apply(rule exI [where x="onefstMerge\<cdot>f"])
  by(auto simp add: fstTransition_insert lscons_conv[symmetric])

lemma mymerge_event_event_snd: "f \<in> myMerge \<Longrightarrow> \<exists>f2. f2\<in>myMerge \<and> \<up>(Event i2) \<Zcat> f\<cdot>(\<up>(Event i1) \<Zcat> input1,  input2) = f2\<cdot>(\<up>(Event i1) \<Zcat> input1, \<up>(Event i2) \<Zcat>input2)"
  apply(rule exI [where x="onesndMerge\<cdot>f"])
  by(auto simp add: sndTransition_insert lscons_conv[symmetric])



lemma relmerge_eps_eps [simp]: "relMerge (\<epsilon>,\<epsilon>) = {\<epsilon>}"
  using merge_eps_eps apply(auto simp add: relMerge_def)
  using fst_in  by blast

lemma relmerge_tick_eps[simp]: "relMerge (\<up>Tick \<Zcat> input1, \<epsilon>) = {\<epsilon>}"
  apply(auto simp add: relMerge_def)
  using mymerge_tick_eps fst_in by blast+

lemma relmerge_eps_tick[simp]: "relMerge ( \<epsilon>, \<up>Tick \<Zcat> input) = {\<epsilon>}"
  apply(auto simp add: relMerge_def)
  using mymerge_eps_tick fst_in by blast+

lemma relmerge_tick_tick[simp]: "relMerge (\<up>Tick \<Zcat> input1, \<up>Tick \<Zcat> input2) = {\<up>Tick \<Zcat> rest | rest. rest \<in> relMerge (input1, input2)}"
  apply(auto simp add: relMerge_def)
  using merge_tick_tick mymerge_tick_tick by blast+

  corollary relmerge_tick_tick2 [simp]: "relMerge (\<up>Tick, \<up>Tick) = {\<up>Tick}"
    apply(subst sconc_snd_empty[symmetric])
    apply(subst(4) sconc_snd_empty[symmetric])
    apply(simp only: relmerge_tick_tick)
    using relmerge_eps_eps by auto


lemma relmerge_event_tick[simp]: "relMerge (\<up>(Event m) \<Zcat> input1, \<up>Tick \<Zcat> input2) = {\<up>(Event m) \<Zcat> rest | rest. rest \<in> relMerge (input1,  \<up>Tick \<Zcat> input2)}"
  apply(auto simp add: relMerge_def)
  using merge_event_tick mymerge_event_tick by blast+

lemma relmerge_tick_event[simp]: "relMerge (\<up>Tick \<Zcat> input1, \<up>(Event m) \<Zcat> input2) = {\<up>(Event m) \<Zcat> rest | rest. rest \<in> relMerge (\<up>Tick \<Zcat> input1,  input2)}"
  apply(auto simp add: relMerge_def)
  using merge_tick_event mymerge_tick_event by blast+

lemma relmerge_event_event[simp]: "relMerge (\<up>(Event i1) \<Zcat> input1, \<up>(Event i2) \<Zcat> input2) = 
    {\<up>(Event i1) \<Zcat> rest | rest. rest \<in> relMerge (input1,   \<up>(Event i2) \<Zcat> input2)}
  \<union> {\<up>(Event i2) \<Zcat> rest | rest. rest \<in> relMerge (\<up>(Event i1) \<Zcat> input1,   input2)}"
  apply(auto simp add: relMerge_def)
  using merge_event_event mymerge_event_event_fst mymerge_event_event_snd by blast+


lemmas relMerge_step = relmerge_tick_tick and relmerge_event_tick and relmerge_tick_event
 and relmerge_event_event and relmerge_eps_eps and relmerge_tick_tick2


theorem "(\<exists>spf\<in>myMerge. spf\<cdot>input = output) \<longleftrightarrow> output\<in>relMerge input"
  by(auto simp add: relMerge_def)

lemma relMergeI: "output\<in>relMerge input \<Longrightarrow> (\<exists>spf\<in>myMerge. spf\<cdot>input = output)"
  by(auto simp add: relMerge_def)

lemma relMergNotIn: "output\<notin>relMerge input \<Longrightarrow> (\<forall>spf\<in>myMerge. spf\<cdot>input \<noteq> output)"
  by(auto simp add: relMerge_def)


end