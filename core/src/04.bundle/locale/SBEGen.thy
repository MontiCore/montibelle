theory SBEGen

imports bundle.SBFin stream.StreamAutomaton
begin

                                                       text\<open>\label{sub:sblocals}\<close>

text\<open>This section introduces two locales. Both locales use constructor
functions to define bijective mappings. The first locale provides a
bijektive constructor for @{type sbElem}s and an injective one for 
\glspl{sb}. The second locale only provides a bijektive constructor
for \glspl{sb}. The intention of these locales is the usage of
generated constructors that fulfill the locales assumptions and then
provide the pleasant options to define a \gls{sb} with a tuple
stream or a tuple of streams. Furthermore, these constructors can
later be used to hide the \gls{sb} level completely when evaluating
automatons on a bundle constructed by a tuple stream. In the 
following we will refer to setters and getters, where setters 
construct @{type sbElem}s or \glspl{sb} and getters destruct them to
their original type.\<close> 




text\<open>The first locale provides two mappings. The fist one maps some
type \<open>'a\<close> to a @{type sbElem}. The second one maps a @{type stream} 
of type \<open>'a\<close> to a \gls{sb}. For example could a \gls{sb} setter map
a \<open>nat\<times>bool\<close> @{type stream} to a \gls{sb} with a \<open>nat\<close> and a \<open>bool\<close>
stream. The constructor mapping is always injective, but in general 
not surjective.\<close>

text\<open>The locales assumptions depend on the constructors domain.
If the domain is empty, \<open>'a\<close> must be a singleton, else, the
constructor has to map to a function that can be interpreted as a 
@{type sbElem}. The constructor also has to map to every 
possible @{type sbElem} and be injective.\<close>

locale sbeGen =
  fixes lConstructor::"'a::countable \<Rightarrow> 'cs::{chan, finite} \<Rightarrow> M"
  assumes c_well: "\<And>a. \<not>chDomEmpty TYPE ('cs) 
                        \<Longrightarrow> \<forall>c. lConstructor a c \<in> ctype(Rep c)"
      and c_inj: "\<not>chDomEmpty TYPE ('cs) \<Longrightarrow> inj lConstructor" 
      and c_surj: "\<And>sbe. \<not>chDomEmpty TYPE ('cs) 
                        \<Longrightarrow> \<forall>c. sbe c \<in> ctype(Rep c)
                        \<Longrightarrow> sbe\<in>range lConstructor"
      and c_empty: "chDomEmpty TYPE ('cs) 
                        \<Longrightarrow> is_singleton(UNIV::'a set)"
begin


lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is 
"if chDomEmpty TYPE ('cs) then (\<lambda>_. None) else Some o lConstructor"
  using c_well sbtypeempty_sbewell by auto


text\<open>The getter work analogous with the inverse constructor. If the
input @{type sbElem} is \<open>None\<close>, we know that the domain \<open>'cs\<close> is 
empty and hence, the type \<open>'a\<close> only contains one element. Therefore,
@{const undefined} can be returned.\<close>

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter sbe \<equiv> case (Rep_sbElem sbe) of 
        None   \<Rightarrow> undefined        | 
        Some f \<Rightarrow> (inv lConstructor) f"


theorem get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  apply (simp add: setter.rep_eq c_inj c_empty)
  by (metis (full_types)UNIV_I c_empty is_singletonE singleton_iff)

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
  apply(cases "\<not>(chDomEmpty(TYPE('cs)))",auto)
  apply(simp add: chDom_def)
  apply auto[1]
proof-
  fix xb::"'cs\<^sup>\<surd>" and xa::'cs
  assume chnEmpty:"Rep xa \<notin> cEmpty"
  obtain f where f_def:"Rep_sbElem xb=(Some f)"
    using chnEmpty cempty_rule sbenotnone2 by blast
  then obtain x where x_def:"f = lConstructor x"
    by (metis (no_types) chnEmpty c_surj empty_iff imageE 
        notcdom_empty sbElem_well.simps(2) sbelemwell2fwell)
  then show "xb\<in>range (\<lambda>x::'a. Abs_sbElem (Some (lConstructor x)))"
    by (metis (no_types,lifting) Rep_sbElem_inverse f_def range_eqI)
qed 

lemma set_bij: "bij setter"
  by (metis bijI inj_onI sbeGen.get_set sbeGen_axioms set_surj)

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)


theorem set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)

lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)

lemma ind[case_names adm least sbeCons, induct type: sb]:
  fixes   x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
  and     "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
  and     "\<And>sbe sb. P sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) 
           \<Longrightarrow> P (setter sbe \<Zcat>\<^sup>\<surd> sb)"   
  shows   "P x"
  apply(induction x, auto simp add: assms)
  using assms(2) sbnleast_len sbhdelemnotempty apply auto[2]
  by (metis assms(3) emptyE set_get)

lemma setter_getch[simp]: "(Rep c) \<in> chDom TYPE ('cs) \<Longrightarrow> 
    sbegetch c (setter a) = lConstructor a (Abs (Rep c))"
  by (auto simp add: sbegetch_def setter.rep_eq)

lemma setter_sbe2sb_getch[simp]: "(Rep c) \<in> chDom TYPE ('cs) \<Longrightarrow> 
    sbe2sb (setter a) \<^enum>  c = \<up>(lConstructor a (Abs (Rep c)))"
  by (auto simp add: sbegetch_def setter.rep_eq sbe2sb.rep_eq 
      sbgetch_insert)


text\<open>These setter and getter functions for 
@{type sbElem}s can then be used to define setter and getter
functions for \glspl{sb}. Because we construct those \glspl{sb} 
purely by appending @{type sbElem}s, we can only construct a subset 
of all \glspl{sb}, where each stream has the same length.\<close>  

fixrec setterSB::"'a stream \<rightarrow> 'cs\<^sup>\<Omega>" where
"setterSB\<cdot>((up\<cdot>l)&&ls) = (setter (undiscr l)) \<Zcat>\<^sup>\<surd> (setterSB\<cdot>ls)" 


lemma settersb_unfold[simp]:
"setterSB\<cdot>(\<up>a \<Zcat> s) = (setter a) \<Zcat>\<^sup>\<surd> setterSB\<cdot>s"
  unfolding setterSB_def
  apply(subst fix_eq)
  apply simp 
  apply(subgoal_tac "\<exists>l. \<up>a \<Zcat> s = (up\<cdot>l)&&s")
  apply auto [1]
  apply (metis (no_types, lifting) lshd_updis stream.sel_rews(4) 
         undiscr_Discr up_inject)
  by (metis lscons_conv)

lemma settersb_emptyfix[simp]:
"chDomEmpty (TYPE ('cs)) \<Longrightarrow> setterSB\<cdot>s = \<bottom>"
  by simp

lemma settersb_strict[simp]:"setterSB\<cdot>\<epsilon> = \<bottom>"
  apply(simp add: setterSB_def)
  apply(subst fix_eq)
  by auto

definition getterSB::"'cs\<^sup>\<Omega> \<rightarrow> 'a stream" where
"getterSB \<equiv> fix\<cdot>(\<Lambda> h. sb_step\<cdot>
                (\<lambda>sbe. \<Lambda> sb. updis (getter sbe) && h\<cdot>sb))"

text\<open>The following theorems describe when @{const setterSB} and 
@{const getterSB} are behave inverse to each other.\<close>

lemma gettersb_unfold[simp]:
"getterSB\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = \<up>(getter sbe) \<Zcat> getterSB\<cdot>sb"
  unfolding getterSB_def
  apply(subst fix_eq)
  apply simp
  by (simp add: lscons_conv)

lemma gettersb_emptyfix:
  "chDomEmpty (TYPE ('cs)) 
  \<Longrightarrow> getterSB\<cdot>sb = \<up>(getter (Abs_sbElem None)) \<Zcat> getterSB\<cdot>sb"
  by (metis(full_types) gettersb_unfold sbtypeepmpty_sbbot)

lemma gettersb_empty_inf: "chDomEmpty (TYPE ('cs)) 
  \<Longrightarrow> getterSB\<cdot>sb = sinftimes (\<up>(getter (Abs_sbElem None)))"
  using gettersb_emptyfix s2sinftimes by blast

lemma gettersb_realboteps[simp]:
  "\<not>(chDomEmpty (TYPE ('cs))) \<Longrightarrow> getterSB\<cdot>\<bottom> = \<epsilon>"
  unfolding getterSB_def
  apply(subst fix_eq)
  by (simp)

lemma gettersb_boteps[simp]:
  "\<not>(chDomEmpty (TYPE ('cs))) \<Longrightarrow> sbIsLeast sb \<Longrightarrow> getterSB\<cdot>sb = \<epsilon>"
  unfolding getterSB_def
  apply(subst fix_eq)
  by (simp)

lemma gettersb_inftimes:
  assumes "chDomEmpty (TYPE ('cs))"
  shows "(getterSB\<cdot>sb) = (sinftimes(\<up>(a)))"
  apply(insert assms,subst gettersb_emptyfix,simp) 
  using gettersb_emptyfix s2sinftimes c_empty
  by (metis (mono_tags) get_set sbtypeepmpty_sbenone)

lemma gettersb_cont[simp]: "cont (\<lambda> h. sb_step\<cdot>
                (\<lambda>sbe. \<Lambda> sb. updis (getter sbe) && h\<cdot>sb))"
  by simp

lemma sbLen_setterSB_h: "\<not>chDomEmpty TYPE('cs) \<Longrightarrow> #(setterSB\<cdot>s \<^enum> c) = #s"
  apply(induction s)
  apply(simp add:  len_stream_def)
  by simp_all 

lemma sbLen_setterSB: "\<not>chDomEmpty TYPE('cs) \<Longrightarrow> # (setterSB\<cdot>s) = #s"
  apply (rule  sblen_rule, simp)
   defer
  apply (simp add:  sbLen_setterSB_h)
proof (induction s)
  case adm
  then show ?case 
    apply simp
    using  adm_imp
    by (simp add:  sbLen_setterSB_h)
next
case bottom
  then show ?case 
    by simp
next
  case (step a s)
  then show ?case
    by (metis  sbLen_setterSB_h order_refl)
qed

lemma "a \<sqsubseteq> getterSB\<cdot>(setterSB\<cdot>a)"
  apply(induction a)
  apply(auto)[2]
  by (simp add: monofun_cfun_arg)

theorem getset_eq[simp]:
  assumes "\<not>chDomEmpty (TYPE ('cs))"
  shows   "getterSB\<cdot>(setterSB\<cdot>a) = a"
  apply(induction a)
  using assms by auto

lemma getset_below: "setterSB\<cdot>(getterSB\<cdot>sb) \<sqsubseteq> sb"
  apply(induction sb,simp)
  apply(cases "chDomEmpty(TYPE('cs))",simp,simp)
  apply(subst gettersb_unfold;subst settersb_unfold)
  by (metis cont_pref_eq1I set_get)


lemma setget_eq_fin:"#sb = Fin k \<Longrightarrow> setterSB\<cdot>(getterSB\<cdot>sb) = sbTake k\<cdot>sb"
  apply(induction sb arbitrary: k)
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule adm_neq_compact)
  apply(rule compactI,simp)
  apply(rule admI)
  apply auto[3]
  apply (metis below_fin_imp_ninf l42 linear lnle_conv lub_below unique_inf_lub)
  apply(subgoal_tac "chDom TYPE('cs) \<noteq> {}")
  apply(case_tac sb,simp_all)
  apply auto[1]
  by(case_tac k,simp_all)


lemma slen_getterSB: "\<not>chDomEmpty TYPE('cs) \<Longrightarrow> # (getterSB\<cdot>sb) = #sb"
 proof (induction sb)
   case adm
   then show ?case 
    apply(rule adm_imp,simp)
    apply(rule adm_eq,simp_all)
    using cont_Rep_cfun2 cont_compose len_stream_cont by blast
 next
   case (least sb)
   then show ?case 
     apply simp
     using sbleast2sblenempty by blast
 next
   case (sbeCons sbe sb)
   then show ?case 
     by simp
 qed

lemma setget_eq_inf[simp]:"#sb = \<infinity> \<Longrightarrow> setterSB\<cdot>(getterSB\<cdot>sb) = sb"
  by (metis (full_types) getset_below sbLen_setterSB sb_empty_eq sblen_sbeqI slen_getterSB)



lemma setget_eq[simp]:"(\<And>c. #(sb \<^enum> c)= k) \<Longrightarrow> setterSB\<cdot>(getterSB\<cdot>sb) = sb"
  apply(rule lncases[of k],simp_all)
  apply(rule setget_eq_inf)
  using inf_less_eq sblengeq apply blast
  apply(subgoal_tac "sb = sbTake ka\<cdot>sb")
  apply (metis sblen2slen sblen_empty setget_eq_fin setget_eq_inf)
  by (metis fin2stake sblen_eqI2 sbtake_below sbtake_getch)

fun setterList::"'a list \<Rightarrow> 'cs\<^sup>\<Omega>" where
"setterList [] = \<bottom>" |
"setterList (l#ls) = (setter l) \<Zcat>\<^sup>\<surd> (setterList ls)" 

lemma gettersb_unfold2:
  assumes "\<not>chDomEmpty (TYPE ('cs))"
  shows "getterSB\<cdot>(sbe \<Zcat>\<^sup>\<Omega> sb) = (getterSB\<cdot>sbe) \<Zcat> getterSB\<cdot>sb"
  apply(cases "sbe=\<bottom>")
  apply(auto)[1]
  apply (metis gettersb_emptyfix gettersb_realboteps s2sinftimes sconc_fst_empty sconc_scons)
  apply(cases "sb=\<bottom>")
   apply(auto)[1]
   apply (metis botsbleast gettersb_boteps sb_empty_eq sconc_snd_empty)
  oops


end



lemma sb_step2stream_step:
  fixes fin::"'a::countable \<Rightarrow> 'in::{chan, finite} \<Rightarrow> M"
  and fout::"'b::countable \<Rightarrow> 'out::{chan, finite} \<Rightarrow> M"
assumes "sbeGen fin"
  and "sbeGen fout"
  and "chDom TYPE ('in) \<noteq> {}"
  and "chDom TYPE ('out) \<noteq> {}"
shows"sbeGen.getterSB fout oo (sb_step\<cdot>f) oo sbeGen.setterSB fin = 
      stream_step\<cdot>(\<lambda> a. \<Lambda> s. sbeGen.getterSB fout \<cdot>(f (sbeGen.setter fin a)\<cdot>(sbeGen.setterSB fin\<cdot>s)))"
  apply(rule cfun_eqI,simp)
  apply(induct_tac x,simp_all)
  apply(subst sbeGen.settersb_strict, simp_all add: assms)
  apply(subst sbeGen.gettersb_realboteps,simp_all add: assms)
  by(subst sbeGen.settersb_unfold,simp_all add: assms)


lemma sbeinv :  "(inv sbe2sb) (sbe2sb input) = input"
  apply(rule inv_f_f)
  apply(rule injI)
  apply(rule sbe_eqI)
  apply(simp add: sbe2sb_def)
  by (metis sbe2sb.abs_eq sbe_emptyiff shd2sbe2)


locale sbeGen_empty = 
  fixes t::"'cs::{emptychan, finite} itself"
begin
end

sublocale sbeGen_empty \<subseteq> sbeGen"(\<lambda>(u::unit) cs::'cs. undefined)"
  apply(standard, simp_all)
  by (metis card_UNIV_unit is_singleton_altdef)
(*>*)

(*>*)

end