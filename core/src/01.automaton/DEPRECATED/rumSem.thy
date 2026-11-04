theory rumSem
  imports dAutomaton
begin

paragraph \<open>Semantic Mapping Comparison \\\<close> text\<open>\label{para:semrum}\<close>

text\<open>The literature semantic of a \gls{deterministic} automaton is
defined differently from @{const daSem}. To show the
correctness of @{const daSem}, we define an Isabelle version of 
Definition \<open>\<lbrakk> \<rbrakk>\<^sup>d\<close> in \cite{Rum96}.\<close>

fun Rum_dssem::"('s::discrete_cpo,'In,'Out) dAutomaton
\<Rightarrow> (('s \<times> 'In\<^sup>\<Omega>) \<rightarrow>'Out\<^sup>\<Omega>) set" where
"Rum_dssem aut = {h | h. \<forall> s m i. 
     (#i = 0 \<longrightarrow> h \<cdot>(s,i) = \<bottom>) \<and>
     h \<cdot>(s,(m \<Zcat>\<^sup>\<surd> i)) = (let (t,out) = daTransition aut s m in
                     out \<Zcat>\<^sup>\<Omega> h \<cdot>(t,i))}"

text\<open>We split the semantic in two definitions, where 
@{const Rum_dssem} restricts function \<open>h\<close> in the final semantic
mapping to have the correct recursive behaviour. Since incomplete
inputs are allowed in this framework, also all incomplete inputs are 
mapped \<open>\<bottom>\<close> in @{const Rum_dssem}.\<close>

fun Rum_dsem::"('s::discrete_cpo,'In,'Out) dAutomaton
\<Rightarrow> ('In\<^sup>\<Omega> \<rightarrow>'Out\<^sup>\<Omega>)  set"where
"Rum_dsem aut = (let(s\<^sub>0,out\<^sub>0) = (daInitState aut,daInitOut aut) in
                {g | g. \<exists>h\<in>Rum_dssem aut. \<forall>i. g\<cdot>i = out\<^sub>0 \<Zcat>\<^sup>\<Omega> h\<cdot>(s\<^sub>0,i)})"

text\<open>When comparing @{const Rum_dsem} and @{const daSem}, one can
immediately the similarities in there definition. Both semantic
define the output over a recursive call. The output of 
@{const Rum_dsem} is a set with exactly one \gls{spf}. The output of 
@{const daSem} is exactly that \gls{spf}. The reasons for using 
@{const daSem} instead of @{const Rum_dsem} is that despite having a
simple and intuitive semantic mapping, it is more challenging to use 
@{const Rum_dsem} in the verification process. Due to the set output
, proofs over the \gls{spf} have to obtain it by an existential
quantifier. If one obtains the \gls{spf} in a different definition,
it would be equal to the \gls{spf} from semantic mapping
@{const daSem}. \<close>

lemma sblen2leasnempty:
  fixes sb::"'cs\<^sup>\<Omega>"
  shows "#sb = 0 \<longleftrightarrow> (sbIsLeast sb \<and> \<not>chDomEmpty TYPE('cs))"
  apply(auto)
  using sbleast2sblenempty sbnleast_mex by auto

lemma rumdtap_step:
  assumes "dastatesem\<in> Rum_dssem aut"
  shows   "dastatesem\<cdot>(s, sbe \<Zcat>\<^sup>\<surd> sb) =
       daNextOut aut s sbe \<Zcat>\<^sup>\<Omega> dastatesem\<cdot>(daNextState aut s sbe, sb)"
  using assms apply auto
  using prod.case_eq_if by blast

lemma rumdtap_step_empty:
  fixes sb::"'in\<^sup>\<Omega>"
  assumes "dastatesem\<in> Rum_dssem aut"
  and "chDomEmpty TYPE ('in)"
  shows   "dastatesem\<cdot>(s,sb) =
       daNextOut aut s (Abs_sbElem None) \<Zcat>\<^sup>\<Omega> dastatesem\<cdot>
      (daNextState aut s (Abs_sbElem None), sb)"
  using assms apply auto
  using prod.case_eq_if
  by (metis (mono_tags, lifting) sbtypeepmpty_sbbot)

text\<open>The following two theorems show the connection between the 
state semantic and the final semantic mappings. A state semantic
obtained by @{const daStateSem} is in the output of 
@{const Rum_dssem}. Because the signature of both mappings is 
slightly different, the input for @{const daStateSem} is here given
as a tuple.\<close>


theorem dastateseminrum_dssem:
  shows"(\<Lambda> (s,sb). daStateSem aut s\<cdot>sb) \<in> Rum_dssem aut"
  unfolding Rum_dssem.simps
  apply auto
  by (simp add: case_prod_beta' dastatesem_final_h2)

text\<open>The semantic obtained by @{const daSem} is also in the 
set @{const Rum_dsem}. In conclusion, both semantics yield the same
result in our framework, because the output of \<open>\<lbrakk> \<rbrakk>\<^sup>d\<close> is a singleton.
\<close>

theorem daseminrum_dsem:
  shows"daSem aut \<in> Rum_dsem aut"
  apply(simp only: daSem_def)
  unfolding Rum_dsem.simps
  apply auto
  apply(rule_tac x="(\<Lambda> (s,sb). daStateSem aut s\<cdot>sb)" in exI)
  apply auto
  by (simp add: case_prod_beta' dastatesem_final_h2)


(*
lemma dastatesem2rum_emtpydom:
  fixes aut::"('state::discrete_cpo, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "chDomEmpty TYPE ('in)"
  and"dastatesem\<in> Rum_dssem aut"
  shows"daStateSem aut= (\<lambda>s. \<Lambda> sb. dastatesem\<cdot>(s,sb))"
  using assms
  apply(simp add: daStateSem_def case_prod_beta' Let_def)
  apply(rule fix_eqI)
  apply(subst beta_cfun)
  apply(intro cont2cont,auto)
  apply(subst fun_eq_iff,auto)
  apply(rule cfun_eqI,auto)
  apply(subst sb_steps_sbe_empty2,simp_all add: assms)
  apply(subst rumdtap_step_empty[of dastatesem aut,symmetric])
  apply(simp_all add: assms case_prod_beta' Let_def)  
  sorry

lemma dastatesemeqrum_dssem:
  assumes "dastatesem\<in> Rum_dssem aut"
  shows"dastatesem\<cdot>(s,sb) = daStateSem aut s\<cdot>sb"
  using assms
  unfolding Rum_dssem.simps
  apply auto   
proof(cases "sbIsLeast sb \<and> chDom TYPE('b) \<noteq> {}")
  case True
  then show ?thesis 
    using assms
    by (simp add: sblen2leasnempty dastatesem_bottom)
next
  case False
  then show ?thesis
    apply simp
    using assms
  proof(induction sb arbitrary: s)
    case adm
    then show ?case 
      by(simp)
  next
    case (least sb)
    then show ?case
      by (simp add: dastatesem2rum_emtpydom)
  next
    case (sbeCons sbe sb)
    then show ?case
      apply simp
      apply(cases "\<not> sbHdElemWell sb",auto)
      defer
      apply(simp_all add: case_prod_beta' dastatesem_final_h2)
      by (simp add: dastatesem_bot sblen2leasnempty)
  qed
qed


lemma rumdtap_single:
  fixes aut::"('s::discrete_cpo,'In::{finite,chan},'Out) dAutomaton"
  shows "is_singleton(Rum_dssem aut)"
  apply (rule is_singletonI')
  using dastateseminrum_dssem[of aut]
  apply blast
  by (metis cfun_eqI dastatesemeqrum_dssem surjective_pairing)
 
lemma rumdta_single:
  fixes aut::"('s::discrete_cpo,'In::{finite,chan},'Out) dAutomaton"
  shows "is_singleton(Rum_dsem aut)"
  apply(rule is_singletonI')
  using daseminrum_dsem 
  apply blast
  unfolding Rum_dsem.simps
  apply(simp only: Let_def case_prod_beta' snd_conv fst_conv)
  apply(subgoal_tac "\<forall>i. x\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> daStateSem aut (daInitState aut)\<cdot>i")
  apply(subgoal_tac "\<forall>i. y\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> daStateSem aut (daInitState aut)\<cdot>i")
  apply (simp add: cfun_eq_iff)
proof -
  fix x :: "'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>" and y :: "'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>"
assume "x \<in> {g |g. \<exists>h\<in>Rum_dssem aut. \<forall>i. g\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> h\<cdot>(daInitState aut, i)}"
assume a1: "y \<in> {g |g. \<exists>h\<in>Rum_dssem aut. \<forall>i. g\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> h\<cdot>(daInitState aut, i)}"
  assume "\<forall>i. x\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> daStateSem aut (daInitState aut)\<cdot>i"
  have "\<exists>c. c \<in> Rum_dssem aut \<and> (\<forall>s. y\<cdot>s = daInitOut aut \<Zcat>\<^sup>\<Omega> c\<cdot>(daInitState aut, s))"
    using a1 by blast
then show "\<forall>s. y\<cdot>s = daInitOut aut \<Zcat>\<^sup>\<Omega> daStateSem aut (daInitState aut)\<cdot>s"
  by (metis (full_types) dastatesemeqrum_dssem)
next
  fix x :: "'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>" and y :: "'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>"
assume a1:"x \<in> {g |g. \<exists>h\<in>Rum_dssem aut. \<forall>i. g\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> h\<cdot>(daInitState aut, i)}"
assume  "y \<in> {g |g. \<exists>h\<in>Rum_dssem aut. \<forall>i. g\<cdot>i = daInitOut aut \<Zcat>\<^sup>\<Omega> h\<cdot>(daInitState aut, i)}"
  have "\<exists>c. c \<in> Rum_dssem aut \<and> (\<forall>s. x\<cdot>s = daInitOut aut \<Zcat>\<^sup>\<Omega> c\<cdot>(daInitState aut, s))"
    using a1 by blast
then show "\<forall>s. x\<cdot>s = daInitOut aut \<Zcat>\<^sup>\<Omega> daStateSem aut (daInitState aut)\<cdot>s"
  by (metis (full_types) dastatesemeqrum_dssem)
qed
*)

end
