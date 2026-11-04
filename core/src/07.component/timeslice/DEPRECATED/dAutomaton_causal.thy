theory dAutomaton_causal
  imports dAutomaton spf.SPF
begin

default_sort "chan"

                                                         text\<open>\label{cauaut}\<close>

text\<open>Since the causality properties are an important factor for the
realizability of a component we introduce two automaton types that
work similar to our general \gls{deterministic} automaton, but 
always have a causal semantic. From the general causality theorems 
we can see directly how to comply with their assumptions. Is is 
enough to restrict the output of the transition function to 
\glspl{sb} that have at least the length 1. Interpreting complete 
\gls{sb} elements as time-slices also leads to the conclusion, that
the output of a \gls{sb} that contains only one element on each 
channel is consistent with our interpretation. Then, the automatons 
processes in each time-slice exactly one input and produces on 
time-slice as output. To accomplish this, we define the  output of a
transition function as a @{type sbElem}. This leads directly the 
weak causality of an automaton and restricts our output to 
\glspl{sb} where each channel contains exactly one element.\<close>

record ('state::type, 'in, 'out) dAutomaton_weak  =
  dawTransition :: "'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>)"
  dawInitState  :: "'state"

text\<open>The semantic of a weak automaton will never be strong, because
it has no initial output. But expanding it with an initial output in
from of a @{type sbElem} will directly fulfill necessary assumptions
for its strong semantic. Hence, we define the extension of the weak
automaton type as the strong automaton type.\<close>

record ('state::type,'in,'out)dAutomaton_strong = 
      "('state::type,'in,'out)dAutomaton_weak" + 
       dasInitOut::"'out\<^sup>\<surd>"


definition daw2das::
"('state::type, 'in, 'out) dAutomaton_weak 
\<Rightarrow> 'out\<^sup>\<surd> \<Rightarrow> ('state::type, 'in, 'out) dAutomaton_strong" where
"daw2das daw initout\<equiv> dAutomaton_weak.extend daw 
                      (dAutomaton_strong.fields initout)"


definition daw2da::"('state::type, 'in, 'out) dAutomaton_weak 
\<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da aut \<equiv>  
(| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),
                           sbe2sb (snd(dawTransition aut s sbe)))),
   daInitState  = dawInitState aut, 
   daInitOut    = \<bottom> |)"


definition das2da::"('state::type, 'in, 'out) dAutomaton_strong 
\<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"das2da aut \<equiv> 
(| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),
                           sbe2sb (snd(dawTransition aut s sbe)))),
   daInitState  = dawInitState aut, 
   daInitOut    = sbe2sb(dasInitOut aut) |)"

text\<open>The semantic mapping of our causal automatons use the 
converters to apply our general state semantic mapping 
@{const daStateSem} to our converted automatons.\<close>

definition dawStateSem::
"('s::type,'I::{chan,finite},'O) dAutomaton_weak 
\<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dawStateSem da \<equiv> daStateSem (daw2da da)"


definition dawSem::
"('s::type, 'I::{chan,finite},'O) dAutomaton_weak 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dawSem da \<equiv> dawStateSem da (dawInitState da)"


definition dasSem::
"('s::type, 'I::{chan,finite},'O) dAutomaton_strong 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"dasSem da \<equiv> daSem(das2da da)"

paragraph \<open>Causal Semantic Properties \\\<close>


lemma dawstatesem_unfolding:
"dawStateSem automat s = sb_step\<cdot>(\<lambda>sbe. \<Lambda> sb .
           let (nextState, output) = dawTransition automat s sbe in
           output \<Zcat>\<^sup>\<surd> ((dawStateSem automat) nextState\<cdot>sb))"
  apply(simp add: dawStateSem_def daw2da_def)
  apply(subst dastatesem_unfolding)
  by(simp add: prod.case_eq_if)

lemma dawNextOut:
  shows "sbe2sb (snd ((dawTransition automat) s sbe)) = 
         daNextOut (daw2da automat) s sbe"
  by (simp add: daw2da_def)

lemma dawNextState:
  shows "fst (dawTransition automat s sbe) = 
         daNextState (daw2da automat) s sbe"
  by  (simp add: daw2da_def)

theorem dawstatesem_bottom:
  assumes "\<not>sbHdElemWell (sb::'b::{finite,chan}\<^sup>\<Omega>)"
  and "\<not> chDomEmpty TYPE('b)"
  shows "(dawStateSem automat s)\<cdot>sb = \<bottom>"
  by  (simp_all add: assms dawStateSem_def dastatesem_bottom)

lemma dawstatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(dawStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dawStateSem_def dastatesem_strict)

lemma dawstatesem_step:
  assumes "sbHdElemWell sb"
  shows "(dawStateSem da s)\<cdot>sb = 
  snd (dawTransition da s (sbHdElem sb)) \<Zcat>\<^sup>\<surd> 
  dawStateSem da (fst (dawTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  by (simp_all add: dawStateSem_def assms 
       dawNextState[symmetric] dawNextOut dastatesem_step)

lemma dawstatesem_final:
  assumes "sbHdElemWell sb"
  shows "dawStateSem automat s\<cdot>sb = 
(let (nextState, output) = dawTransition automat s (sbHdElem sb) in
                  output \<Zcat>\<^sup>\<surd> dawStateSem automat nextState\<cdot>(sbRt\<cdot>sb))"
  by (simp add: case_prod_unfold Let_def dawStateSem_def
      dawNextOut dawNextState dastatesem_final assms)

lemma dawstatesem_final_h2:
  shows "(dawStateSem automat s)\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) =
          (let (nextState, output) = dawTransition automat s sbe in
                         output \<Zcat>\<^sup>\<surd> dawStateSem automat nextState\<cdot>sb)"
  by (simp add: case_prod_unfold Let_def dawStateSem_def dawNextOut 
      dawNextState)

lemma dawstatesem_bottomlen[simp]:
  assumes "#sb=0"
  shows "(dawStateSem automat s)\<cdot>sb = \<bottom>"
  apply(rule dawstatesem_bottom)
  using assms sbnleast_len apply blast
  using assms sblen_empty by auto

lemma dawstatesem_final_step[simp]:
  fixes   automat::"('state::type, 'in::{chan, finite}, 'out) dAutomaton_weak"
  assumes "chDom TYPE ('in) \<noteq> {}"
  shows "(dawStateSem automat s)\<cdot>(sbe2sb sbe) =
          sbe2sb (snd (dawTransition automat s sbe))"
  apply (insert dawstatesem_final_h2[of automat s sbe \<bottom>],simp add: case_prod_unfold Let_def)
  by(simp add: assms dawstatesem_bottom)


theorem dawstatesem_final_stepI:
  assumes "(nextState, output) = dawTransition automat s sbe"
  shows "(dawStateSem automat s)\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) =
                         output \<Zcat>\<^sup>\<surd> dawStateSem automat nextState\<cdot>sb"
  apply (simp add: dawstatesem_final_h2 case_prod_unfold Let_def)
  by (metis assms fst_conv snd_conv)


lemma dawsem_len:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_weak"
  assumes "\<not>chDomEmpty TYPE('O)"  
  shows "#(dawStateSem automat s\<cdot>sb) = #sb"
proof (cases "chDomEmpty TYPE('I)")
  case True
  have 
"\<And>s sbe. #(sbe2sb (snd ((dawTransition automat) s sbe))) = 1"
    by (simp add: assms)
  thus ?thesis
    by (metis (mono_tags, lifting) True dastatesem_inempty_len
        dawNextOut dawStateSem_def min.orderI min_def sblen_empty
        sbtypeepmpty_sbbot)
next
  case False
  have 
"\<And>s sbe. #(sbe2sb (snd ((dawTransition automat) s sbe))) = 1"
    by (simp add: assms)
  hence nextout_len: 
        "\<And>s sbe. #(daNextOut (daw2da automat) s sbe) = 1"
    by (simp add: dawNextOut)
  have "# sb < \<infinity> \<Longrightarrow> # sb = #(dawStateSem automat s\<cdot>sb)"
  proof-
    assume sb_len: "#sb < \<infinity>"
    thus ?thesis
    proof (induction sb arbitrary: s rule: sb_finind)
      case 1
      then show ?case
        using sb_len by blast
    next
      case (2 sb)
      then show ?case
        by (metis False assms botsbleast dawstatesem_bottom 
            lnzero_def sbleast2sblenempty)
    next
      case (3 sbe sb)
      then show ?case
        by (metis dawstatesem_step fold_inf inf_less_eq 
            le_less_linear lnat.con_rews lnzero_def sbecons_len 
            sbleast2sblenempty sbrt_sbecons)
    qed
  qed
  thus ?thesis
    by (metis dastatesem_weak dawStateSem_def inf_less_eq
        le_less_linear less_irrefl nextout_len weak_well_ts_def)
qed

lemma dawstatesem_weak:
  shows  "weak_well_ts (dawStateSem automat s)"
  apply (simp add: dawStateSem_def)
  apply (rule dastatesem_weak)
  apply (simp add: daw2da_def)
  by (cases "chDomEmpty TYPE('b)",auto)

theorem dawsem_weak[simp]:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_weak"
  shows  "weak_well_ts (dawSem automat)"
  apply (simp add: dawSem_def)
  by (simp add: dawstatesem_weak eta_cfun)
  
lemma dassem_insert:
"dasSem automat\<cdot>sb = dasInitOut automat \<Zcat>\<^sup>\<surd> 
                     dawStateSem (dAutomaton_weak.truncate automat)
                     (dawInitState automat)\<cdot>sb"
  by (simp add:  dasSem_def dawSem_def dAutomaton_weak.defs 
      dAutomaton_strong.defs dasem_insert das2da_def 
      dawStateSem_def daw2da_def daStateSem_def)

lemma dasinitout_well[simp]:"(dasInitOut
         (dAutomaton_weak.extend daw
           (dAutomaton_strong.fields
             sbe))) = sbe"
  by(simp add: dAutomaton_weak.defs dAutomaton_strong.defs)

lemma das2daw_trunc_well[simp]:"dAutomaton_weak.truncate
                (dAutomaton_weak.extend da
                  (dAutomaton_strong.fields sbe)) = da" 
  by(simp add: dAutomaton_weak.defs dAutomaton_strong.defs)

lemma outns_ex:
"\<exists>a s2. \<forall>sb. (dawStateSem da s)\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = a \<Zcat>\<^sup>\<surd> (dawStateSem da s2)\<cdot>sb"
  apply(subst dawstatesem_final_h2,simp add: case_prod_unfold Let_def)
  by blast

lemma (in sbeGen) outns_ex:"
\<exists>a s2. \<forall>sb. getterSB\<cdot>((dawStateSem da s)\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb)) = 
\<up>a \<Zcat> getterSB\<cdot>(dawStateSem da s2\<cdot>sb)"
  apply(subst dawstatesem_final_h2,simp add: case_prod_unfold Let_def)
  by blast


lemma (in sbeGen) getter_eps[simp]:
  assumes"chDom TYPE('cs) \<noteq> {}" 
  and "#sb =0"
  shows"\<And>s. getterSB\<cdot>((dawStateSem da s)\<cdot>sb)=\<epsilon>"
  by(simp add: assms)

lemma (in sbeGen) getter_strict:
  assumes"chDom TYPE('cs) \<noteq> {}"
  and"chDom TYPE('c) \<noteq> {}"
  shows"\<And>s. getterSB\<cdot>((dawStateSem da s)\<cdot>(\<bottom>::'c::{chan,finite}\<^sup>\<Omega>))=\<epsilon>"
  apply(rule getter_eps)
  apply(simp add: assms)
  apply(rule botlen)
  by(simp add: assms)

lemma dassem_bottom:
  assumes "\<not> chDomEmpty TYPE('b::{finite,chan})"
  shows "dasSem automat\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = sbe2sb (dasInitOut automat)"
  by (simp add: dasSem_def dasem_bottom assms das2da_def)


lemma dassem_len:
  fixes automat::"('s::type,'I::{chan,finite},'O)dAutomaton_strong"
  assumes "\<not>chDomEmpty TYPE('O)"  
  shows  "#(dasSem automat\<cdot>sb) = lnsuc\<cdot>(#sb)"
  by (simp add: assms dassem_insert dawsem_len)

theorem dassem_strong:
shows "strong_well_ts (dasSem automat)"
  apply (simp add: strong_well_ts_def dassem_insert)
  by (meson dawstatesem_weak weak_well_ts_def)

paragraph \<open>Lifted semantic \\\<close>

text\<open>We then provide lifted semantics for strong and weak
automatons. The lifted versions of @{const dawSem} and 
@{const dasSem} map to well formed causal \glspl{spf}.\<close>

lift_definition semantic_weak::
"('state::type,'in::{tschan,finite},'out::tschan) dAutomaton_weak 
\<Rightarrow> ('in,'out)spfw" is "dawSem"
  using dawsem_weak weak_well_eq by %visible blast


lift_definition semantic_strong::
"('s::type, 'in::{tschan,finite}, 'out::tschan) dAutomaton_strong 
\<Rightarrow> ('in,'out)spfs"is "\<lambda>auts. Abs_spfw(dasSem auts)"
  by %visible (metis Abs_spfw_inverse dassem_strong mem_Collect_eq strong2weak_well strong_well_eq)

end
