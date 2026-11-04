theory dAutomaton
  imports bundle.SB_fin spf.SPF bundle.SBCodegen

begin


lemma prod_contI[cont2cont]: "(\<And>s. cont(\<lambda>f. g (f,s))) 
\<Longrightarrow>(\<And>f. cont (\<lambda>s. g (f,s))) \<Longrightarrow> cont g"
  by (simp add: prod_contI)

                                 text\<open>\label{sec:aut}\<close>

text\<open>The behaviour of a component can be modeled by a \<open>I/O\<^sup>\<omega>\<close> 
automaton. This section defines \gls{deterministic} and 
\gls{nondeterministic} automaton types and their semantic mapping to
\glspl{spf} and \glspl{sps}. Furthermore, we take a closer look at 
causal automatons and use their properties to introduce locales that
simplifies the generation and also the verification process for the 
input-output behavior by hiding bundles.\<close>


                                                  text\<open>\label{sub:detaut}\<close>

default_sort %invisible "chan"

text\<open>A \gls{deterministic} \<open>I/O\<^sup>\<omega>\<close> Automaton consists of states, a 
transition function that reacts on input messages and produces 
output messages, an initial state and an initial output. The 
transition function for a \gls{deterministic} automaton maps from a
state type with a @{type sbElem} to another state and a output 
\gls{sb}. Now we define \gls{deterministic} automaton as a tuple. 
Since we always have the message type @{type M} it does not 
explicitly occur in our signature. It is hidden in our \gls{sb} and 
@{type sbElem} types.\<close>

record ('state::type, 'in::chan, 'out::chan) dAutomaton  =
  daTransition :: "'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>)"
  daInitState :: "'state"
  daInitOut :: "'out\<^sup>\<Omega>"

text\<open>The type parameter of @{type dAutomaton} show the state set and
the input and output domain. We then introduce two abbreviations to 
obtain the next state or the next output of the transition function.
\<close>

abbreviation daNextState:: 
"('s::type,'in , _) dAutomaton \<Rightarrow> 's \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> 's"where 
"daNextState aut s m \<equiv> fst ((daTransition aut) s m)"


abbreviation daNextOut::
"('s::type, 'in,'out) dAutomaton \<Rightarrow> 's \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> 'out\<^sup>\<Omega>" where
"daNextOut aut s m \<equiv> snd ((daTransition aut) s m)"

                                              text\<open>\label{subsub:sem}\<close>

text\<open>The semantic of an automaton corresponds to a \gls{spf}. 
In comprehensible terms, our the semantic mapping iterates through 
the input and obtain the automatons output for each input 
bundle element. This is formulated as a fixed point function for a 
function from states to \gls{spf}, because the behaviour of the 
transition function depends on the state. Hence, the states are part
of the iteration. The usage of @{const sb_step} allows to directly
access the first stream bundle element of the input. This is the 
input of the transition function and allows us formulate a semantic 
mapping without splitting the input \gls{sb} into a lot of cases. If
the input \gls{sb} contains no complete bundle element, 
@{const sb_step} maps to the empty output.\<close>

definition daStateSem::"('s::type, 'I::{finite,chan},'O) dAutomaton 
\<Rightarrow> 's \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daStateSem da =
 fix\<cdot>(\<Lambda> h. (\<lambda> state. sb_step\<cdot>
        (\<lambda>sbe. \<Lambda> sb.
           let (nextState, output) = daTransition da state sbe in
                output \<Zcat>\<^sup>\<Omega> h nextState\<cdot>sb)))"


text\<open>An infinite input domain would lead to continuity problems in 
@{const sb_step} \cref{subsub:sbhdelemc,subsub:sbsplit}. Another 
option to still force continuity would be restricting \glspl{sb} to
only contain streams of equal length. This would then be problematic
for compositions of weak and strong \glspl{spf}, because the streams
in the output might not have the same length. On the other hand, 
forcing all streams to be infinitely long complicates the definition
of a general composition operator, because the fixpoint operator 
@{const fix} would then do nothing. Hence, we restrict the input
domains to be finite.\<close>

text\<open>Altogether, @{const daStateSem} maps to the semantic of any
desired state and is independent form the start state or the initial
output of the automaton. Therefore, the semantic mapping of our
complete automaton uses the initial state to obtain the
corresponding semantic from @{const daStateSem} and also first
outputs the initial output of the automaton.\<close>

definition daSem::"('s::type, 'I::{finite,chan},'O) dAutomaton 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem da \<equiv> \<Lambda> sb. daInitOut da \<Zcat>\<^sup>\<Omega> daStateSem da(daInitState da)\<cdot>sb"

lemma[code]:"Rep_cfun (daSem da) = (\<lambda> sb. daInitOut da \<Zcat>\<^sup>\<Omega> daStateSem da(daInitState da)\<cdot>sb)"
  by(simp add: daSem_def)

lemma dasem_cont[simp]:"cont (\<lambda> sb. daInitOut da \<Zcat>\<^sup>\<Omega> daStateSem
        da(daInitState da)\<cdot>sb)"
  by simp

text\<open>The abbreviation \<open>\<lbrakk> \<rbrakk>\<^sup>d\<close> for the semantic of a total 
deterministic automaton is defined identical to \cite{Rum96}.\<close>

abbreviation dasem_abbrev::
"('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" 
("\<lbrakk>_\<rbrakk>\<^sup>d" [1000] 999) where "\<lbrakk>aut\<rbrakk>\<^sup>d \<equiv> daSem aut"

paragraph\<open>Semantic Properties \\\<close>


lemma dastatesem_unfolding: "(daStateSem automat s) = 
sb_step\<cdot>(\<lambda>sbe. \<Lambda> sb .
           let (nextState, output) = daTransition automat s sbe in
           output \<Zcat>\<^sup>\<Omega> ((daStateSem automat) nextState\<cdot>sb))"
  unfolding daStateSem_def
  apply(subst fix_eq)
  apply(subst beta_cfun)
  apply(intro cont2cont; simp)
  by auto


lemma dastatesem_bottom:
  fixes sb::"'cs::{finite,chan}\<^sup>\<Omega>"
  assumes "\<not>sbHdElemWell (sb)"
  and "\<not> chDomEmpty TYPE('cs)"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_step_insert)
  by (metis (no_types, lifting) assms fup1 sbHdElem_h_cont.rep_eq 
      sbHdElem_h_def)

theorem dastatesem_bot[simp]:
  fixes   sb::"'cs::{finite,chan}\<^sup>\<Omega>"
  assumes "#sb = 0"
  shows   "(daStateSem automat s)\<cdot>sb = \<bottom>"
  apply (rule dastatesem_bottom)
  using assms sbnleast_len apply blast
  using assms sblen_empty by auto

lemma dastatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(daStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dastatesem_bottom sbHdElemWell_def)

lemma dastatesem_step: 
  assumes "sbHdElemWell sb"
  shows "(daStateSem da s)\<cdot>sb = snd (daTransition da s (sbHdElem sb)) 
  \<Zcat>\<^sup>\<Omega> daStateSem da (fst (daTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_step_insert Let_def case_prod_unfold)
  apply (cases "sbHdElem_h_cont\<cdot>sb")
  apply (simp_all add: sbHdElem_h_cont.rep_eq sbHdElem_def)
  apply (simp_all split: u.split)
  apply (metis assms inst_up_pcpo sbHdElem_h_def u.simps(3))
  by (simp add: up_def)

lemma dastatesem_final:
  assumes "sbHdElemWell sb"
  shows "(daStateSem automat s)\<cdot>sb =
  daNextOut automat s (sbHdElem sb) \<Zcat>\<^sup>\<Omega> 
  daStateSem automat (daNextState automat s (sbHdElem sb))\<cdot>(sbRt\<cdot>sb)"
  by (metis assms dastatesem_step)

lemma dastatesem_empty:
  fixes   aut::"('state::type,'in::{chan, finite},'out) dAutomaton"
  assumes "chDomEmpty TYPE('in)"
  shows   "(daStateSem aut s)\<cdot>sb =
  daNextOut aut s (sbHdElem sb) \<Zcat>\<^sup>\<Omega> 
  daStateSem aut (daNextState aut s (sbHdElem sb))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_step_insert Let_def case_prod_unfold)
  apply (cases "sbHdElem_h_cont\<cdot>sb")
  apply (simp_all add: sbHdElem_h_cont.rep_eq sbHdElem_def)
  apply (simp_all split: u.split)
  apply (metis assms inst_up_pcpo sbHdElem_h_def u.simps(3))
  by (simp add: up_def)

lemma dastatesem_final_h2[simp]:
  shows "daStateSem automat s\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) =
  daNextOut automat s sbe \<Zcat>\<^sup>\<Omega> 
  daStateSem automat (daNextState automat s sbe)\<cdot>sb"
  apply (cases "chDomEmpty(TYPE('b))")
  apply (subst dastatesem_empty,simp)
  apply (metis sbhdelem_sbecons sbrt_sbecons)
  apply (subst dastatesem_final)
  apply (metis lnat.con_rews lnzero_def sbecons_len 
         sbleast2sblenempty)
  by (metis sbhdelem_sbecons sbrt_sbecons)

lemma dastatesem_code_h:"daStateSem p s \<cdot>(sb::('b::{chan,finite})\<^sup>\<Omega>) = (if chDomEmpty TYPE('b) then daStateSem p s \<cdot>sb else (if sbIsLeast sb then botsb else 
 sbConc (snd(daTransition p s (sbHdElem sb)))\<cdot> (daStateSem p (fst(daTransition p s (sbHdElem sb)))\<cdot> (sbRt\<cdot>sb))))"
  apply(case_tac "sbIsLeast sb", simp_all)
  apply (simp add: botsb_eq dastatesem_bottom)
  by(simp add:dastatesem_step)

lemma[code]:"Rep_cfun(daStateSem p s)  = (\<lambda>(sb::('b::{chan,finite})\<^sup>\<Omega>). (if chDomEmpty TYPE('b) then daStateSem p s \<cdot>sb else (if sbIsLeast sb then botsb else 
 sbConc (snd(daTransition p s (sbHdElem sb)))\<cdot> (daStateSem p (fst(daTransition p s (sbHdElem sb)))\<cdot> (sbRt\<cdot>sb)))))"
  using dastatesem_code_h by (metis (no_types, opaque_lifting) dastatesem_final)



theorem dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
  and     "(daNextState da s sbe) = nextState"
  shows   "daStateSem da s\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = 
           out  \<Zcat>\<^sup>\<Omega> daStateSem da nextState\<cdot>sb"
  by (simp add: assms)

lemma dastatesem_inempty_len:
  fixes   automat::"('state::type, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. 1 \<le> #(daNextOut automat state sbe)"
  and     "chDomEmpty TYPE('in)"
  shows   "\<forall>s. #(daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
proof(rule contrapos_pp,simp+)
  assume a1: "\<exists>s::'state. # (daStateSem automat s\<cdot>\<bottom>) \<noteq> \<infinity>"
  obtain len_set where len_set_def: 
        "len_set = {# (daStateSem automat s\<cdot>\<bottom>) | s. True }"
    by simp
  hence len_set_least: "\<exists>n \<in> len_set. \<forall>i \<in> len_set. n \<le> i"
    by (metis (mono_tags, lifting) exists_least_iff le_less_linear 
        len_set_def mem_Collect_eq)
  then obtain state where state_def: "#(daStateSem automat state\<cdot>\<bottom>) \<in> len_set" 
    and "\<forall>n \<in> len_set. # (daStateSem automat state\<cdot>\<bottom>) \<le> n"
    using len_set_def by blast
  hence state_least: "\<forall>s. # (daStateSem automat state\<cdot>\<bottom>) \<le> 
                          # (daStateSem automat s\<cdot>\<bottom>)"
    using len_set_def len_set_least by blast
  then obtain k where k_def: "Fin k = 
                              #(daStateSem automat state\<cdot>\<bottom>)"
    by (metis a1 inf_less_eq ninf2Fin)

  hence "Fin k < #(daNextOut automat state (Abs_sbElem None)) + 
         #(daStateSem automat 
         (daNextState automat state (Abs_sbElem None))\<cdot> \<bottom>)"
    by (metis add.commute assms(1) le2lnle lessequal_addition lnat_plus_suc not_le_imp_less notinfI3 state_least)
  thus "False"
    by (metis assms(2) dastatesem_final_h2 k_def leD sblen_sbconc 
        sbtypeempty_sbecons_bot)
qed


theorem dastatesem_inempty_leninf:
  fixes   automat::"('state::type, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. 1 \<le> # (daNextOut automat state sbe)"
  and     "chDomEmpty TYPE('in)"
  shows   "# (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
  by(simp add: assms dastatesem_inempty_len)

lemma dastatesem_weak_fin:
  assumes "# sb = Fin n"
    and "\<And>state sbe. 1 \<le> # (daNextOut automat state sbe)"
  shows "# sb \<le> # (daStateSem automat s\<cdot>sb)"
  apply (induction sb arbitrary: s rule: sb_finind)
  apply (simp_all add: assms)
  apply (cases "chDomEmpty TYPE('a)")
  using assms(1) apply auto[1]
  using sbleast2sblenempty apply fastforce
  by (metis (no_types, lifting) dual_order.trans 
      assms(2) dastatesem_final_h2 lessequal_addition 
      lnat_plus_commu lnat_plus_suc sblen_sbconc)

lemma [simp]:"sbIsLeast (sb::'cs\<^sup>\<Omega>) \<Longrightarrow> chDom TYPE('cs) \<noteq> {} \<Longrightarrow> #sb=0"
  using sbleast2sblenempty by blast

lemma dastatesem_weak_leneq:
  assumes "# sb = Fin n"
    and "\<And>state sbe c. 1 = # (daNextOut automat state sbe \<^enum> c)"
  shows "# (daStateSem automat s\<cdot>sb) = #sb"
  apply (induction sb arbitrary: s rule: sb_finind)
  apply (simp_all add: assms)
  apply (cases "chDomEmpty TYPE('a)";cases "chDomEmpty TYPE('c)";simp)
  using assms(1) apply auto[1]
  apply(subgoal_tac "\<And>state sbe. #(daNextOut automat state sbe) = \<infinity>")
  using Fin_neq_inf assms(2) one_lnat_def apply auto[1]
  using sblen_empty apply blast
  apply(subgoal_tac "\<exists> sbeout. sbe2sb sbeout = daNextOut automat s sbe ")
  apply (metis sbecons_len)
  apply (rule len2sbe_ex)
  using assms(2) by auto


theorem dastatesem_weak:
  fixes   automat::"('state::type, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. 1 \<le> # (daNextOut automat state sbe)"
  shows   "weak_well_ts (daStateSem automat s)"
  apply (cases "chDomEmpty TYPE('in)")
  apply (metis (full_types) assms dastatesem_inempty_len fold_inf 
        less_lnsuc sblen_empty sbtypeepmpty_sbbot weak_well_ts_def)
  by (metis assms weak_well_tsI2 dastatesem_weak_fin lnat_well_h2)

lemma dastatesem_least:
  assumes"(\<lambda>state. sb_step\<cdot>
          (\<lambda>sbe. \<Lambda> sb. snd (daTransition X state sbe) \<Zcat>\<^sup>\<Omega>  
          Z (fst (daTransition X state sbe))\<cdot>sb)) \<sqsubseteq> Z"
  shows"daStateSem X \<sqsubseteq> Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_least_below)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  by (simp add: assms case_prod_unfold)

lemma dastatesem_empbelowI:
  fixes X::"('state::type,'in::{chan, finite},'out) dAutomaton"
  assumes "chDomEmpty TYPE('in)"
  assumes"\<And>state. snd (daTransition X state (Abs_sbElem None)) \<Zcat>\<^sup>\<Omega>  
          Z (fst (daTransition X state (Abs_sbElem None)))\<cdot>\<bottom> \<sqsubseteq> 
          Z state\<cdot>\<bottom>"
  shows"daStateSem X \<sqsubseteq> Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_least_below)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  apply (simp add: assms case_prod_unfold)
  apply (rule fun_belowI)
  apply (rule cfun_belowI)
  apply (subst sb_steps_sbe_empty2,simp add: assms)
  apply(insert assms(2))
  apply (subst beta_cfun,simp)
  using monofun_cfun_arg rev_below_trans by blast
(*
lemma dastatesem_empeqI:
  fixes X::"('state::type,'in::{chan, finite},'out) dAutomaton"
  assumes "chDomEmpty TYPE('in)"
  and"\<And>state. snd (daTransition X state (Abs_sbElem None)) \<Zcat>\<^sup>\<Omega>  
          Z (fst (daTransition X state (Abs_sbElem None)))\<cdot>\<bottom> = 
          Z state\<cdot>\<bottom>"
  and"\<And>z state.  daNextOut X state (Abs_sbElem None) \<Zcat>\<^sup>\<Omega> 
          z (daNextState X state (Abs_sbElem None))\<cdot>\<bottom> = z state\<cdot>\<bottom> 
        \<Longrightarrow> Z state\<cdot>\<bottom> \<sqsubseteq> z state\<cdot>\<bottom>"  
  shows"daStateSem X = Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_eqI)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  apply (simp add: assms case_prod_unfold)
  apply (subst fun_eq_iff,auto)
  apply (rule cfun_eqI)
  apply (subst sb_steps_sbe_empty2,simp add: assms)
  apply(insert assms(2))
  apply (subst beta_cfun,simp)
  apply(subgoal_tac "xa=\<bottom>")
  using monofun_cfun_arg rev_below_trans apply blast
  using assms apply simp
  apply(rule fun_belowI)
  apply(rule cfun_belowI)
  oops*)


lemma statesem_sbtakeinput:
  "#sb=Fin k \<Longrightarrow> daStateSem aut s\<cdot>sb = daStateSem aut s\<cdot>(sbTake k\<cdot>sb)"
proof(induction sb arbitrary: s k)
  case adm
  then show ?case
    apply(rule adm_all)+
    by(rule adm_imp,simp_all)
next
  case (empty sb)
  then show ?case 
    by simp
next
  case (least sb)
  then show ?case 
    by simp
next
  case (sbeCons sbe sb)
  then show ?case
    by(cases k,simp_all)
qed

lemma statesem_sbtakeoutput:
  fixes aut::"('state::type,'in::{chan,finite},'out::{chan,finite})dAutomaton"
  assumes "\<And>s i c. #(snd (daTransition aut s i) \<^enum> c) = 1"
  shows"#(daStateSem aut s\<cdot>sb)=Fin k \<Longrightarrow> daStateSem aut s\<cdot>sb = sbTake k\<cdot>(daStateSem aut s\<cdot>sb)"
  using assms
proof(induction sb arbitrary: s k)
  case adm
  then show ?case
    apply(rule adm_all)+
    by(rule adm_imp,simp_all)
next
  case (empty sb)
  then show ?case
    by (metis (mono_tags, lifting) Fin_neq_inf dastatesem_inempty_len 
le_numeral_extra(4) len_sb_def less2nat one_lnat_def sb_empty_eq sblengeq')
next
  case (least sb)
  then show ?case 
    by simp
next
  case (sbeCons sbe sb)
  then show ?case
    apply(cases k,simp_all)
    apply (metis (mono_tags, opaque_lifting) len2sbe_ex sb_empty_eq 
        sbehdleme_well sbnleast_len)
    apply(subgoal_tac "\<exists>sbeout. daNextOut aut s sbe = sbe2sb sbeout")
    apply auto[1]
    by (metis len2sbe_ex)
qed



theorem dasem_insert:
  "\<lbrakk>automat\<rbrakk>\<^sup>d\<cdot>sb = daInitOut automat \<Zcat>\<^sup>\<Omega> 
                     daStateSem automat (daInitState automat)\<cdot>sb"
  by (simp add: daSem_def)


theorem dasem_bottom:
  assumes "\<not>chDomEmpty TYPE('in::{chan,finite})"
  shows "\<lbrakk>automat\<rbrakk>\<^sup>d\<cdot>(\<bottom>::'in\<^sup>\<Omega>) = daInitOut automat"
  by (simp add: daSem_def assms dastatesem_strict)


theorem dasem_strong:
  assumes "weak_well_ts(daStateSem automat (daInitState automat))"
  and     "1 \<le> # (daInitOut automat)"
  shows "strong_well_ts (\<lbrakk>automat\<rbrakk>\<^sup>d)"
  apply (subst strong_well_ts_def)
  apply (simp add: daSem_def)
proof
  fix sb
  have h1: "# sb <\<^sup>l lnsuc\<cdot>(# 
                      (daStateSem automat (daInitState automat)\<cdot>sb))"
    using assms(1) sblen_mono
    by (simp add: weak_well_ts_def)
  have h4: "lnsuc\<cdot>(#(daStateSem automat(daInitState automat)\<cdot>sb))
             \<le> # (daInitOut automat) + 
               # (daStateSem automat (daInitState automat)\<cdot>sb)"
    by (metis add.commute assms(2) lessequal_addition lnat_plus_suc 
        order_refl)
  have h2: "# (daInitOut automat) + # (daStateSem automat 
       (daInitState automat)\<cdot>sb) \<le> # (daInitOut automat \<Zcat>\<^sup>\<Omega>  
        daStateSem automat (daInitState automat)\<cdot>sb)"
    using sblen_sbconc by auto
  have h3: "# sb <\<^sup>l # (daInitOut automat \<Zcat>\<^sup>\<Omega> 
            daStateSem automat (daInitState automat)\<cdot>sb)"
    using h1 h2 h4 dual_order.trans by blast
  then show "\<And>sb. # sb <\<^sup>l # (daInitOut automat \<Zcat>\<^sup>\<Omega>  
                  daStateSem automat (daInitState automat)\<cdot>sb)"
    by (metis (no_types, lifting) assms(1) assms(2) dual_order.trans lessequal_addition lnat_plus_commu lnat_plus_suc sblen_sbconc weak_well_ts_def)
qed
  
end
