theory ndAutomaton
  imports bundle.SB_fin spf.SPF
begin
default_sort "chan"


                                                   text\<open>\label{sub:ndaut}\<close>



record ('state::type,'in::chan,'out::chan) 
  ndAutomaton_incomplete =
    ndaiTransition :: "'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set)"
    ndaiInitConfig :: "('state \<times> 'out\<^sup>\<Omega>) set"

record %invisible('state::type,'in, 'out) 
ndAutomaton_weak  =
  ndawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<surd>) set))"
  ndawInitConfig :: "('state) set"

record %invisible('state::type,'in, 'out) 
ndAutomaton_strong  =
  ndasTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<surd>) set))"
  ndasInitConfig :: "('state \<times> 'out\<^sup>\<surd>) set"

definition %invisible ndAw2nda::"('state::type,'in, 'out) 
ndAutomaton_weak \<Rightarrow> ('state::type,'in, 'out) 
ndAutomaton_incomplete" where
"ndAw2nda ndaw = (| ndaiTransition=
    (\<lambda>s sbe. (apsnd sbe2sb)`ndawTransition ndaw s sbe), 
    ndaiInitConfig=(\<lambda>s. (s,\<bottom>))`(ndawInitConfig ndaw) |)"

definition %invisible ndAs2nda::"('state::type,'in, 'out)
ndAutomaton_strong \<Rightarrow> ('state::type,'in, 'out) 
ndAutomaton_incomplete" where
"ndAs2nda ndas = (| ndaiTransition=
    (\<lambda>s sbe. (apsnd sbe2sb)`ndasTransition ndas s sbe), 
    ndaiInitConfig=(apsnd sbe2sb)`(ndasInitConfig ndas) 
|)"


cpodef ('state::type,'in::chan,'out::chan) ndAutomaton =
  "{( transition    ::'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set)
    , initialConfig ::('state \<times> 'out\<^sup>\<Omega>) set)
      | transition initialConfig.
          (\<forall>state sbe. transition state sbe \<noteq> {})
        \<and> initialConfig \<noteq> {}}"
  apply auto[1]
  apply (subst UU_eq_empty[symmetric])+
  apply (rule admI)
  apply (simp add: lub_prod)
  apply (rule, rule, rule)
  apply (simp_all add: lub_eq_bottom_iff mem_Times_iff)
proof -
  fix Y :: "nat \<Rightarrow> 
  ('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<times> ('state \<times> 'out\<^sup>\<Omega>) set" 
  and state :: 'state and sbe :: "'in\<^sup>\<surd>"
  assume a1: "\<forall>i. (\<forall>state sbe. fst (Y i) state sbe \<noteq> \<bottom>) \<and> 
                               snd (Y i)           \<noteq> \<bottom>"
  assume "chain Y"
  then have "chain (\<lambda>n. fst (Y n))"
    using ch2ch_fst by blast
  then show "(\<Squnion>n. fst (Y n)) state sbe \<noteq> \<bottom>"
    using a1 by (simp add: fun_chain_iff lub_eq_bottom_iff lub_fun)
qed

setup_lifting %invisible type_definition_ndAutomaton


lemma nd_rep_cont[simp, cont2cont]: "cont Rep_ndAutomaton"
  using cont_Rep_ndAutomaton cont_id by blast



lift_definition ndai2ndac::
"('state::type,'in, 'out) ndAutomaton_incomplete
  \<Rightarrow>('state::type,'in, 'out) ndAutomaton " is
"\<lambda>auti. (
  \<comment>\<open>transitionfunction:\<close>
      (\<lambda> s sbe. let out = ndaiTransition auti s sbe in
                   if out = {} then UNIV else out)
    ,
  \<comment>\<open>initial config:\<close>
   (if ndaiInitConfig auti = {} then UNIV else ndaiInitConfig auti))"
  by(simp add: Let_def)

lift_definition ndaw2ndac::
"('state::type,'in, 'out) ndAutomaton_weak
\<Rightarrow>('state::type,'in, 'out) ndAutomaton " is
"\<lambda>autw. ((\<lambda> s sbe. let out = ndawTransition autw s sbe in
                   if out = {} then (apsnd sbe2sb) ` UNIV else ((apsnd sbe2sb) ` out)),
                   if ndawInitConfig autw = {} 
                               then UNIV else (\<lambda>s. (s,\<bottom>))` (ndawInitConfig autw))"
  by (simp add: Let_def)                          


lift_definition ndas2ndac::
"('state::type,'in, 'out) ndAutomaton_strong
\<Rightarrow>('state::type,'in, 'out) ndAutomaton " is
"\<lambda>auts. ((\<lambda> s sbe. let out = ndasTransition auts s sbe in
                   if out = {} then (apsnd sbe2sb) ` UNIV else ((apsnd sbe2sb) ` out)),
                   if ndasInitConfig auts = {} 
                               then (apsnd sbe2sb) ` UNIV else (apsnd sbe2sb) ` (ndasInitConfig auts))"
  by (simp add: Let_def)                          


lift_definition ndaTransition::
"('state::type, 'in, 'out) ndAutomaton \<rightarrow> 
'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set)" is
"\<lambda> aut. fst(Rep_ndAutomaton aut)"
  by(intro cont2cont)

lemma nda_trans_mono: assumes "nda1 \<sqsubseteq> nda2"
  shows "(ndaTransition\<cdot>nda1) state sbe \<subseteq> (ndaTransition\<cdot>nda2) state sbe"
  apply (subgoal_tac "(ndaTransition\<cdot>nda1) \<sqsubseteq> (ndaTransition\<cdot>nda2)")
  apply (simp add: SetPcpo.less_set_def fun_below_iff)
  using assms monofun_cfun_arg by auto 

lemma nda_trans_ndAw2ndac_refinement: 
  assumes "\<And>s sbe t out. (t, out) \<in> (ndawTransition nda1) s sbe \<Longrightarrow>
                       (f t, out) \<in> (ndawTransition nda2) (f s) sbe"
  and "\<And>s sbe. (ndawTransition nda1) s sbe = {} 
    \<Longrightarrow> (ndawTransition nda2) (f s) sbe = {}"
shows "\<And>s sbe t out.
    (t, out) \<in> (ndaTransition\<cdot>(ndai2ndac (ndAw2nda nda1))) s sbe 
    \<Longrightarrow> (f t, out) \<in> (ndaTransition\<cdot>(ndai2ndac (ndAw2nda nda2))) (f s) sbe"
proof -
  fix s sbe t out
  assume a1: "(t, out) \<in> (ndaTransition\<cdot>(ndai2ndac (ndAw2nda nda1))) s sbe"
  then have h1: "ndawTransition nda2 (f s) sbe \<noteq> {} 
             \<Longrightarrow> ndawTransition nda1 s sbe \<noteq> {}"
    using assms(2) by blast
  have h2:"(t, out) \<in> apsnd sbe2sb ` ndawTransition nda1 s sbe \<Longrightarrow> (f t, out) \<in> ( apsnd sbe2sb ` ndawTransition nda2 (f s) sbe)"
    using assms(1) image_iff by fastforce
  show "(f t, out) \<in> (ndaTransition\<cdot>(ndai2ndac (ndAw2nda nda2))) (f s) sbe"
    using a1 apply(simp add: ndaTransition.rep_eq ndai2ndac.rep_eq ndAw2nda_def)
    by(cases "ndawTransition nda1 s sbe = {}",simp_all add: h1 assms h2)
qed

lemma nda_trans_ndAw2ndac_len: 
  assumes "\<And> state sbe. ndawTransition nda_weak state sbe \<noteq> {}" 
  shows "\<forall> (s,out::'a::{chan,finite}\<^sup>\<Omega>) \<in> 
((ndaTransition\<cdot>(ndai2ndac (ndAw2nda nda_weak))) state sbe). #out \<ge> 1"
  apply(simp add: ndaTransition_def ndai2ndac.rep_eq ndAw2nda_def assms case_prod_beta)
  using sbe2sb_len by blast


lift_definition ndaInitConfig::
"('state::type, 'in, 'out) ndAutomaton \<rightarrow> ('state \<times>'out\<^sup>\<Omega>)set" is
"\<lambda> aut. snd(Rep_ndAutomaton aut)"
  by(intro cont2cont)

lemma nda_init_mono: assumes "nda1 \<sqsubseteq> nda2"
  shows "(ndaInitConfig\<cdot>nda1) \<subseteq> (ndaInitConfig\<cdot>nda2)"
  by (metis SetPcpo.less_set_def assms cont_pref_eq1I)

lemma repnda_exists:
 "\<exists>f P. Rep_ndAutomaton nda = (f, P) \<and> (\<forall>a s. f a s \<noteq> {}) \<and> P \<noteq> {}"
  using Rep_ndAutomaton by blast

lemma ndatrans_nempty: "(ndaTransition\<cdot>nda) s sbe \<noteq> {}"
  apply(simp add: ndaTransition.rep_eq)
  using fstI repnda_exists by fastforce

lemma ndainit_nempty: "(ndaInitConfig\<cdot>nda) \<noteq> {}"
  apply(simp add: ndaInitConfig.rep_eq)
  by (metis repnda_exists snd_conv)

lemma nda_belowI: 
  assumes "\<And>state sbe. (ndaTransition\<cdot>nda1) state sbe  
                     \<subseteq> (ndaTransition\<cdot>nda2) state sbe"
      and "ndaInitConfig\<cdot>nda1 \<subseteq> ndaInitConfig\<cdot>nda2"
    shows "nda1 \<sqsubseteq> nda2"
  apply(subst below_ndAutomaton_def)
  apply(rule prod_belowI)
  apply (metis SetPcpo.less_set_def assms(1) fun_belowI ndaTransition.rep_eq)
  by (metis SetPcpo.less_set_def assms(2) ndaInitConfig.rep_eq)

lemma nda_eqI: 
  assumes "\<And>state sbe. (ndaTransition\<cdot>nda1) state sbe  = (ndaTransition\<cdot>nda2) state sbe"
    and "ndaInitConfig\<cdot>nda1 = ndaInitConfig\<cdot>nda2"
  shows "nda1 = nda2"
  by (simp add: assms(1) assms(2) below_antisym nda_belowI)



lemma ndastatesem_mono[simp]:"mono (\<lambda>h state. {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)

  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
             \<and>  fst (f sbe) \<in> h (fst (snd (f sbe))) })"
  apply(rule monoI)
  apply(simp add: prod.case_eq_if)
  apply(simp add: le_fun_def)
  by auto



definition ndaStateSem ::
 "('state::type, 'in::{chan, finite}, 'out::chan) ndAutomaton 
    \<Rightarrow> 'state \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaStateSem nda \<equiv> gfp (\<lambda>h state. {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)

  | f .  \<forall>sbe . \<comment> \<open>\<open>('state\<times>'out\<^sup>\<Omega>):\<close>\<close> 
                    snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
                \<comment> \<open>\<open>'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>:\<close>\<close>
                  \<and>  fst (f sbe) \<in> h (fst (snd (f sbe))) })"



text\<open>The abbreviation \<open>\<lbrakk> \<rbrakk>\<^sup>p\<close> for the state semantic of a total 
automaton is taken from \cite{Rum96}.\<close>

abbreviation ndastatesem_abbrev::
"('s::type, 'I::{finite,chan},'O) ndAutomaton \<Rightarrow>'s\<Rightarrow>('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set" 
("\<lbrakk>_\<rbrakk>\<^sup>p" [1000] 999) where "\<lbrakk>aut\<rbrakk>\<^sup>p \<equiv> ndaStateSem aut"


lemma ndastatesem_unfold:"(\<lbrakk>nda\<rbrakk>\<^sup>p) s = {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)

  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) s sbe)
             \<and>  fst (f sbe) \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) (fst (snd (f sbe))) }"
  unfolding ndaStateSem_def
  apply(subst gfp_unfold)
  using ndastatesem_mono apply auto[1]
  by auto

lemma ndastatesem_step: assumes "spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  shows "\<exists>spf2 output nextState. ((\<forall>sb. spf\<cdot>(sbe\<Zcat>\<^sup>\<surd>sb) = output \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb)) 
    \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) nextState
    \<and> (nextState,output) \<in> (ndaTransition\<cdot>nda) s sbe)"
  using assms apply(subst (asm) ndastatesem_unfold)
  apply auto
  by (smt case_prod_beta' surjective_pairing)

lemma ndastatesem_upper: assumes "\<And>s. Z s \<subseteq> {sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)

  | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) s sbe)
             \<and>  fst (f sbe) \<in> Z (fst (snd (f sbe))) }"
  shows "Z \<le> \<lbrakk>nda\<rbrakk>\<^sup>p"
  unfolding ndaStateSem_def
  apply(rule gfp_upperbound)
  apply(rule le_funI)
  using assms by simp

lemma ndastatesem_upper_h: assumes "\<And>s spf. spf \<in> Z s \<Longrightarrow> \<exists>f. spf = sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)
\<and> (\<forall>sbe. snd (f sbe) \<in> ((ndaTransition\<cdot>nda) s sbe)
             \<and>  fst (f sbe) \<in> Z (fst (snd (f sbe))))"
shows "Z \<le> \<lbrakk>nda\<rbrakk>\<^sup>p"
  apply(rule ndastatesem_upper)
  using assms by auto

lemma sbsplit_intro: assumes "\<And>sbe. spf oo (\<Lambda> sb. sbECons sbe sb) = f sbe"
    and "\<And>sb. #sb = 0 \<Longrightarrow> spf\<cdot>sb = \<bottom>"
  shows "spf = sb_step\<cdot>f"
  apply(rule cfun_eqI)
  apply(rename_tac "sb", case_tac "sb" rule: sb_cases2)
  apply (simp add: assms(2))
  by (metis assms(1) cfcomp2 eta_cfun sb_steps_sbe)

lemma assumes "\<And>s spf. spf \<in> Z s \<Longrightarrow> \<exists>f. (\<forall>sbe. spf oo  (\<Lambda> sb. sbECons sbe sb) = (\<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb))
\<and> (\<forall>sbe. snd (f sbe) \<in> ((ndaTransition\<cdot>nda) s sbe)
             \<and>  fst (f sbe) \<in> Z (fst (snd (f sbe))))"
  and "\<And>spf sb s . spf\<in>Z s \<Longrightarrow> sbLen sb = 0 \<Longrightarrow> spf\<cdot>sb = \<bottom>"
  shows "Z \<le> \<lbrakk>nda\<rbrakk>\<^sup>p"
  apply(rule ndastatesem_upper_h)
  oops
(* using sbsplit_intro by (metis assms(1) assms(2)) *)

lemma assumes "\<And>sbe. snd (f sbe) \<in> ((ndaTransition\<cdot>nda) s sbe)"
  and "\<And>sbe. fst (f sbe) \<in> ndaStateSem nda (fst (snd (f sbe)))"
  shows "sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb.
    let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb) \<in>(\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  using assms(1) assms(2) ndastatesem_unfold by force

lemma assumes "Rum_p = 
{h | h. (\<forall>s i. sbLen i=0 \<longrightarrow> h\<cdot>(s,i) = \<bottom>) \<and>
        (\<forall>m s. \<exists>t out. (t,out) \<in> ((ndaTransition\<cdot>aut) s m) \<and> 
                       (\<exists>h'\<in> Rum_p.
                          \<forall>i. h\<cdot>(s,m \<Zcat>\<^sup>\<surd> i) = out\<Zcat>\<^sup>\<Omega> h'\<cdot>(t,i)))}"
  shows "(\<lambda>h. ( \<Lambda> sb .  h\<cdot>(s,sb))) ` Rum_p \<subseteq> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  apply auto
  oops

lemma ndastate_complete: assumes "\<forall>sbe. \<exists>spf2 output nextState.
   ((spf oo  (\<Lambda> sb. sbECons sbe sb) = (sbConc output) oo spf2 
    \<and> spf2 \<in> ndaStateSem nda nextState
    \<and> (nextState,output) \<in> (ndaTransition\<cdot>nda) s sbe))"
  and "\<And>sb. sbLen sb = 0 \<Longrightarrow> spf\<cdot>sb = \<bottom>"
shows "spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  oops
(*
proof - 
(*  obtain spf2 out nextState where "\<And>sbe. spf oo (sbECons sbe) = (sbConc (out sbe)) oo (spf2 sbe)"
    and "\<And>sbe. (spf2 sbe) \<in> ndaStateSem nda (nextState sbe)"
    and "\<And>sbe. (nextState sbe,out sbe) \<in> (ndaTransition\<cdot>nda) s sbe"
    sorry (* FUUUCK! Hilbert_Choice.choice*)  *)
  obtain f where "\<forall>sbe. let (spf2, nextState, output) = f sbe in
  ((spf oo (sbECons sbe) = (sbConc output) oo spf2 
    \<and> spf2 \<in> ndaStateSem nda nextState
    \<and> (nextState,output) \<in> (ndaTransition\<cdot>nda) s sbe))"
    sorry
  have "\<And>sbe sb. spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) =
       (\<Lambda> (sb::'a\<^sup>\<Omega>). let (nextSPF::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>, state::'c, output::'b\<^sup>\<Omega>) = f sbe in output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)\<cdot>sb"
    sorry
  hence "spf = (sb_step\<cdot>(\<lambda> sbe. \<Lambda> sb. let (nextSPF, state, output) = f sbe in
                 output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb))"
    by(rule sbsplit_eqI, simp add: assms)
  thus ?thesis 
  using ndastatesem_upper 
  oops
*)

lemma ndastatesem_mono_h:
  assumes "(\<And>state sbe. (ndaTransition\<cdot>nda1) state sbe \<subseteq> (ndaTransition\<cdot>nda2) state sbe)"
  shows "\<lbrakk>nda1\<rbrakk>\<^sup>p \<le> \<lbrakk>nda2\<rbrakk>\<^sup>p"
  unfolding ndaStateSem_def
  apply(rule gfp_mono)
  apply(rule le_funI)
  apply auto
  using assms  by blast

lemma ndastatesem_monofun: "monofun ndaStateSem"
  apply(rule monofunI)
  apply(rule fun_belowI) 
  apply(subst less_set_def)
  using ndastatesem_mono_h nda_trans_mono
  by (metis le_funE) 

lemma ndastatesem_inempty_len_h: assumes "chDomEmpty TYPE('a::{chan,finite})"
  and "\<And> state sbe. \<forall> (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe). #out \<ge> 1"
  shows "\<forall>s spf. spf \<in> ndaStateSem nda s \<longrightarrow> #(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>"   
proof(rule contrapos_pp,simp+)
  assume a1: "\<exists>s spf. spf \<in> ndaStateSem nda s \<and> #(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) \<noteq> \<infinity>"
  obtain len_set where 
    len_set_def: "len_set = {#(spf\<cdot>\<bottom>) | spf s. spf \<in> ndaStateSem nda s}"
    by simp
  hence len_set_least: "\<exists>n \<in> len_set. \<forall>i \<in> len_set. n \<le> i"
    by (metis (mono_tags, lifting) LeastI_ex Least_le a1 mem_Collect_eq)

  then obtain state where 
    state_def: "\<exists>spf. spf \<in> ndaStateSem nda state \<and> (\<forall>n \<in> len_set. #(spf\<cdot>\<bottom>) \<le> n)"
    using len_set_def by blast
  then obtain spf where spf_def: "spf \<in> ndaStateSem nda state"
    and spf_len_def: "\<forall>n \<in> len_set. #(spf\<cdot>\<bottom>) \<le> n"
    by blast
  then have spf_len_inSet: "#(spf\<cdot>\<bottom>) \<in> len_set"
    using len_set_def by blast
  then have spf_inf: "#(spf\<cdot>\<bottom>) < \<infinity>"
    using a1 spf_len_def len_set_def
  proof -
    obtain cc :: "'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" and bb :: 'b where
      f1: "\<infinity> \<noteq> #(cc\<cdot>\<bottom>) \<and> cc \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) bb"
      by (metis (lifting) a1)
    then have "#(cc\<cdot>\<bottom>) \<in> len_set"
      using len_set_def by blast
    then show ?thesis
      using f1 by (metis (no_types) inf_ub leI less2eq spf_len_def)
  qed
  then obtain k where k_def: "Fin k = #(spf\<cdot>\<bottom>)"
    by (metis lnat_well_h2)

  obtain nextOutput nextSpf nextState where 
    nextOutput_def: 
        "spf\<cdot>((Abs_sbElem None)\<Zcat>\<^sup>\<surd>\<bottom>) = nextOutput \<Zcat>\<^sup>\<Omega> (nextSpf\<cdot>\<bottom>)
      \<and> nextSpf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) nextState
      \<and> (nextState,nextOutput) \<in> (ndaTransition\<cdot>nda) state (Abs_sbElem None)"
    by (meson ndastatesem_step spf_def)

  have nextOutput_len: "1 \<le> #nextOutput"
    using nextOutput_def assms(2)
    by fastforce

  have h0: "spf\<cdot>((Abs_sbElem None)\<Zcat>\<^sup>\<surd>\<bottom>) = nextOutput \<Zcat>\<^sup>\<Omega> (nextSpf\<cdot>\<bottom>)"
    using nextOutput_def by blast
  have h1: "(\<bottom>::'a\<^sup>\<Omega>) = (Abs_sbElem None)\<Zcat>\<^sup>\<surd>(\<bottom>::'a\<^sup>\<Omega>)"
    using assms(1) by simp

  have "#(nextSpf\<cdot>\<bottom>) \<in> len_set"
    using len_set_def nextOutput_def by blast
  then have nextSpf_len_def: "Fin k \<le> #(nextSpf\<cdot>\<bottom>)"
    using k_def spf_len_def by simp

  have k_contr: "Fin k < #(spf\<cdot>\<bottom>)"
    apply(subst h1)
    apply(simp add: h0)
    using nextOutput_len nextSpf_len_def sblen_sbconc
    spf_inf k_def le2lnle 
        lessequal_addition lnat_plus_commu lnat_plus_suc
    by (metis h0 h1 leD)

  show "False"
    using k_contr k_def lnless_def by blast
qed

lemma ndastatesem_inempty_len: 
  assumes "chDomEmpty TYPE('a::{chan,finite})"
  and "\<And> state sbe. 
    \<forall> (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe). #out \<ge> 1"
  and "spf \<in> ndaStateSem nda s"
  shows "#(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>"  
  using ndastatesem_inempty_len_h assms by blast

lemma ndastatesem_bottom[simp]:
  fixes sb::"'cs::{finite,chan}\<^sup>\<Omega>"
  assumes "\<not>sbHdElemWell (sb)"
  and "\<not> chDomEmpty TYPE('cs)"
  shows "spf \<in> ndaStateSem nda s \<longrightarrow> spf\<cdot>sb = \<bottom>"
  apply(subst ndastatesem_unfold)
  apply (simp add: sb_step_insert)
  using assms sbHdElem_h_cont.rep_eq sbHdElem_h_def 
    sb_steps_leastbot by blast

lemma ndastatesem_weak_len_h:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('in)"
  and "\<not>chDomEmpty TYPE('out)"
  and "# sb = Fin n"
  and "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe) 
    \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
  shows "spf \<in> ndaStateSem nda s \<Longrightarrow> #(spf\<cdot>sb) = #sb"
proof(induction sb arbitrary: s spf rule: sb_finind)
  case 1
  then show ?case 
    by(simp add: assms)
next
  case (2 sb)
  then show ?case 
    by (metis assms(1) assms(2) ndastatesem_bottom botsbleast sbleast2sblenempty)
next
  case (3 sbe sb)
  obtain s where s_def: "spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
    using "3.prems" by auto
  obtain nextOutput nextSpf nextState 
    where out_def: "spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = nextOutput \<Zcat>\<^sup>\<Omega> (nextSpf\<cdot>sb)"
    and nSpf_def: "nextSpf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) nextState"
    and nOut_def: "(nextState,nextOutput) \<in> (ndaTransition\<cdot>nda) s sbe"
    using ndastatesem_step s_def by fastforce
  then obtain outSBE 
    where outsbe_def: "nextOutput = sbe2sb outSBE"
    using nOut_def assms(4) by blast
  then show ?case
    apply(simp add: out_def outsbe_def) 
    using "3.IH" nSpf_def
    by (metis)
qed

lemma ndastatesem_weak_len:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('out)"  
      and "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
        \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
      and "spf \<in> ndaStateSem nda s"
    shows "#(spf\<cdot>sb) = #sb"
  apply (cases "chDomEmpty TYPE('in)")
   apply(subst (2) sbtypeepmpty_sbbot, simp)
  apply(subst (2) sblen_empty, simp)
  using ndastatesem_inempty_len assms sbe2sb_len_ex apply (metis case_prodI2)
  by (meson spf_weak_len ndastatesem_weak_len_h assms lnat_well_h2)

lemma ndastatesem_weak_h:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
    \<Longrightarrow> 1 \<le> #out"
  and "chDom TYPE ('in) = {}"
  and "spf \<in> ndaStateSem nda s"
shows "#(spf\<cdot>sb) = \<infinity>"
  apply(subst sbtypeepmpty_sbbot[of sb],simp add: assms)
proof(rule contrapos_pp,simp+)
  assume a1:"#(spf\<cdot>\<bottom>) \<noteq> \<infinity>"
  have "\<forall>k. Fin k < #(spf\<cdot>\<bottom>)"
  proof(auto)
    fix k::nat
    show "Fin k < #(spf\<cdot>\<bottom>)"
    using assms(3)
    proof(induction k arbitrary: spf s)
      case 0
      obtain spf2 ns out where spf2_def:"((spf\<cdot>\<bottom> = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>\<bottom>)) 
      \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) ns
      \<and> (ns,out) \<in> (ndaTransition\<cdot>nda) s (Abs_sbElem None))"
        apply(subgoal_tac "spf\<cdot>(\<bottom>) = spf\<cdot>(Abs_sbElem None \<Zcat>\<^sup>\<surd> \<bottom>)",simp)
         apply (metis "0.prems" ndastatesem_step sbconc_bot_r)
        apply(subst sbtypeempty_sbecons_bot)
        by(simp_all add: assms)
      then have "1\<le>#out"
        using assms(1) spf2_def by blast
      then show ?case
        apply(simp only: spf2_def)
        by (metis Fin_02bot gr_0 less2nat_lemma lnzero_def not_one_le_zero 
         one_lnat_def sbHdElem sbHd_reduce sbconctakedrop sbecons_len spf2_def)
    next
      case (Suc k)
      obtain spf2 ns out where spf2_def:"((spf\<cdot>\<bottom> = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>\<bottom>)) 
      \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) ns
      \<and> (ns,out) \<in> (ndaTransition\<cdot>nda) s (Abs_sbElem None))"
        apply(subgoal_tac "spf\<cdot>(\<bottom>) = spf\<cdot>(Abs_sbElem None \<Zcat>\<^sup>\<surd> \<bottom>)",simp)
         apply (metis Suc.prems ndastatesem_step sbconc_bot_r)
        apply(subst sbtypeempty_sbecons_bot)
        by(simp_all add: assms)
      then have "1\<le>#out"
        using assms(1) spf2_def by blast
      then show ?case
        apply(simp add: spf2_def)
        apply(subgoal_tac "#(spf2\<cdot>\<bottom>)+1 \<le> #(out \<Zcat>\<^sup>\<Omega> spf2\<cdot>\<bottom>)") 
        apply (smt Suc.IH dual_order.strict_trans2 less2lnleD less_lnsuc 
              ln_less lnat_plus_suc not_le_imp_less notinfI3 order.not_eq_order_implies_strict spf2_def)
        by (metis (no_types, opaque_lifting) add.commute dual_order.trans lessequal_addition order_refl sblen_sbconc)
    qed
  qed
  hence "#(spf\<cdot>\<bottom>) = \<infinity>"
    apply(subst lncases[of "#(spf\<cdot>\<bottom>)"],simp_all)
    by blast
  thus "False"
    using a1 by simp
qed

lemma ndastatesem_weak_fin:
  assumes "# sb = Fin n"
  assumes "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
    \<Longrightarrow> 1 \<le> #out"
  and "spf \<in> ndaStateSem nda s"
shows "# sb \<le> # (spf\<cdot>sb)"
  using assms(3)
  apply (induction sb arbitrary: s spf rule: sb_finind)
  apply (simp_all add: assms)
  apply (cases "chDomEmpty TYPE('a)")
  using assms(1) apply auto[1]
  using sbleast2sblenempty apply fastforce
proof-
  fix sbe::"'a\<^sup>\<surd>" and s and sb::"'a\<^sup>\<Omega>" and spf::"'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"
  assume a1:"(\<And>(s::'b) spf::'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>. spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s \<Longrightarrow> #sb \<le> #(spf\<cdot>sb))"
  assume a2:"chDom TYPE('a) \<noteq> {}"
  assume a4:"spf \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) s"
  obtain spf2 ns out where spf2_def:"((spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb)) 
         \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) ns
         \<and> (ns,out) \<in> (ndaTransition\<cdot>nda) s sbe)"
    by (meson a4 ndastatesem_step)
  then have "1\<le>#out"
        using assms(2) spf2_def by blast
  thus "#sb <\<^sup>l #(spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))"
    apply(simp add: spf2_def)
    apply(subgoal_tac "lnsuc\<cdot>(#(spf2\<cdot>sb)) \<le> #(out \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)")
    apply (meson a1 dual_order.trans lnsuc_lnle_emb spf2_def)
    by (metis add.commute dual_order.strict_trans2 leD le_less_linear 
        lessequal_addition lnat_plus_suc refl_lnle sblen_sbconc)
qed


theorem ndastatesem_weak:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"  
  assumes "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
              \<Longrightarrow> 1 \<le> #out"
    and "spf \<in> ndaStateSem nda s"
    shows "weak_well spf"
  apply (cases "chDomEmpty TYPE('in)")
  apply(rule spf_weakI)
   apply(subgoal_tac "#(spf\<cdot>sb) = \<infinity>",simp)
  using ndastatesem_weak_h assms apply metis
  apply(rule spf_weakI2,simp)
  using ndastatesem_weak_fin lncases
  by (metis assms(1) assms(2) lnat_well_h2)


definition ndaSem :: 
"('state::type, 'in::{chan, finite}, 'out::chan) ndAutomaton 
  \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaSem nda \<equiv> {(\<Lambda> sb. initOut \<Zcat>\<^sup>\<Omega> spf\<cdot>sb) | initOut initState spf.
                    (initState,initOut) \<in> ndaInitConfig\<cdot>nda 
                      \<and> spf\<in>ndaStateSem nda initState}"

text\<open>The abbreviation \<open>\<lbrakk> \<rbrakk>\<^sup>c\<close> for the semantic of a total automaton is 
defined identical to \cite{Rum96}.\<close>

abbreviation ndasem_abbrev::
"('s::type, 'I::{finite,chan},'O) ndAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) set" 
("\<lbrakk>_\<rbrakk>\<^sup>c" [1000] 999) where "\<lbrakk>aut\<rbrakk>\<^sup>c \<equiv> ndaSem aut"


lemma ndasem_pred:assumes"spf \<in> \<lbrakk>nda\<rbrakk>\<^sup>c"
  shows"\<exists>initState initOut. (initState,initOut)\<in>ndaInitConfig\<cdot>nda \<and>
        (\<exists>spf2\<in>(\<lbrakk>nda\<rbrakk>\<^sup>p) initState.
          spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
  using assms
  apply(simp add: ndaSem_def)
  by auto+

lemma ndasem_unfold_pred:
  assumes "spf \<in> \<lbrakk>nda\<rbrakk>\<^sup>c"
    and "\<And>initState initOut spf2. (initState,initOut) \<in> (ndaInitConfig\<cdot>nda) 
         \<Longrightarrow> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) initState 
         \<Longrightarrow> P (initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
  shows "P (spf\<cdot>sb)"
  by (metis assms(1) assms(2) ndasem_pred)
  
lemma ndasem_mono_h: 
  assumes "\<And>state.(\<lbrakk>nda1\<rbrakk>\<^sup>p) state \<subseteq>(\<lbrakk>nda2\<rbrakk>\<^sup>p) state"
    and "ndaInitConfig\<cdot>nda1 \<subseteq> ndaInitConfig\<cdot>nda2"
  shows "\<lbrakk>nda1\<rbrakk>\<^sup>c \<subseteq> \<lbrakk>nda2\<rbrakk>\<^sup>c"
  unfolding ndaSem_def using assms(1) assms(2) by blast

lemma ndasem_mono: "monofun ndaSem"
  apply(rule monofunI, subst less_set_def)
  apply(rule ndasem_mono_h)
  apply (metis le_funE nda_trans_mono ndastatesem_mono_h)
  by (simp add: nda_init_mono)

lemma ndasem_inempty_len_h: assumes "chDomEmpty TYPE('a::{chan,finite})"
  and "\<And> state sbe. \<forall> (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe). #out \<ge> 1"
shows "\<forall>spf \<in> ndaSem nda. #(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>" 
proof
  fix spf
  assume a1: "spf \<in> ndaSem nda"
  obtain spf2 where spf2_def: 
    "\<exists>initState initOut. ((initState,initOut)\<in>ndaInitConfig\<cdot>nda
    \<and> spf2\<in>(ndaStateSem nda initState)
    \<and> (\<forall>sb. spf\<cdot>sb = (initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)))"
    using a1 apply(simp add: ndaSem_def)
    by fastforce
  then have "#(spf2\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>"
    using ndastatesem_inempty_len_h assms
    by blast
  then show "#(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>"
    using spf2_def sblen_sbconc
    by (metis inf_less_eq plus_lnatInf_l) 
qed

lemma ndasem_inempty_len: 
  assumes "chDomEmpty TYPE('a::{chan,finite})"
  and "\<And> state sbe. \<forall> (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe). 
      #out \<ge> 1"
  and "spf \<in> ndaSem nda"
shows "#(spf\<cdot>(\<bottom>::'a\<^sup>\<Omega>)) = \<infinity>"
  using ndasem_inempty_len_h assms by blast

lemma ndasem_weak_len:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not> chDomEmpty TYPE('out)"
  and "nda_weak = ndai2ndac (ndAw2nda nda_w)"
  and "ndawInitConfig (nda_w) \<noteq> {}"
  and "\<And> state sbe. ndawTransition nda_w state sbe \<noteq> {}"
  and "spf \<in> \<lbrakk>nda_weak\<rbrakk>\<^sup>c"
shows "#(spf\<cdot>sb) = #sb"
proof - 
  obtain initState initOut spf2 
    where initConfig_def: "((initState,initOut)\<in>(ndaInitConfig\<cdot>nda_weak))"
    and spf2_def: "spf2\<in>(ndaStateSem nda_weak initState)"
    and initOut_def: "(spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
    using assms ndasem_pred by (metis (full_types, opaque_lifting))
  have h1: "initOut = \<bottom>"
    using initConfig_def
    by(auto simp add: ndaInitConfig.rep_eq assms ndai2ndac.rep_eq 
        ndAw2nda_def)
  have h2: "\<And> state sbe s out. 
    (s,out) \<in> ((ndaTransition\<cdot>nda_weak) state sbe)
    \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
    by(auto simp add: assms(2) assms(4) ndaTransition.rep_eq 
        ndai2ndac.rep_eq ndAw2nda_def)
  show ?thesis
    apply(simp add: initOut_def h1)
    apply(rule ndastatesem_weak_len 
        [where nda="nda_weak", where s="initState"])
    by(simp_all add: assms(1) h2 spf2_def)
qed

lemma ndasem_weak_len2:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('out)"  
      and "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
        \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
      and "spf \<in> ndaSem nda"
      and "\<forall>s. s \<in>(ndaInitConfig\<cdot>nda) \<longrightarrow> snd s = \<bottom>"
    shows "#(spf\<cdot>sb) = #sb"
proof - 
  obtain initState initOut spf2 
    where initConfig_def: "((initState,initOut)\<in>(ndaInitConfig\<cdot>nda))"
    and spf2_def: "spf2\<in>(ndaStateSem nda initState)"
    and initOut_def: "(spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
    using assms ndasem_pred by (metis (full_types, opaque_lifting))
  have h1: "initOut = \<bottom>"
    using assms(4) initConfig_def by auto
  show ?thesis
    apply(simp add: initOut_def h1)
    apply(rule ndastatesem_weak_len 
        [where nda="nda", where s="initState"])
    by (simp_all  add: assms spf2_def)
qed

lemma ndasem_strong_len:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not> chDomEmpty TYPE('out)"
  and "nda_strong = ndai2ndac (ndAs2nda nda_s)"
  and "ndasInitConfig (nda_s) \<noteq> {}"
  and "\<And> state sbe. ndasTransition nda_s state sbe \<noteq> {}"
  and "spf \<in> \<lbrakk>nda_strong\<rbrakk>\<^sup>c"
  shows "#(spf\<cdot>sb) = lnsuc\<cdot>(#sb)"
proof - 
  obtain initState initOut spf2 
    where initConfig_def: "((initState,initOut)\<in>(ndaInitConfig\<cdot>nda_strong))"
    and spf2_def: "spf2\<in>(ndaStateSem nda_strong initState)"
    and initOut_def: "(spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
    using assms ndasem_pred by (metis (full_types, opaque_lifting))
  have h1: "\<exists>outSBE. initOut = sbe2sb outSBE"
    using initConfig_def
    by(auto simp add: ndaInitConfig.rep_eq assms ndai2ndac.rep_eq 
        ndAs2nda_def)
  then have h2: "#(initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb) = lnsuc\<cdot>(#(spf2\<cdot>sb))"
    by (metis sbecons_len)
  have h3: "\<And> state sbe s out. 
    (s,out) \<in> ((ndaTransition\<cdot>nda_strong) state sbe)
    \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
    by(auto simp add: assms(2) assms(4) ndaTransition.rep_eq 
        ndai2ndac.rep_eq ndAs2nda_def)
  show ?thesis
    apply(simp add: initOut_def h2)
    apply(rule ndastatesem_weak_len 
        [where nda="nda_strong", where s="initState"])
    by(simp_all add: assms(1) h3 spf2_def)
qed

lemma ndasem_strong_len2:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('out)"  
      and "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
        \<Longrightarrow> \<exists>outSBE. out = sbe2sb outSBE"
      and "spf \<in> ndaSem nda"
      and "\<forall>s. s \<in>(ndaInitConfig\<cdot>nda) \<longrightarrow> (\<exists>outSBE. snd s = sbe2sb outSBE)"
    shows "#(spf\<cdot>sb) = lnsuc\<cdot>(#sb)"
proof - 
  obtain initState initOut spf2 
    where initConfig_def: "((initState,initOut)\<in>(ndaInitConfig\<cdot>nda))"
    and spf2_def: "spf2\<in>(ndaStateSem nda initState)"
    and initOut_def: "(spf\<cdot>sb = initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb)"
    using assms ndasem_pred by (metis (full_types, opaque_lifting))
  have h1: "\<exists>outSBE. initOut = sbe2sb outSBE"
    using assms(4) initConfig_def by auto
  then have h2: "#(initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb) = lnsuc\<cdot>(#(spf2\<cdot>sb))"
    by (metis sbecons_len)
  show ?thesis
    apply(simp add: initOut_def h2)
    apply(rule ndastatesem_weak_len 
        [where nda="nda", where s="initState"])
    by(simp_all add: assms spf2_def)
qed


theorem ndasem_weak:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"  
  assumes "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
    \<Longrightarrow> 1 \<le> #out"
  and "spf \<in> ndaSem nda"
  shows "weak_well spf"
proof(insert assms(2),simp add: ndaSem_def)
  assume a1:"\<exists>(initOut::'out\<^sup>\<Omega>) (initState::'a) spfa::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
       spf = (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut \<Zcat>\<^sup>\<Omega> spfa\<cdot>sb) \<and>
       (initState, initOut) \<in> ndaInitConfig\<cdot>nda \<and> spfa \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) initState"
  then obtain initOut initState spf2 where spf2_def:"spf = (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb) \<and>
       (initState, initOut) \<in> ndaInitConfig\<cdot>nda \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) initState" 
    by blast
  have "weak_well spf2"
  by(rule ndastatesem_weak[where nda=nda and s="initState"],simp_all add: assms spf2_def)
  thus "weak_well spf"
    apply(subgoal_tac "\<forall>sb. #(spf2\<cdot>sb) \<le> #(spf\<cdot>sb)")
    apply (meson trans_lnle weak_well_def)
    apply(simp add: spf2_def)
    by (metis (no_types, lifting) add.right_neutral dual_order.trans 
        lessequal_addition lnat_plus_commu lnmin_smaller_addition order_refl 
        sblen_sbconc strict_lnmin_snd)
qed



theorem ndasem_strong:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"  
  assumes "\<And> state sbe s out. (s,out) \<in> ((ndaTransition\<cdot>nda) state sbe)
    \<Longrightarrow> 1 \<le> #out"
  and "\<And>s out. (s,out) \<in> (ndaInitConfig\<cdot>nda) \<Longrightarrow> 1\<le>#out"
  and "spf \<in> ndaSem nda"
  shows "strong_well spf"
proof(insert assms(3),simp add: ndaSem_def)
  assume a1:"\<exists>(initOut::'out\<^sup>\<Omega>) (initState::'a) spfa::'in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>.
       spf = (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut \<Zcat>\<^sup>\<Omega> spfa\<cdot>sb) \<and>
       (initState, initOut) \<in> ndaInitConfig\<cdot>nda \<and> spfa \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) initState"
  then obtain initOut initState spf2 where spf2_def:"spf = (\<Lambda> (sb::'in\<^sup>\<Omega>). initOut \<Zcat>\<^sup>\<Omega> spf2\<cdot>sb) \<and>
       (initState, initOut) \<in> ndaInitConfig\<cdot>nda \<and> spf2 \<in> (\<lbrakk>nda\<rbrakk>\<^sup>p) initState" 
    by blast
  have initlen:"1\<le>#initOut"
    using assms(2) spf2_def by blast
  have "weak_well spf2"
   by(rule ndastatesem_weak[where nda=nda and s="initState"],simp_all add: assms spf2_def)
  thus "strong_well spf"
    apply(subgoal_tac "\<forall>sb. lnsuc\<cdot>(#(spf2\<cdot>sb)) \<le> #(spf\<cdot>sb)")
    apply (meson dual_order.trans lnsuc_lnle_emb spf_strongI weak_well_def)
    apply(simp add: spf2_def)
    by (metis (no_types, opaque_lifting) dual_order.trans initlen 
        lessequal_addition lnat_plus_commu lnat_plus_suc order_refl 
        sblen_sbconc)
qed




paragraph \<open>Literature Semantic Mapping \\\<close> text\<open>\label{nsemrum}\<close>


function Rum_p::"('s::discrete_cpo, 'in,'out) ndAutomaton 
\<Rightarrow> (('s\<times>'in\<^sup>\<Omega>)\<rightarrow>'out\<^sup>\<Omega>) set" where
"Rum_p aut = 
{h | h. (\<forall>s i. #i=0 \<longrightarrow> h\<cdot>(s,i) = \<bottom>) \<and>
        (\<forall>m s. \<exists>t out. (t,out) \<in> ((ndaTransition\<cdot>aut) s m) \<and> 
                       (\<exists>h'\<in> Rum_p aut.
                          \<forall>i. h\<cdot>(s,m \<Zcat>\<^sup>\<surd> i) = out\<Zcat>\<^sup>\<Omega> h'\<cdot>(t,i)))}"
  by(simp)+

text\<open>The semantic mapping @{const Rum_p} is defined analog to \<open>\<lbrakk> \<rbrakk>\<^sup>p\<close>
\cite{Rum96} and calls itself recursively to allow model 
\gls{nondeterministic} behaviour with its set of \glspl{spf}.
In each step, an non-empty input is processed according to the 
\gls{nondeterministic} transition function. Thus, the output in one
step can be different, from the output in the next step, even if the
input and state of the automaton are the same.\<close>

fun Rum_c::"('s::discrete_cpo, 'in,'out) ndAutomaton 
\<Rightarrow> ('in\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>) set" where
"Rum_c aut = {g | g. \<exists>h\<in>(Rum_p aut). \<exists>s\<^sub>i out\<^sub>i. 
                        (s\<^sub>i,out\<^sub>i)\<in>(ndaInitConfig\<cdot>aut)\<and>
                        (\<forall>i. g\<cdot>i = out\<^sub>i \<Zcat>\<^sup>\<Omega> h\<cdot>(s\<^sub>i,i))}"

text\<open>Also the semantic mapping \<open>\<lbrakk> \<rbrakk>\<^sup>c\<close> defines all possible 
\gls{nondeterministic} behaviour of the automaton, because its 
elements cover all possible combinations of initial configurations 
and \glspl{spf} from @{const Rum_p}. The input is the completely 
processed by the chosen \gls{spf} form @{const Rum_p}.\<close>

lemma 
  assumes "Rum_prec aut = {h | h. (\<forall>s i. sbLen i=0 \<longrightarrow> h\<cdot>(s,i) = \<bottom>)\<and>
        (\<forall>m s. \<exists>t out. (t,out) \<in> ((ndaTransition\<cdot>aut) s m) \<and> 
                       (\<exists>h'\<in> Rum_prec aut.
                          \<forall>i. h\<cdot>(s,m \<Zcat>\<^sup>\<surd> i) = out\<Zcat>\<^sup>\<Omega> h'\<cdot>(t,i)))}"
  shows"(\<lambda>f. \<Lambda>(s,sb). f s\<cdot>sb)`setify (ndaStateSem aut) \<subseteq> Rum_prec aut"
  apply(subst assms ndaStateSem_def,auto simp add: setify_def)
  oops

paragraph \<open>New Semantic Mapping\<close>

definition ndaStateSem_helper::"('s::type, 'in::{chan, finite}, 'out) ndAutomaton
  \<Rightarrow> ('s \<Rightarrow> (('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set)) \<Rightarrow> 's \<Rightarrow>   (('in\<^sup>\<surd> \<Rightarrow> (('in \<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) \<times> 's \<times>  'out\<^sup>\<Omega>)) set)" where
"ndaStateSem_helper nda h state = {f | f .  \<forall>sbe . snd (f sbe) \<in> ((ndaTransition\<cdot>nda) state sbe)
             \<and>  fst (f sbe) \<in> h (fst (snd (f sbe))) }" 

definition ndaStateSem2 ::
 "('s::type, 'in::{chan, finite}, 'out) ndAutomaton 
    \<Rightarrow> 's \<Rightarrow> ('in\<^sup>\<Omega> \<rightarrow> 'out\<^sup>\<Omega>) set" where
"ndaStateSem2 nda \<equiv> gfp (\<lambda>h state.  
  (\<lambda>trans. sb_step\<cdot>(\<lambda>sbe . \<Lambda> sb . (snd (snd( trans sbe))) \<Zcat>\<^sup>\<Omega> ((fst (trans sbe))\<cdot>sb))) `
  (ndaStateSem_helper nda h state))"

lemma ndastatesem2_helper_mono: "mono (ndaStateSem_helper nda)"
  apply(rule monoI)
  apply(simp add: ndaStateSem_helper_def le_fun_def)
  by blast

lemma ndastatesem2_mono: "mono (\<lambda>h state.  
  (\<lambda>trans. sb_step\<cdot>(\<lambda>sbe . \<Lambda> sb . (snd (snd( trans sbe))) \<Zcat>\<^sup>\<Omega> ((fst (trans sbe))\<cdot>sb))) `
  (ndaStateSem_helper nda h state))"
proof(rule monoI)
  fix x::"'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set"
  and y::"'a \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) set"
  assume a0: "x \<le> y"
  then have a1: "\<And>xa. x xa \<subseteq> y xa"
    by(simp add: le_fun_def)
  then have a2: "\<And> state. (ndaStateSem_helper nda x state) \<subseteq> (ndaStateSem_helper nda y state)"
    using ndastatesem2_helper_mono a0 by (simp add: ndastatesem2_helper_mono le_funD monoD)
  show "(\<lambda>state::'a.
           (\<lambda>trans::'b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>.
               sb_step\<cdot>(\<lambda>sbe::'b\<^sup>\<surd>. \<Lambda> (sb::'b\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
           ndaStateSem_helper nda x state)
       \<le> (\<lambda>state::'a.
              (\<lambda>trans::'b\<^sup>\<surd> \<Rightarrow> ('b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>) \<times> 'a \<times> 'c\<^sup>\<Omega>.
                  sb_step\<cdot>(\<lambda>sbe::'b\<^sup>\<surd>. \<Lambda> (sb::'b\<^sup>\<Omega>). snd (snd (trans sbe)) \<Zcat>\<^sup>\<Omega> fst (trans sbe)\<cdot>sb)) `
              ndaStateSem_helper nda y state)"
    apply(simp add: le_fun_def)
    using a2 by (simp add: image_mono)
qed

lemma ndastatesem_eq: "ndaStateSem (nda::('a::type, 'b::{chan, finite},'c) ndAutomaton) = ndaStateSem2 nda"
  apply(simp add: ndaStateSem_def ndaStateSem2_def ndaStateSem_helper_def)
  apply(simp add: case_prod_beta')
  by (simp add: setcompr_eq_image)

lemma otherstatesem_def_h:"{sb_step\<cdot>(\<lambda>sbe. \<Lambda> sb. snd (snd (f sbe)) \<Zcat>\<^sup>\<Omega> fst (f sbe)\<cdot>sb) |
             f.
             \<forall>sbe2. snd (f sbe2) \<in> (ndaTransition\<cdot>nda) state sbe2 \<and> fst (f sbe2) \<in> h (fst (snd (f sbe2)))}
   = {sb_step\<cdot>f
  | f. \<forall>sbe. \<exists>output nextSPF nextState. 
   (nextState,output) \<in> (ndaTransition\<cdot>nda) state sbe
    \<and>  nextSPF \<in> h nextState 
    \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)}"
  apply(auto)
  apply(rule_tac x="(\<lambda>sbe. \<Lambda> sb. snd (snd (f sbe)) \<Zcat>\<^sup>\<Omega> fst (f sbe)\<cdot>sb)" in exI,auto)
  apply(rule_tac x="snd(snd (f sbe))" in exI)
  apply(rule_tac x="fst (f sbe)" in exI)
proof(rule_tac x="fst (snd (f sbe))" in exI,auto)
  fix f::"'a\<^sup>\<surd> \<Rightarrow> 'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>"
  assume a1:" \<forall>sbe::'a\<^sup>\<surd>.
          \<exists>(output::'b\<^sup>\<Omega>) (nextSPF::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) nextState::'c.
             (nextState, output) \<in> (ndaTransition\<cdot>nda) state sbe \<and>
             nextSPF \<in> h nextState \<and> (\<forall>sb::'a\<^sup>\<Omega>. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)"
  obtain outf statef nspf where outf_def:"\<forall>sbe. \<exists>(output::'b\<^sup>\<Omega>) (nextSPF::'a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) nextState::'c.
             (nextState, output) \<in> (ndaTransition\<cdot>nda) state sbe \<and>
             nextSPF \<in> h nextState \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb) \<and> outf sbe = (output) \<and> statef sbe = nextState \<and> nspf sbe = nextSPF"
    using a1
    by (metis)
  then obtain newf where nf_def:"newf =(\<lambda>sbe. (nspf sbe, (statef sbe, outf sbe)))"
    by simp
  thus "\<exists>fa::'a\<^sup>\<surd> \<Rightarrow> ('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>) \<times> 'c \<times> 'b\<^sup>\<Omega>.
          sb_step\<cdot>f = sb_step\<cdot>(\<lambda>sbe::'a\<^sup>\<surd>. \<Lambda> (sb::'a\<^sup>\<Omega>). snd (snd (fa sbe)) \<Zcat>\<^sup>\<Omega> fst (fa sbe)\<cdot>sb) \<and>
          (\<forall>sbe2::'a\<^sup>\<surd>. snd (fa sbe2) \<in> (ndaTransition\<cdot>nda) state sbe2 \<and> fst (fa sbe2) \<in> h (fst (snd (fa sbe2))))" 
    apply(rule_tac x="newf" in exI,auto simp add: nf_def)
    apply(rule sbsplit_eqI)
    using outf_def by simp_all
qed


lemma otherStateSem_def:"ndaStateSem nda = gfp (\<lambda>h state. 
  {sb_step\<cdot>f | f. \<forall>sbe. \<exists>output nextSPF nextState. 
     (nextState,output) \<in> (ndaTransition\<cdot>nda) state sbe
      \<and>  nextSPF \<in> h nextState 
      \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)
  })"
  by(simp add: ndaStateSem_def case_prod_unfold Let_def otherstatesem_def_h)


lemma otherstatesem_def_h2:"{sb_step\<cdot>f
  | f. \<forall>sbe. \<exists>output nextSPF nextState. 
   (nextState,output) \<in> (ndaTransition\<cdot>nda) state sbe
    \<and>  nextSPF \<in> h nextState 
    \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb)}
   = {sb_step\<cdot>f
  | f. \<forall>sbe. \<exists>output nextState. 
   (nextState,output) \<in> (ndaTransition\<cdot>nda) state sbe
    \<and>  (\<exists>nextSPF. nextSPF \<in> h nextState 
    \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb))}"
  by blast


theorem otherStateSem_def2: "ndaStateSem nda = gfp(\<lambda>h state. 
  {sb_step\<cdot>f | f. \<forall>sbe. \<exists>output nextState. 
   (nextState,output) \<in> (ndaTransition\<cdot>nda) state sbe
    \<and>  (\<exists> nextSPF. nextSPF \<in> h nextState 
    \<and> (\<forall>sb. f sbe\<cdot>sb = output \<Zcat>\<^sup>\<Omega> nextSPF\<cdot>sb))})"
  by(simp add: otherStateSem_def otherstatesem_def_h2)


lemma statesem_unfold_pred:
  assumes"(\<And>spf out nstate. (nstate,out)\<in> (ndaTransition\<cdot>aut) s sbe 
               \<Longrightarrow> spf \<in> ndaStateSem aut nstate 
               \<Longrightarrow> P(out \<Zcat>\<^sup>\<Omega> (spf\<cdot>sb)))"
  and "spf\<in>ndaStateSem aut s"
  shows "P (spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb))"
proof-
  obtain spf2 out ns where spf2_def:"spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = out \<Zcat>\<^sup>\<Omega> (spf2\<cdot>sb) \<and> spf2\<in>ndaStateSem aut ns 
                                     \<and> (ns,out)\<in>(ndaTransition\<cdot>aut) s sbe"
    by (meson assms(2) ndastatesem_step)
  thus ?thesis
    by(auto simp add: assms)
qed


end
