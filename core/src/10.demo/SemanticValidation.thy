theory SemanticValidation
imports stream.eventStream stream.StreamAutomaton sps.SPS

begin

default_sort type


class lenconc = len + conc + 
  assumes inject_conc:"\<And>x y z. #x < \<infinity> \<Longrightarrow> x \<Zcat>\<Zcat> y = x \<Zcat>\<Zcat> z \<Longrightarrow> y = z" 
  and len_conc[simp]:"\<And>a b. #a=\<infinity> \<Longrightarrow> a \<Zcat>\<Zcat> b = a"

  and conc_suf_ex:"\<And>a b. a \<sqsubseteq> b \<Longrightarrow> \<exists>t. a\<Zcat>\<Zcat>t = b"
  and conc_suf_prev:"\<And>x y. x \<sqsubseteq> x \<Zcat>\<Zcat> y"

begin
lemma inf_eqI: assumes "#x = \<infinity>" and "x \<sqsubseteq> y" shows "y = x"
proof - 
  obtain t where t_def: "x \<Zcat>\<Zcat> t = y" 
    using assms(2) local.conc_suf_ex by blast
  show ?thesis
    unfolding t_def[symmetric]
    apply(rule len_conc)
    using assms(1) .
qed
end

locale stream_similar =
  fixes uhd::"'u::{lenconc} \<rightarrow> 'msg::type lift" 
    and urt::"'u \<rightarrow> 'u" 
    and uup::"'msg \<Rightarrow> 'u" 
  assumes uhd_umsg:"\<And>msg. uhd\<cdot>(uup msg) = Def msg"
  assumes urt_uup:"\<And>input msg. urt\<cdot>((uup msg) \<Zcat>\<Zcat> input) = input"

  and uind:  "\<And>P x. adm P \<Longrightarrow> P \<bottom>
            \<Longrightarrow> (\<And>msg input. P input \<Longrightarrow> P ((uup msg) \<Zcat>\<Zcat> input)) 
            \<Longrightarrow> P x"
  and uhd_strict[simp]: "uhd\<cdot>\<bottom> = \<bottom>"
begin

definition diff::"('u \<rightarrow> 'out) \<Rightarrow> ('u \<Rightarrow> 'msg \<Rightarrow> 'out::{pcpo,lenconc})"where
"diff spf u msg = (if #(spf\<cdot>u) = \<infinity> then \<bottom> else (THE rt. spf\<cdot>u \<Zcat>\<Zcat> rt = spf\<cdot>(u \<Zcat>\<Zcat> (uup msg))))"

lemma diff_eps[simp]:assumes"#(spf\<cdot>s) = \<infinity>"
  shows "diff spf s a = \<bottom>"
  by(simp add: assms diff_def)

lemma diff_eqI[simp]:assumes "#(spf\<cdot>s)<\<infinity>"
      and "spf\<cdot>(s\<Zcat>\<Zcat> uup a) = spf\<cdot>s \<Zcat>\<Zcat> y"
  shows"(diff spf) s a = y" 
  apply(cases "#(spf\<cdot>s)")
  apply(auto simp add: assms diff_def)
  apply(rule the_equality)
  apply(simp add: assms )
  using inject_conc assms apply blast
  using assms(1) by simp

lemma diff2spf:"spf\<cdot>s \<Zcat>\<Zcat> diff spf s a = spf\<cdot>(s \<Zcat>\<Zcat> uup a)"
  apply(cases "#(spf\<cdot>s)",auto)
  apply(simp add: diff_def)
  apply(rule theI',auto)
  apply(subgoal_tac "spf\<cdot>s \<sqsubseteq> spf\<cdot>(s \<Zcat>\<Zcat> uup a)")
  using conc_suf_ex apply blast
  using cont_pref_eq1I apply (metis botconc2 minimal)
  apply (metis LNat.lnat.distinct(1) inf_ub inject_conc lnle_conv lnless_def)
  using conc_suf_prev 
  by (metis conc_suf_ex cont_pref_eq1I lenconc_class.len_conc)



text\<open>Using @{const diff} a transition can be defined for any \gls{spf} by using the input domain as
the state space. The current state in a run is equivalent to the processed input stream. The next 
output can then be defined by @{const diff} of the spf, the state and the input element.\<close> 
fun spfTransition::"('u \<rightarrow> 'out) \<Rightarrow> 'u \<Rightarrow> 'msg \<Rightarrow> ('u\<times>'out::{pcpo,lenconc})"where
"spfTransition spf i a = (i \<Zcat>\<Zcat> uup a,diff spf i a)"

fun spfInitConfig::"('u \<rightarrow> 'out::{cpo}) \<Rightarrow> 'u \<times> 'out" where
"spfInitConfig spf = (\<bottom>,spf\<cdot>\<bottom>)"

definition "spfAutomaton spf = (|dautTransition =  spfTransition spf, dautInitConfig = spfInitConfig spf|)"

definition ustep::"('msg \<Rightarrow> 'u \<rightarrow> 'out) \<rightarrow> 'u \<rightarrow> 'out::pcpo" where
"ustep  = (\<Lambda> f input. case (uhd\<cdot>input) of Def msg \<Rightarrow> f msg\<cdot>(urt\<cdot>input) | 
                                            _ \<Rightarrow> \<bottom> )"

lemma "ustep = (\<Lambda> f input. (case_lift \<bottom> (\<lambda>msg. f msg\<cdot>(urt\<cdot>input)) (uhd\<cdot>input)))"
  by (simp add: ustep_def)

thm strictify_def
declare cont2cont_case_lift [cont2cont]


lemma flat_cfun_eqI: fixes f::"'x::cpo \<rightarrow> 'a lift"
  shows  "f\<cdot>x \<noteq> \<bottom> \<Longrightarrow> x\<sqsubseteq>y \<Longrightarrow> f\<cdot>y = f\<cdot>x"
  apply(rule flat_eqI[symmetric])
   apply (simp add: monofun_cfun_arg)
  .

lemma ustep_bot[simp]: "ustep\<cdot>f\<cdot>\<bottom> = \<bottom>" 
  and ustep_step [simp]: "ustep\<cdot>f\<cdot>(uup msg \<Zcat>\<Zcat> ls) = f msg\<cdot>ls"
  unfolding ustep_def
   apply(subst beta_cfun, intro cont2cont, simp)+
  apply(subst flat_cfun_eqI [where y="uup msg\<Zcat>\<Zcat>ls" and x="uup msg"])
    by (simp add: uhd_umsg conc_suf_prev urt_uup)+
  

lemma spfautstatesem_def:"spf\<cdot>s \<Zcat>\<Zcat> daStateSem ustep (spfAutomaton spf) s\<cdot>i = spf\<cdot>(s \<Zcat>\<Zcat> i)"
  apply(cases "#(spf\<cdot>s) = \<infinity>")
     apply simp_all
   apply(rule inf_eqI[symmetric])
  apply simp
   apply (meson conc_suf_prev cont_pref_eq1I)
  apply(induction i arbitrary: s rule: uind)
proof-
  fix a::'b and i s::"'b stream" and x1::nat and spf::"'b stream \<rightarrow> 'a stream"
  assume hypo:"(\<And>(x1::nat) (s::'b stream).
           #(spf\<cdot>s) = Fin x1 \<Longrightarrow> spf\<cdot>s \<Zcat> daStateSem stream_step (spfAutomaton spf) s\<cdot>i = spf\<cdot>(s \<Zcat> i))"
  and "#(spf\<cdot>s) = Fin x1"
  have diff_insert:"spf\<cdot>s \<Zcat> diff spf (s, a) = spf\<cdot>(s \<Zcat> \<up>a)"
    using diff2spf by blast
  then have diff_insert_assoc:"\<And>rt. spf\<cdot>s \<Zcat> diff spf (s, a) \<Zcat> rt = spf\<cdot>(s\<Zcat>\<up>a) \<Zcat> rt"
    apply(subst diff_insert[symmetric])
    by (metis assoc_sconc)
  show "spf\<cdot>s \<Zcat> diff spf (s, a) \<Zcat> daStateSem stream_step (spfAutomaton spf) (s \<Zcat> \<up>a)\<cdot>i = spf\<cdot>(s \<Zcat> \<up>a \<Zcat> i)"
    apply (simp add: diff_insert_assoc)
    apply(cases "#(spf\<cdot>(s \<Zcat> \<up>a))")
    apply(simp_all add: hypo)
    by (metis assoc_sconc monofun_spf_ubl)
qed


text\<open>Converting any \gls{spf} using @{const spfTransition} and @{const spfInitConfig} results in a
semantically equivalent automaton.\<close>

theorem spfautsem_def:"daSem stream_step (spfAutomaton spf) = spf"
  apply(rule cfun_eqI)
  apply(simp add: dasem_unfold)
  apply(subst(1) spfAutomaton_def) 
  apply(subst(2) spfAutomaton_def) apply (simp)
  by(subst spfautstatesem_def,simp)



end

default_sort countable




definition diff::"('a::{countable} stream \<rightarrow> 'b::{countable} stream) \<Rightarrow> (('a stream \<times> 'a) \<Rightarrow> 'b stream)"where
"diff spf \<equiv> \<lambda>(x,y). (case #(spf\<cdot>x) of \<infinity> \<Rightarrow> \<epsilon> | _ \<Rightarrow> (THE rt. spf\<cdot>x \<Zcat> rt = spf\<cdot>(x \<Zcat> \<up>y)))"

lemma diff_eps[simp]:assumes"#(spf\<cdot>s) = \<infinity>"
  shows "diff spf (s,a) = \<epsilon>"
  by(simp add: assms diff_def)

lemma diff_eqI[simp]:assumes "#(spf\<cdot>s)<\<infinity>"
      and "spf\<cdot>s = x"
      and "spf\<cdot>(s\<Zcat>\<up>a) = x \<Zcat> y"
  shows"(diff spf) (s,a) = y" 
  apply(cases "#(spf\<cdot>s)")
  apply(auto simp add: assms diff_def)
  apply(rule the_equality)
  apply(simp add: assms )
  using inject_sconc assms by auto

lemma diff2spf:"spf\<cdot>s \<Zcat> diff spf (s, a) = spf\<cdot>(s\<Zcat> \<up>a)"
  apply(cases "#(spf\<cdot>s)",auto)
  apply(simp add: diff_def)
  apply(rule theI',auto)
  apply(subgoal_tac "spf\<cdot>s \<sqsubseteq> spf\<cdot>(s \<Zcat> \<up>a)")
  using approxl3 apply blast
  using cont_pref_eq1I sconc_prefix apply blast
  by (metis inject_sconc)


text\<open>Using @{const diff} a transition can be defined for any \gls{spf} by using the input domain as
the state space. The current state in a run is equivalent to the processed input stream. The next 
output can then be defined by @{const diff} of the spf, the state and the input element.\<close> 
fun spfTransition::"('a stream \<rightarrow> 'b stream) \<Rightarrow> 'a stream \<Rightarrow> 'a \<Rightarrow> ('a stream\<times>'b stream)"where
"spfTransition spf i a = (i\<Zcat>\<up>a,diff spf (i,a))"

fun spfInitConfig::"('a stream \<rightarrow> 'b::{cpo}) \<Rightarrow> 'a stream \<times> 'b" where
"spfInitConfig spf = (\<epsilon>,spf\<cdot>\<epsilon>)"

definition "spfAutomaton spf = (|dautTransition =  spfTransition spf, dautInitConfig = spfInitConfig spf|)"

lemma spfautstatesem_def:"spf\<cdot>s \<Zcat> daStateSem stream_step (spfAutomaton spf) s\<cdot>i = spf\<cdot>(s \<Zcat> i)"
  apply(cases "#(spf\<cdot>s)")
  apply(induction i arbitrary: s)
  apply simp_all
  apply(subst dastatesem_step,simp)
  apply(subst dastatesem_step,simp)
  apply(subst(2) spfAutomaton_def) apply simp
proof-
  fix a::'b and i s::"'b stream" and x1::nat and spf::"'b stream \<rightarrow> 'a stream"
  assume hypo:"(\<And>(x1::nat) (s::'b stream).
           #(spf\<cdot>s) = Fin x1 \<Longrightarrow> spf\<cdot>s \<Zcat> daStateSem stream_step (spfAutomaton spf) s\<cdot>i = spf\<cdot>(s \<Zcat> i))"
  and "#(spf\<cdot>s) = Fin x1"
  have diff_insert:"spf\<cdot>s \<Zcat> diff spf (s, a) = spf\<cdot>(s \<Zcat> \<up>a)"
    using diff2spf by blast
  then have diff_insert_assoc:"\<And>rt. spf\<cdot>s \<Zcat> diff spf (s, a) \<Zcat> rt = spf\<cdot>(s\<Zcat>\<up>a) \<Zcat> rt"
    apply(subst diff_insert[symmetric])
    by (metis assoc_sconc)
  show "spf\<cdot>s \<Zcat> diff spf (s, a) \<Zcat> daStateSem stream_step (spfAutomaton spf) (s \<Zcat> \<up>a)\<cdot>i = spf\<cdot>(s \<Zcat> \<up>a \<Zcat> i)"
    apply (simp add: diff_insert_assoc)
    apply(cases "#(spf\<cdot>(s \<Zcat> \<up>a))")
    apply(simp_all add: hypo)
    by (metis assoc_sconc monofun_spf_ubl)
qed


text\<open>Converting any \gls{spf} using @{const spfTransition} and @{const spfInitConfig} results in a
semantically equivalent automaton.\<close>

theorem spfautsem_def:"daSem stream_step (spfAutomaton spf) = spf"
  apply(rule cfun_eqI)
  apply(simp add: dasem_unfold)
  apply(subst(1) spfAutomaton_def) 
  apply(subst(2) spfAutomaton_def) apply (simp)
  by(subst spfautstatesem_def,simp)



text\<open>Any \gls{sps} can be transformed to an automaton in three steps. First, transform the \gls{sps}
into a set of deterministic automatons using @{const image} and @{const spfAutomaton}. Then, a 
incomplete automaton can be constructed by non-deterministically choosing an deterministic automaton
in the initial configuration and then processing the rest of the output with its transition 
function. Here, this is achieved by expanding the incomplete automatons state-space by the domain of
deterministic automatons.\<close>

definition daSetToNda::"('s::type, 'a::type, 'b::conc) dAutomaton set \<Rightarrow> ('s \<times> ('s::type, 'a::type, 'b::conc) dAutomaton, 'a, 'b) iAutomaton"where
"daSetToNda S = (| iautTransition = (\<lambda>(s,da) i. {apfst (\<lambda>newS. (newS, da)) (dautTransition da s i)}), 
                  iautInitConfig = (\<lambda>da. ((apfst (\<lambda>newS. (newS, da))) (dautInitConfig da))) ` S |)"

lemma "daSem step ` autSet \<subseteq> sem step (gi2gc (daSetToNda autSet))"
  apply auto
proof -
  fix auts
  assume as: "auts \<in> autSet"
  show "daSem step auts \<in> sem step (gi2gc (daSetToNda autSet))"
    apply(rule daseminsem_rule[of _ "(\<lambda>c. (c,auts))" _],simp_all add: case_prod_beta' Let_def)
     apply(simp add: autInitConfig.rep_eq gi2gc.rep_eq spfAutomaton_def daSetToNda_def)
    apply (metis (mono_tags, lifting) as apfst_conv rev_image_eqI surjective_pairing)
    apply(rule dasseminssem_rule,simp add: Let_def)
    apply(simp add: autTransition.rep_eq gi2gc.rep_eq spfAutomaton_def daSetToNda_def)
    by fastforce
qed


lemma h2:assumes"autSet \<noteq> {}"
and" ((a, aut), initOut) \<in> autInitConfig\<cdot>(gi2gc (daSetToNda autSet))"
shows "dautInitConfig aut = (a,initOut)"
and "aut \<in> autSet"
  using assms 
  apply(auto simp add: assms daSetToNda_def autInitConfig.rep_eq gi2gc.rep_eq)
  using apfst_convE by blast+

lemma transitionaut_eq:assumes"((a, aut2), out) \<in> (autTransition\<cdot>(gi2gc (daSetToNda autSet))) (s,aut) i"
and "autSet \<noteq> {}"  
shows "aut2 = aut"
  using assms 
  apply(simp add: assms daSetToNda_def autTransition.rep_eq gi2gc.rep_eq)
  by (metis apfst_conv prod.inject surj_pair)

lemma transition_helper:assumes"autSet \<noteq> {}"
and" ((a, aut), out) \<in> (autTransition\<cdot>(gi2gc (daSetToNda autSet))) (s,aut) i"
shows "dautTransition aut s i = (a,out)"
  using assms 
  apply(simp add: assms daSetToNda_def autTransition.rep_eq gi2gc.rep_eq)
  by (metis apfst_conv prod.inject surj_pair)

lemma ind_h:
  assumes "autSet \<noteq> {}"
shows"spf2\<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (a, aut) \<longrightarrow> spf2\<cdot>s = daStateSem stream_step aut a\<cdot>s"
 proof(induction s arbitrary: a spf2)
    case adm
    then show ?case by auto
  next
    case bottom
    then show ?case 
     apply auto
     apply(subst dastatesem_step,simp)
     by(rule stateSem_bot[of _ stream_step "gi2gc (daSetToNda autSet)" "(a,aut)"];simp)
  next
    case (step x xs)
    then show ?case 
      apply(auto)
      apply(subst dastatesem_step,simp add: case_prod_beta' Let_def)
    proof- 
      assume ih:"(\<And>spf2 a.
        spf2 \<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (a, aut) \<longrightarrow> spf2\<cdot>xs = daStateSem stream_step aut a\<cdot>xs)"
      and spf_well:"spf2 \<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (a, aut)"
      then obtain nout nstate aut2 nspf where aut_def:"spf2\<cdot>(\<up>x \<Zcat> xs) = nout\<Zcat>\<Zcat>nspf\<cdot>xs \<and>
       ((nstate, aut2), nout) \<in> (autTransition\<cdot>(gi2gc (daSetToNda autSet))) (a,aut) x \<and> 
       nspf \<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (nstate, aut2)"
       using assms by (smt old.prod.exhaust stateSem_nextspf_def stream_steps_sbe) 
      then have aut_eq:"aut2= aut"
        using transitionaut_eq
        by (metis assms)
      show "spf2\<cdot>(\<up>x \<Zcat> xs) = snd (dautTransition aut a x)\<Zcat>\<Zcat>daStateSem stream_step aut (fst (dautTransition aut a x))\<cdot>xs"
        apply (simp add: aut_def)
        using aut_def transition_helper spf_well ih assms aut_eq
        by (metis fstI sndI)
    qed
  qed


lemma helper:assumes" spf\<in> sem stream_step (gi2gc (daSetToNda autSet))"
  and "autSet \<noteq> {}"
shows "\<exists>da\<in>autSet. spf = daSem stream_step da"
  using assms
  apply(simp add: sem_def)
proof - 
  assume a1:"\<exists>(initOut) (a) b spfa.
       spf = (\<Lambda> sb. initOut\<Zcat>\<Zcat>spfa\<cdot>sb) \<and>
       ((a, b), initOut) \<in> autInitConfig\<cdot>(gi2gc (daSetToNda autSet)) \<and> spfa \<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (a, b)"
  then obtain initOut a aut spf2 where aut_def:"spf = (\<Lambda> (sb). initOut\<Zcat>\<Zcat>spf2\<cdot>sb) \<and>
       ((a, aut), initOut) \<in> autInitConfig\<cdot>(gi2gc (daSetToNda autSet)) \<and> spf2 \<in> stateSem stream_step (gi2gc (daSetToNda autSet)) (a, aut)" 
    by blast
  have init_def:"(dautInitConfig aut) = (a,initOut)"
    by(rule h2[of autSet];simp add: assms aut_def)
 
  show "\<exists>da\<in>autSet. spf = daSem stream_step da"
    apply(rule bexI[of _ aut])
    apply(rule cfun_eqI)
    apply(simp add: init_def daSem_def case_prod_unfold aut_def Let_def)
    apply (metis assms(2) aut_def ind_h)
    by (meson h2(2) assms(2) aut_def)
qed

lemma sem_subset:"autSet \<noteq> {} \<Longrightarrow> 
sem stream_step (gi2gc (daSetToNda autSet)) \<subseteq> (daSem stream_step ` autSet)"
  using helper by auto

definition "spsAutomaton = gi2gc o daSetToNda o (image spfAutomaton)"


theorem spssubspsautsem:"SPS \<subseteq> sem stream_step (spsAutomaton SPS)"
  apply auto
  apply(subgoal_tac "daSem stream_step (spfAutomaton x) \<in> sem stream_step ((spsAutomaton SPS))")
   apply (simp add: spfautsem_def)
proof -
  fix spf
  assume as: "spf \<in> SPS"
  show "daSem stream_step (spfAutomaton spf) \<in> sem stream_step (spsAutomaton SPS)"
    apply(rule daseminsem_rule[of _ "(\<lambda>c. (c,(spfAutomaton spf)))" _],simp_all add: case_prod_beta' Let_def)
     apply(simp add: autInitConfig.rep_eq gi2gc.rep_eq daSetToNda_def spfAutomaton_def spsAutomaton_def image_iff)
    using as apply blast
  apply(rule dasseminssem_rule,simp add: Let_def)
  by(simp add: autTransition.rep_eq gi2gc.rep_eq spfAutomaton_def spsAutomaton_def Let_def daSetToNda_def)
qed

lemma spsautsem_subcomplete: assumes "SPS \<noteq> {}" shows "sem stream_step (spsAutomaton SPS) \<subseteq> SPS"
  apply(simp add: spsAutomaton_def)
  apply auto
  by (smt assms helper imageE image_is_empty spfautsem_def)

theorem spsautsem_def:
  assumes "SPS \<noteq> {}"  
    shows "eSem (spsAutomaton SPS) = SPS"
  by (metis eSem_def assms spsautsem_subcomplete spssubspsautsem subset_antisym)

end