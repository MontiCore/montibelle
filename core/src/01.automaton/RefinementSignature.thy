theory RefinementSignature
imports Automaton DeterministicAutomaton Nda2DaSet

begin




lemma sem_change_inouttypes:
  fixes inconv::"'in2::cpo \<rightarrow> 'in1::cpo"
  and outconv::"'out1::{conc,pcpo} \<rightarrow> 'out2::{conc,pcpo}"
  and msgconv::"'msg2 \<Rightarrow> 'msg1"
  and step1::"('msg1 \<Rightarrow> 'in1 \<rightarrow> 'out1) \<rightarrow> 'in1 \<rightarrow> 'out1"
  and step2::"('msg2 \<Rightarrow> 'in2 \<rightarrow> 'out2) \<rightarrow> 'in2 \<rightarrow> 'out2"
  and aut1::"('s, 'msg1, 'out1) automaton"
  and aut2::"('s, 'msg2, 'out2) automaton"
assumes "\<And>f. outconv oo (step1\<cdot>f) oo inconv = step2\<cdot>(\<lambda>m . outconv oo f (msgconv m) oo inconv)"
  and "\<And>s1 s2 m out. (s2,out) \<in> (autTransition\<cdot>aut1) s1 (msgconv m) \<Longrightarrow> (s2, outconv\<cdot>out) \<in> (autTransition\<cdot>aut2) s1 m"
  and "\<And>a b s m. a \<in> snd ` (autTransition\<cdot>aut1) s m \<Longrightarrow> outconv\<cdot>(a \<Zcat>\<Zcat> b) = outconv\<cdot>a \<Zcat>\<Zcat> outconv\<cdot>b"
shows "(\<lambda>sem s::'s. (\<lambda>spf. outconv oo spf oo inconv) ` sem s) (stateSem step1 aut1) \<le> stateSem step2 aut2"
  apply(auto simp add: stateSem_def)[1]
  apply(rule gfp_upperbound)
  apply(rule le_funI,auto)
  unfolding stateSem_def[symmetric]
proof-
  fix x::'s and xb::"'in1 \<rightarrow> 'out1"
  assume a1:"xb \<in> stateSem step1 aut1 x"
  then obtain f where f_def:"\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>aut1) x msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step1 aut1) nextState 
        \<and>  (\<forall>sb. f msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and "xb = step1\<cdot>f"
    using stateSemf_def[of xb step1 aut1 x] by blast
  then show " outconv oo xb oo inconv
       \<in> stateSem_step step2 aut2 (\<lambda>s::'s. (\<lambda>x::'in1 \<rightarrow> 'out1. outconv oo x oo inconv) ` stateSem step1 aut1 s) x"
    apply(auto)
    apply(simp add: assms(1))
    apply(auto simp only: stateSem_step_def)[1]
    apply(rule imageI)
    proof auto
      fix msg::'msg2
      assume a2:"\<forall>msg::'msg1.
            \<exists>(output::'out1) nextState::'s.
               (nextState, output) \<in> (autTransition\<cdot>aut1) x msg \<and>
               (\<exists>nextSPF::'in1 \<rightarrow> 'out1. nextSPF \<in> stateSem step1 aut1 nextState \<and> (\<forall>sb::'in1. f msg\<cdot>sb = output\<Zcat>\<Zcat>nextSPF\<cdot>sb))"
      then obtain out ns where out_def:"(ns, out) \<in> (autTransition\<cdot>aut1) x (msgconv msg) \<and>
               (\<exists>nextSPF::'in1 \<rightarrow> 'out1. nextSPF \<in> stateSem step1 aut1 ns \<and> 
               (\<forall>sb::'in1. f (msgconv msg)\<cdot>sb = out\<Zcat>\<Zcat>nextSPF\<cdot>sb))"
        by blast
      then show "\<exists>(output::'out2) nextState::'s.
            (nextState, output) \<in> (autTransition\<cdot>aut2) x msg \<and>
            (\<exists>nextSPF::'in1 \<rightarrow> 'out1\<in>stateSem step1 aut1 nextState.
                \<forall>input::'in2. outconv\<cdot>(f (msgconv msg)\<cdot>(inconv\<cdot>input)) = output\<Zcat>\<Zcat>outconv\<cdot>(nextSPF\<cdot>(inconv\<cdot>input)))"
        apply(rule_tac x="outconv\<cdot>out" in exI)
        apply(rule_tac x="ns" in exI)
        apply(auto simp add: assms)[1]
        apply(subst assms(3)[where s="x" and m="msgconv msg"],auto)
        by (simp add: rev_image_eqI)
    qed
qed

lemma sem_change_inouttypes2:
  fixes inconv::"'in2::cpo \<rightarrow> 'in1::cpo"
  and "inInv"::"'in1 \<rightarrow> 'in2"
  and outconv::"'out1::{conc,pcpo} \<rightarrow> 'out2::{conc,pcpo}"
  and outInv::"'out2 \<rightarrow> 'out1"
  and msgconv::"'msg2 \<Rightarrow> 'msg1"
  and msgInv::"'msg1 \<Rightarrow> 'msg2"
  and step1::"('msg1 \<Rightarrow> 'in1 \<rightarrow> 'out1) \<rightarrow> 'in1 \<rightarrow> 'out1"
  and step2::"('msg2 \<Rightarrow> 'in2 \<rightarrow> 'out2) \<rightarrow> 'in2 \<rightarrow> 'out2"
  and aut1::"('s, 'msg1, 'out1) automaton"
  and aut2::"('s, 'msg2, 'out2) automaton"
assumes "\<And>f. step2\<cdot>(\<lambda>m . outconv oo f(msgconv m) oo inconv) = outconv oo (step1\<cdot>f) oo inconv"
  and "\<And>s1 s2 m out. (s2,out) \<in> (autTransition\<cdot>aut1) s1 (msgconv m) \<Longrightarrow> (s2, outconv\<cdot>out) \<in> (autTransition\<cdot>aut2) s1 m"
  and "\<And>a b s m. a \<in> snd ` (autTransition\<cdot>aut1) s m \<Longrightarrow> outconv\<cdot>(a \<Zcat>\<Zcat> b) = outconv\<cdot>a \<Zcat>\<Zcat> outconv\<cdot>b"
  and "\<forall>x. outconv\<cdot>(outInv\<cdot>x) = x"
  and "\<forall>x. outconv\<cdot>(outInv\<cdot>x) = x"
  and "\<forall>x. outconv\<cdot>(outInv\<cdot>x) = x"
  and "\<forall>x. inInv\<cdot>(inconv\<cdot>x) = x"
  and "\<forall>x. msgInv(msgconv x) = x"
shows "(stateSem step2 aut2) \<le> (\<lambda>sem s::'s. (\<lambda>spf. outconv oo spf oo inconv) ` sem s) (stateSem step1 aut1)"
(*  apply(auto simp add: stateSem_def)[1]
  apply(rule gfp_least)
  apply(rule le_funI,auto)
  unfolding stateSem_def[symmetric]
proof -
  fix u and xb and xa
  assume asm1: "u \<le> stateSem_step step2 aut2 u"
  and asm2: "xa \<in> u xb"

  have "u \<le> stateSem step2 aut2"
    using asm1
    unfolding stateSem_def
    by (rule gfp_upperbound)
  hence "xa \<in> stateSem step2 aut2 xb"
    using asm2 le_funD by fastforce
  then obtain g where g_def:"\<forall>msg. \<exists>output nextState. 
       (nextState,output) \<in> (autTransition\<cdot>aut2) xb msg
        \<and>  (\<exists> nextSPF. nextSPF \<in> (stateSem step2 aut2) nextState 
        \<and>  (\<forall>sb. g msg\<cdot>sb = output \<Zcat>\<Zcat> nextSPF\<cdot>sb))" 
      and xa_def: "xa = step2\<cdot>g"
    using stateSemf_def[of xa step2 aut2 xb]
    by blast

  obtain f where f_constr: "f = (\<lambda>n. outInv oo (g (msgInv n)) oo inInv)"
    by blast
  hence f_def: "g = (\<lambda>m. outconv oo (f (msgconv m)) oo inconv)"
    apply auto
    unfolding oo_def apply auto
    using assms by auto

  then have step1FInStateSem: "step1\<cdot>f \<in> stateSem step1 aut1 xb"
    using f_constr assms
    (*apply(simp add: assms(1))
    apply(auto simp only: stateSem_step_def)[1]
    apply(rule imageI)*)
    sorry
  
  show "xa \<in> (\<lambda>x. outconv oo x oo inconv) ` stateSem step1 aut1 xb"
    apply (subst xa_def)
    unfolding image_def apply auto
    unfolding f_def
    apply (subst assms(1)[of f])
    apply (rule_tac x="(step1\<cdot>f)" in bexI)
    apply auto
    using step1FInStateSem by simp
oops*)
oops


lemma sem_change_inouttypes_spf:
  fixes inconv::"'in2::cpo \<rightarrow> 'in1::cpo"
  and outconv::"'out1::{conc,pcpo} \<rightarrow> 'out2::{conc,pcpo}"
  and msgconv::"'msg2 \<Rightarrow> 'msg1"
  and step1::"('msg1 \<Rightarrow> 'in1 \<rightarrow> 'out1) \<rightarrow> 'in1 \<rightarrow> 'out1"
  and step2::"('msg2 \<Rightarrow> 'in2 \<rightarrow> 'out2) \<rightarrow> 'in2 \<rightarrow> 'out2"
  and aut1::"('s, 'msg1, 'out1) automaton"
  and aut2::"('s, 'msg2, 'out2) automaton"
assumes "\<And>f. outconv oo (step1\<cdot>f) oo inconv = step2\<cdot>(\<lambda>m . outconv oo f (msgconv m) oo inconv)"
  and "\<And>s1 s2 m out. (s2,out) \<in> (autTransition\<cdot>aut1) s1 (msgconv m) \<Longrightarrow> (s2, outconv\<cdot>out) \<in> (autTransition\<cdot>aut2) s1 m"
  and "\<And>a b s m. a \<in> snd ` (autTransition\<cdot>aut1) s m \<Longrightarrow> outconv\<cdot>(a \<Zcat>\<Zcat> b) = outconv\<cdot>a \<Zcat>\<Zcat> outconv\<cdot>b"
  and "spf \<in> stateSem step1 aut1 s"
shows "outconv oo spf oo inconv \<in> stateSem step2 aut2 s"
  using sem_change_inouttypes[of outconv step1 inconv step2 msgconv aut1 aut2] assms
  apply auto[1]
  by (meson image_iff in_mono le_fun_def)

lemma sem_inoutref:
  fixes inconv::"'in2::cpo \<rightarrow> 'in1::cpo"
    and outconv::"'out1::{conc,pcpo} \<rightarrow> 'out2::{conc,pcpo}"
    and msgconv::"'msg2 \<Rightarrow> 'msg1"
    and step1::"('msg1 \<Rightarrow> 'in1 \<rightarrow> 'out1) \<rightarrow> 'in1 \<rightarrow> 'out1"
    and step2::"('msg2 \<Rightarrow> 'in2 \<rightarrow> 'out2) \<rightarrow> 'in2 \<rightarrow> 'out2"
    and aut1::"('s, 'msg1, 'out1) automaton"
    and aut2::"('s, 'msg2, 'out2) automaton"
  assumes "\<And>f. outconv oo (step1\<cdot>f) oo inconv = step2\<cdot>(\<lambda>m . outconv oo f (msgconv m) oo inconv)"
    and "\<And>s1 s2 m out. (s2,out) \<in> (autTransition\<cdot>aut1) s1 (msgconv m) \<Longrightarrow> (s2, outconv\<cdot>out) \<in> (autTransition\<cdot>aut2) s1 m"
    and "\<And>out1 b s m. out1 \<in> snd ` (autTransition\<cdot>aut1) s m \<Longrightarrow> outconv\<cdot>(out1 \<Zcat>\<Zcat> b) = outconv\<cdot>out1 \<Zcat>\<Zcat> outconv\<cdot>b"
  shows "(\<lambda>spf1. outconv oo spf1 oo inconv)` (stateSem step1 aut1 s) \<subseteq> stateSem step2 aut2 s"
  apply auto[1]
  apply(rule sem_change_inouttypes_spf)
  apply(simp_all add: assms)
  by (simp add: assms(2))

lemma statesem_inoutref:
  fixes inconv::"'in2::cpo \<rightarrow> 'in1::cpo"
    and outconv::"'out1::{conc,pcpo} \<rightarrow> 'out2::{conc,pcpo}"
    and msgconv::"'msg2 \<Rightarrow> 'msg1"
    and step1::"('msg1 \<Rightarrow> 'in1 \<rightarrow> 'out1) \<rightarrow> 'in1 \<rightarrow> 'out1"
    and step2::"('msg2 \<Rightarrow> 'in2 \<rightarrow> 'out2) \<rightarrow> 'in2 \<rightarrow> 'out2"
    and aut1::"('s, 'msg1, 'out1) automaton"
    and aut2::"('s, 'msg2, 'out2) automaton"
  assumes "\<And>f. outconv oo (step1\<cdot>f) oo inconv 
              = step2\<cdot>(\<lambda>m . outconv oo f (msgconv m) oo inconv)"
    and "\<And>s sN m out. (sN,out) \<in> (autTransition\<cdot>aut1) s (msgconv m) 
            \<Longrightarrow> (sN, outconv\<cdot>out) \<in> (autTransition\<cdot>aut2) s m"
    and "\<And>out1 b s m. out1 \<in> snd ` (autTransition\<cdot>aut1) s m 
            \<Longrightarrow> outconv\<cdot>(out1 \<Zcat>\<Zcat> b) = outconv\<cdot>out1 \<Zcat>\<Zcat> outconv\<cdot>b"
  shows "{inconv} \<then> (stateSem step1 aut1 s) \<then> {outconv} 
                   \<subseteq> stateSem step2 aut2 s"
  unfolding seqcomp_image_sps 
  using sem_inoutref[OF assms]
  .


lemma statesem_in_ref:
  fixes inconv::"'inOrig::cpo \<rightarrow> 'inRef::cpo"
    and msgconv::"'msgOrig \<Rightarrow> 'msgRef"
    and stepRef::"('msgRef \<Rightarrow> 'inRef \<rightarrow> 'out) \<rightarrow> 'inRef \<rightarrow> 'out::{conc,pcpo}"
    and stepOrig::"('msgOrig \<Rightarrow> 'inOrig \<rightarrow> 'out) \<rightarrow> 'inOrig \<rightarrow> 'out"
    and autRef::"('s, 'msgRef, 'out) automaton"
    and autOrig::"('s, 'msgOrig, 'out) automaton"
  assumes "\<And>f. (stepRef\<cdot>f) oo inconv 
              = stepOrig\<cdot>(\<lambda>m . f (msgconv m) oo inconv)"
    and "\<And>s sN m out. (autTransition\<cdot>autRef) s (msgconv m) \<subseteq> (autTransition\<cdot>autOrig) s m"
  shows "{inconv} \<then> (stateSem stepRef autRef s) 
                   \<subseteq> stateSem stepOrig autOrig s"
  apply(subst(3) seqcomp_ID2[symmetric])
  unfolding seqcomp_assoc
  apply(rule statesem_inoutref[where msgconv=msgconv])
  using assms by fastforce+

lemma sem_def2: "sem step aut = \<Union>((\<lambda> (initState, initOut). (stateSem step aut initState) \<then> {(conc initOut)}) 
  ` autInitConfig\<cdot>aut)"
  by(auto simp add: sem_def seqcomp_image2 oo_def)

lemma seqcomp_union_left: "A \<then> (\<Union>b\<in>B. P b) = (\<Union>b\<in>B. (A \<then> P b))"
  by (auto simp add: seqcomp_insert) 
lemma seqcomp_union_right: "(\<Union>b\<in>B. P b)\<then>A = (\<Union>b\<in>B. (P b \<then> A))"
  by (auto simp add: seqcomp_insert) 

lemma sem_in_ref:
  fixes inconv::"'inOrig::cpo \<rightarrow> 'inRef::cpo"
    and msgconv::"'msgOrig \<Rightarrow> 'msgRef"
    and stepRef::"('msgRef \<Rightarrow> 'inRef \<rightarrow> 'out) \<rightarrow> 'inRef \<rightarrow> 'out::{conc,pcpo}"
    and stepOrig::"('msgOrig \<Rightarrow> 'inOrig \<rightarrow> 'out) \<rightarrow> 'inOrig \<rightarrow> 'out"
    and autRef::"('s, 'msgRef, 'out) automaton"
    and autOrig::"('s, 'msgOrig, 'out) automaton"
  assumes A1: "\<And>f. (stepRef\<cdot>f) oo inconv 
              = stepOrig\<cdot>(\<lambda>m . f (msgconv m) oo inconv)"
    and A2:"\<And>s m out. (autTransition\<cdot>autRef) s (msgconv m) 
                    \<subseteq> (autTransition\<cdot>autOrig) s m"
    and A3: "autInitConfig\<cdot>autRef \<subseteq> autInitConfig\<cdot>autOrig"
  shows "{inconv} \<then> (sem stepRef autRef) 
                   \<subseteq> sem stepOrig autOrig"
  unfolding sem_def2
  apply(subst seqcomp_union_left)+
  apply auto
proof -
  fix x a b
  assume H1: "(a, b) \<in> autInitConfig\<cdot>autRef"
  assume H2: "x \<in> {inconv} \<then> stateSem stepRef autRef a \<then> {conc b}"
  from A3 and H1 have "(a, b) \<in> autInitConfig\<cdot>autOrig" by auto
  moreover have "x \<in> stateSem stepOrig autOrig a \<then> {conc b}"
    using H2 statesem_in_ref[OF A1 A2] seqcomp_assoc seqcomp_subset
    by blast
    
  ultimately show
    "\<exists>xa\<in>autInitConfig\<cdot>autOrig.
       x \<in> (case xa of (initState, initOut) \<Rightarrow>
              stateSem stepOrig autOrig initState \<then> {conc initOut})"
    by auto
qed


lemma "inconv o inconv_inverse = id \<Longrightarrow> surj inconv"
  apply(rule surjI[where f=inconv_inverse])
  apply(auto simp add: o_def id_def)
  by meson

lemma statesem_in_inv_ref:
  fixes inconv::"'inOrig::cpo \<rightarrow> 'inRef::cpo"
    and inconv_inverse::"'inRef \<rightarrow> 'inOrig"
    and msgconv::"'msgOrig \<Rightarrow> 'msgRef"
    and stepRef::"('msgRef \<Rightarrow> 'inRef \<rightarrow> 'out) \<rightarrow> 'inRef \<rightarrow> 'out::{conc,pcpo}"
    and stepOrig::"('msgOrig \<Rightarrow> 'inOrig \<rightarrow> 'out) \<rightarrow> 'inOrig \<rightarrow> 'out"
    and autRef::"('s, 'msgRef, 'out) automaton"
    and autOrig::"('s, 'msgOrig, 'out) automaton"
  assumes "\<And>f. (stepRef\<cdot>f) oo inconv 
              = stepOrig\<cdot>(\<lambda>m . f (msgconv m) oo inconv)"
    and "\<And>s m. (autTransition\<cdot>autRef) s (msgconv m) \<subseteq> (autTransition\<cdot>autOrig) s m"
    and "inconv oo inconv_inverse = ID"
  shows "stateSem stepRef autRef s 
           \<subseteq> {inconv_inverse} \<then> stateSem stepOrig autOrig s"
proof - 
  have hRef: "{inconv} \<then> (stateSem stepRef autRef s) \<subseteq> stateSem stepOrig autOrig s"
    using statesem_in_ref[OF assms(1-2), where s=s] .
  hence "{inconv_inverse} \<then> {inconv} \<then> (stateSem stepRef autRef s)
      \<subseteq> {inconv_inverse} \<then> stateSem stepOrig autOrig s"
    by(auto simp add: seqcomp_insert)
  moreover have "\<And> A. {inconv_inverse} \<then> {inconv} \<then> A = A"
    apply(auto simp add: seqcomp_insert assms(3) oo_assoc)
    by (metis ID2 assms(3) assoc_oo)
  ultimately show ?thesis       
    by blast
qed

lemma sem_in_inv_ref:
  fixes inconv::"'inOrig::cpo \<rightarrow> 'inRef::cpo"
    and inconv_inverse::"'inRef \<rightarrow> 'inOrig"
    and msgconv::"'msgOrig \<Rightarrow> 'msgRef"
    and stepRef::"('msgRef \<Rightarrow> 'inRef \<rightarrow> 'out) \<rightarrow> 'inRef \<rightarrow> 'out::{conc,pcpo}"
    and stepOrig::"('msgOrig \<Rightarrow> 'inOrig \<rightarrow> 'out) \<rightarrow> 'inOrig \<rightarrow> 'out"
    and autRef::"('s, 'msgRef, 'out) automaton"
    and autOrig::"('s, 'msgOrig, 'out) automaton"
  assumes A1: "\<And>f. (stepRef\<cdot>f) oo inconv 
              = stepOrig\<cdot>(\<lambda>m . f (msgconv m) oo inconv)"
    and A2: "\<And>s m. (autTransition\<cdot>autRef) s (msgconv m) \<subseteq> (autTransition\<cdot>autOrig) s m"
    and A3: "autInitConfig\<cdot>autRef \<subseteq> autInitConfig\<cdot>autOrig"
    and A4: "inconv oo inconv_inverse = ID"
  shows "sem stepRef autRef 
           \<subseteq> {inconv_inverse} \<then> sem stepOrig autOrig"
  unfolding sem_def2
  apply(subst seqcomp_union_left)+
  apply auto
  proof -
  fix x a b
  assume H1: "(a, b) \<in> autInitConfig\<cdot>autRef"
  assume H2: "x \<in> stateSem stepRef autRef a \<then> {conc b}"
  from A3 and H1 have "(a, b) \<in> autInitConfig\<cdot>autOrig" by auto
  moreover
  have "x \<in> {inconv_inverse} \<then> (stateSem stepOrig autOrig a \<then> {conc b})"
  proof -
    have "stateSem stepRef autRef a
          \<subseteq> {inconv_inverse} \<then> stateSem stepOrig autOrig a"
      using statesem_in_inv_ref[OF A1 A2 A4] by blast
    hence "stateSem stepRef autRef a \<then> {conc b}
           \<subseteq> {inconv_inverse} \<then> (stateSem stepOrig autOrig a \<then> {conc b})"
      using seqcomp_assoc seqcomp_subset by blast
    with H2 show ?thesis by auto
  qed
  ultimately show
    "\<exists>xa\<in>autInitConfig\<cdot>autOrig.
       x \<in> {inconv_inverse} \<then>
             (case xa of (initState, initOut) \<Rightarrow>
                stateSem stepOrig autOrig initState \<then> {conc initOut})"
    by force
qed

lemma statesem_step_input_convert:
      fixes nda1::"('state::type,'msg1::type,'out::{conc, pcpo}) automaton"
        and nda2::"('state::type,'msg2::type,'out::{conc, pcpo}) automaton"  
  assumes "\<forall>s. (\<lambda>f. f oo rep) ` y s \<subseteq> x s"
    and step2rep:"\<And>f. step2\<cdot>f oo rep = step1\<cdot>(\<lambda>msg. \<Lambda> input. f (rep_msg msg)\<cdot>(rep\<cdot>input))"
    and "\<And>state msg. (autTransition\<cdot>nda2) state (rep_msg msg) \<subseteq> (autTransition\<cdot>nda1) state msg"
  shows "(\<lambda>f. f oo rep) ` stateSem_step step2 nda2 y s \<subseteq> stateSem_step step1 nda1 x s"
  apply(simp add: stateSem_step_def image_iff image_def)
  apply auto[1]
  apply(rename_tac f)
  apply(rule_tac x="(\<lambda>msg. \<Lambda> input. f (rep_msg msg)\<cdot>(rep\<cdot>input))" in exI)
  apply (auto simp add: step2rep)[1]
proof -
  fix f msg1
  assume as: "\<forall>msg2::'msg2.
          \<exists>(output::'out) nextState::'state.
             (nextState, output) \<in> (autTransition\<cdot>nda2) s msg2 \<and>
             (\<exists>nextSPF::'b \<rightarrow> 'out.
                 nextSPF \<in> y nextState \<and>
                 (\<forall>input::'b. f msg2\<cdot>input = output\<Zcat>\<Zcat>nextSPF\<cdot>input))"
  obtain out nextState nextSPF where trans:"(nextState, out) \<in> (autTransition\<cdot>nda2) s (rep_msg msg1)"
                and spf_in: "nextSPF \<in> y nextState"
                and step:"(\<forall>input::'b. f (rep_msg msg1)\<cdot>input = out\<Zcat>\<Zcat>nextSPF\<cdot>input)"
    using as by blast
  show "\<exists>(output::'out) nextState::'state.
          (nextState, output) \<in> (autTransition\<cdot>nda1) s msg1 \<and>
          (\<exists>nextSPF::'a \<rightarrow> 'out.
              nextSPF \<in> x nextState \<and>
              (\<forall>input::'a. f (rep_msg msg1)\<cdot>(rep\<cdot>input) = output\<Zcat>\<Zcat>nextSPF\<cdot>input))"
    apply(rule_tac x="out" in exI, rule_tac x="nextState" in exI)
    apply auto[1]
    using assms(3) local.trans apply auto[1]
    apply(rule_tac x="nextSPF oo rep" in exI, auto)
    using assms(1) spf_in apply auto[1]
    using local.step by auto
qed

theorem statesem_input_convert:
  assumes
    step2rep:"\<And>f. step2\<cdot>f oo rep = step1\<cdot>(\<lambda>msg. \<Lambda> input. f (rep_msg msg)\<cdot>(rep\<cdot>input))"
    and "\<And>state msg. (autTransition\<cdot>nda2) state (rep_msg msg) \<subseteq> (autTransition\<cdot>nda1) state msg"
    shows "\<forall>s. (\<lambda>f .f oo rep) ` stateSem step2 nda2 s \<le> stateSem step1 nda1 s"
  unfolding stateSem_def
  apply(rule gfp_parallel_induct [of "(stateSem_step step1 nda1)" "stateSem_step step2 nda2"])
     apply simp+
   apply(rule allI)
   apply(rule statesem_step_input_convert; (simp add: assms)?)
  apply (simp add: assms(2); fail)
   apply auto[1]
  by fastforce




lift_definition changeOutAut::"('outOld \<rightarrow> 'outNew) \<Rightarrow> ('state::type, 'message::type, 'outOld::conc) automaton
  \<Rightarrow> ('state::type, 'message::type, 'outNew::conc) automaton" is
"\<lambda> outmod aut. (\<lambda>state msg. apsnd (Rep_cfun outmod) ` ((autTransition\<cdot>aut) state msg), 
              apsnd (Rep_cfun outmod) ` (autInitConfig\<cdot>aut))"
  by simp

theorem changeoutaut_statesem: 
  assumes "\<And>f. outmod oo step'\<cdot>f = step\<cdot>(\<lambda>m. outmod oo f m)"
      and "\<And>a b. outmod\<cdot>(a\<Zcat>\<Zcat>b) = outmod\<cdot>a\<Zcat>\<Zcat>outmod\<cdot>b"
  shows "(\<lambda>spf. outmod oo spf) `stateSem step' aut s 
                            \<subseteq> stateSem step (changeOutAut outmod aut) s"
  apply(subst(5) ID2[symmetric])
   apply(rule sem_inoutref [where msgconv=id]; simp add: assms)
    apply(simp add: autTransition.rep_eq changeOutAut.rep_eq)
    apply force
  done


theorem statesem_refine_rule_outmodify:
    assumes "\<And>state msg nextState out. Inv state 
                \<Longrightarrow> (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
                \<Longrightarrow> (f nextState, outmod\<cdot>out) \<in> (autTransition\<cdot>aut) (f state) msg"
        and invariant: "\<And>state msg nextState. Inv state
                   \<Longrightarrow> nextState \<in> fst ` (autTransition\<cdot>aut') state msg
                   \<Longrightarrow> Inv nextState"
        and init_invariant: "\<And>state. state \<in> fst ` (autInitConfig\<cdot>aut') \<Longrightarrow> Inv state"
        and "Inv s"
        
        and "\<And>f. outmod oo step'\<cdot>f = step\<cdot>(\<lambda>m. outmod oo f m)"
        and "\<And>a b. outmod\<cdot>(a\<Zcat>\<Zcat>b) = (outmod\<cdot>a)\<Zcat>\<Zcat>(outmod\<cdot>b)"

      shows "(\<lambda>spf. outmod oo spf) ` stateSem step' aut' s 
                                   \<subseteq> stateSem step aut (f s)"
proof -                                           
  have "(\<lambda>spf. outmod oo spf) `stateSem step' aut' s 
                            \<subseteq> stateSem step (changeOutAut outmod aut') s"
    by(rule changeoutaut_statesem; simp add: assms)
  moreover have "stateSem step (changeOutAut outmod aut') s \<subseteq> stateSem step aut (f s)"
    apply(rule statesem_refine_rule [where Inv=Inv]; (simp add: assms)?)
    apply(simp_all add: autTransition.rep_eq changeOutAut.rep_eq)
    apply(simp add:  autTransition.rep_eq image_iff)
    apply (metis assms(1) autTransition.rep_eq fst_apsnd fst_eqD prod.collapse snd_apsnd snd_conv)
       by (simp add: autTransition.rep_eq image_iff invariant)
  ultimately show ?thesis
    by blast
qed


theorem sem_refine_rule_outmodify:
  assumes "\<And>s. s \<in>fst`(autInitConfig\<cdot>aut') \<Longrightarrow> (\<lambda>spf. outmod oo spf) ` stateSem step' aut' s 
                                   \<subseteq> stateSem step aut (f s)"     
    and "\<And>s out. (s,out) \<in> (autInitConfig\<cdot>aut') \<Longrightarrow> 
            (f s, outmod\<cdot>out) \<in> (autInitConfig\<cdot>aut)"
        and "\<And>a b. outmod\<cdot>(a\<Zcat>\<Zcat>b) = (outmod\<cdot>a)\<Zcat>\<Zcat>(outmod\<cdot>b)"

    shows "(\<lambda>spf. outmod oo spf) ` sem step' aut'
              \<subseteq> sem step aut "
   apply(auto simp add: sem_def)[1]
   apply(rule_tac x="outmod\<cdot>initOut" in exI)
   apply(rule_tac x="f initState" in exI)
  apply(rule_tac x="outmod oo spf" in exI)
  apply auto[1]
    apply(rule cfun_eqI)
  using assms by fastforce+

theorem sem_refine_add_output:
 assumes "\<And>state msg nextState out.  
                (  nextState, out) \<in> (autTransition\<cdot>aut') state msg
            \<Longrightarrow> (nextState, outmod\<cdot>out) \<in> (autTransition\<cdot>aut) (state) msg"
   and   "\<And>s out. (s,out) \<in> (autInitConfig\<cdot>aut') \<Longrightarrow> 
            (s, outmod\<cdot>out) \<in> (autInitConfig\<cdot>aut)"
        and "\<And>a b. outmod\<cdot>(a\<Zcat>\<Zcat>b) = (outmod\<cdot>a)\<Zcat>\<Zcat>(outmod\<cdot>b)"
        and "\<And>f. outmod oo step'\<cdot>f = step\<cdot>(\<lambda>m. outmod oo f m)"
    shows "(sem step' aut') \<then> {outmod} \<subseteq> sem step aut"
  apply (subst seqcomp_image2)
  apply(rule sem_refine_rule_outmodify[where f=id])
    apply(rule statesem_refine_rule_outmodify[where Inv="\<lambda>_. True"])
  by(simp add: assms)+



lift_definition changeInAut::"('messageBigger \<Rightarrow> 'messageSmaller) 
  \<Rightarrow> ('state::type, 'messageSmaller::type, 'out::conc) automaton
  \<Rightarrow> ('state::type, 'messageBigger::type, 'out::conc) automaton" is
"\<lambda> msgconv aut. (\<lambda>state msg. ((autTransition\<cdot>aut) state (msgconv msg)), 
              (autInitConfig\<cdot>aut))"
  by simp

lemma changein_aut: 
  fixes msgconv::"('messageBigger \<Rightarrow> 'messageSmaller)"
      and aut::"('state::type, 'messageSmaller::type, 'out::conc) automaton"
  shows "{inconv} \<then> stateSem step' aut s
                            \<subseteq> stateSem step (changeInAut msgconv aut) s"
  oops

theorem 
  fixes inconv::"'inRef::cpo \<rightarrow> 'inOrig::cpo"
    and msgconv::"'msgRef \<Rightarrow> 'msgOrig"
    and stepRef::"('msgRef \<Rightarrow> 'inRef \<rightarrow> 'out) \<rightarrow> 'inRef \<rightarrow> 'out::{conc,pcpo}"
    and stepOrig::"('msgOrig \<Rightarrow> 'inOrig \<rightarrow> 'out) \<rightarrow> 'inOrig \<rightarrow> 'out"
    and autRef::"('s, 'msgRef, 'out) automaton"
    and autOrig::"('s, 'msgOrig, 'out) automaton"
  assumes "\<And>f. stepRef\<cdot>(\<lambda>m . f (msgconv m) oo inconv) 
              = stepOrig\<cdot>f oo inconv"
    and "\<And>s m. (autTransition\<cdot>autRef) s m \<subseteq> (autTransition\<cdot>autOrig) s (msgconv m)"
  shows "stateSem stepRef autRef s 
       \<subseteq> spsComplete({inconv} \<then> stateSem stepOrig autOrig s)"
proof(rule spscomplete_belowI)
  fix spfRef::"'inRef \<rightarrow> 'out" and input::"'inRef"
  assume "spfRef \<in> stateSem stepRef autRef s"
  obtain daRef where "daRef \<in> nda2daset autRef" oops

end