theory StreamNondet
  imports stream.StreamScanl
begin

default_sort countable




subsection\<open>Non-deterministic @{const smap}\<close>
lemma monondetsmap[simp]:"mono (\<lambda>H. {f | f.  (f\<cdot>\<epsilon>=\<epsilon>) \<and> (\<forall>m s. \<exists>x g. 
                           (f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s) \<and> x\<in>(T m) \<and> g\<in>H)})"
  apply(rule monoI)
  apply(simp add: prod.case_eq_if,auto)
  by (meson subset_iff)


text\<open>The Non-deterministic @{const smap} function works similar to 
@{const smap} but over a set of possible outputs for every input 
element of the input stream. The set of possible outputs is defined
by the input function with the signature \<open>'a \<Rightarrow> 'b set\<close>. The 
non-deterministic smap returns a set of all possible functions, that
map the input according to the input function.\<close>

definition ndetsmap::"('a::countable \<Rightarrow> 'b::countable set) 
                    \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"ndetsmap T = gfp (\<lambda>H. {f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> (\<forall>m s. \<exists>x g.  
                           (f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s) \<and> x\<in>(T m) \<and> g\<in>H)})"

lemma ndsmap_unfold:"ndetsmap S = {f |f . f\<cdot>\<epsilon> = \<epsilon> \<and>
     (\<forall>m s. \<exists>x g. f\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat> g\<cdot>s \<and> 
                x \<in> S m \<and> g\<in> (ndetsmap S))}"
  unfolding ndetsmap_def
  apply(subst gfp_unfold)
  using monondetsmap by auto

lemma ndsmap_strict[simp]:"spf \<in> ndetsmap S \<Longrightarrow> spf\<cdot>\<epsilon>=\<epsilon>"
  using ndsmap_unfold[of S] by auto

lemma ndsmap_step: assumes "spf1 \<in> ndetsmap T"
  shows "\<exists>spf2\<in>(ndetsmap T). \<exists>out\<in>(T m). spf1\<cdot>(\<up>m\<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s"
  apply (insert assms)
  using ndsmap_unfold[of T] apply auto
  by fastforce

lemma ndsmap_message: assumes "spf1 \<in> ndetsmap T"
  shows "\<exists>out\<in>(T m). spf1\<cdot>(\<up>m) = \<up>out"
  apply (insert assms)
  using ndsmap_step ndsmap_strict sconc_snd_empty by metis

lemma ndsmap_srt: assumes "spf1 \<in> ndetsmap T"
  shows "\<exists>spf2\<in>(ndetsmap T). srt\<cdot>(spf1\<cdot>(\<up>m \<Zcat>s)) = spf2\<cdot>s"
proof-
  obtain spf2 out where spf2_def:"spf1\<cdot>(\<up>m \<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s"
    using ndsmap_step assms by blast
  then show ?thesis
    by (metis assms inject_scons ndsmap_step stream.sel_rews(2) 
        strictI surj_scons)
qed

lemma ndsmaplen[simp]: 
  assumes "spf \<in> ndetsmap A"
  shows "#(spf\<cdot>s) = #s"
using assms
proof(induction s arbitrary: spf)
  case adm
  then show ?case 
    by(simp add: len_stream_def)
next
  case bottom
  then show ?case
    using assms ndsmap_unfold by auto
next
  case (step a s)
  then obtain spf2 out where spf2_def:"spf2\<in>(ndetsmap A)\<and> out\<in>(A a) 
                                       \<and> spf\<cdot>(\<up>a\<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s"
    using ndsmap_step[of spf A a s] by blast
  then show ?case 
    by (simp add: step.IH)
qed

text\<open>Thus, each output element of any function in @{const ndetsmap} 
is element of the set determined by the input mapping.\<close>

theorem ndsmap_snth[simp]: 
  assumes "spf \<in> ndetsmap T"
  and "Fin n<#s"
  shows "snth n (spf\<cdot>s) \<in> (T (snth n s))"
  using assms
proof(induction n arbitrary: spf s)
  case 0
  then show ?case
    apply(cases s,auto)
    unfolding ndetsmap_def
    by (metis (no_types, lifting) "0.prems"(1) ndsmap_step shd1)
next
  case (Suc n)
  then show ?case
    apply(cases s,auto)
    apply(simp add: snth_rt)
    using ndsmap_srt by metis
qed

lemma ndsmap_subset[simp]:
  assumes "S={spf | spf. \<forall>n s. (Fin n < #s \<longrightarrow> 
        snth n (spf\<cdot>s) \<in> (A (snth n s))) \<and> #(spf\<cdot>s) = #s \<and> spf\<cdot>\<epsilon>=\<epsilon>}"
  shows "S \<subseteq> ndetsmap A"
  apply(subst ndetsmap_def)
  apply(rule gfp_ordinal_induct)
  using monondetsmap apply blast
  apply(auto simp add: assms)
proof-
  fix S::"('a stream \<rightarrow> 'b stream) set" 
  and x::"'a stream \<rightarrow> 'b stream" and m::'a and s::"'a stream"
  assume a1:"{uu. \<forall>n s. (Fin n < #s \<longrightarrow> 
        snth n (uu\<cdot>s) \<in> A (snth n s)) \<and> #(uu\<cdot>s) = #s \<and> uu\<cdot>\<epsilon> = \<epsilon>} \<subseteq> S"  
  assume a2:"gfp (\<lambda>H. {uu. uu\<cdot>\<epsilon> = \<epsilon> \<and> 
       (\<forall>m s. \<exists>x g. uu\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat> g\<cdot>s \<and> x \<in> A m \<and> g \<in> H)}) \<subseteq> S"
  assume a3:"\<forall>n s. (Fin n < #s \<longrightarrow> 
        snth n (x\<cdot>s) \<in> A (snth n s)) \<and> #(x\<cdot>s) = #s \<and> x\<cdot>\<epsilon> = \<epsilon>"
  then have h0:"\<And>s. #(x\<cdot>(\<up>m \<Zcat> s)) = lnsuc\<cdot>(#s)"
    by simp
  have h2:"\<exists>out. x\<cdot>(\<up>m) = \<up>out"
    apply(rule_tac x="shd (x\<cdot>(\<up>m))" in exI)
    by (simp add: a3)
  have x:"\<And>n s m. Fin n < #(\<up>m \<Zcat> s) \<Longrightarrow> 
          snth n (x\<cdot>(\<up>m \<Zcat> s)) \<in> A (snth n (\<up>m \<Zcat> s))"
    using a3 by auto
  then have h1:"\<And>m s. shd (x\<cdot>(\<up>m \<Zcat> s)) \<in> A m"
    using snth_shd
    by (metis Fin_02bot a3 gr_0 lnzero_def shd1 slen_scons)
  have h3':"\<And>n s. Fin n < #(srt\<cdot>s) 
            \<Longrightarrow> snth n (srt\<cdot>(x\<cdot>s)) \<in> A (snth (Suc n) s)"
    apply (simp add: snth_rt)
  proof-
    fix n::nat and s::"'a stream"
    assume a1:"Fin n < #(srt\<cdot>s)"
    obtain out where out_def:"x\<cdot>s = out"
      by simp
    then have"\<And>n. Fin n < #out \<Longrightarrow> snth n out \<in> A (snth n s)"
      using a3 by auto
    then have "snth (Suc n) out \<in> A (snth (Suc n) s)"
      by (metis a1 a3 dual_order.strict_implies_order less2eq 
           linear neq_iff out_def slen_rt_ile_eq)
    then show "snth n (srt\<cdot>(x\<cdot>s)) \<in> A (snth n (srt\<cdot>s))"
      by(simp add: out_def snth_rt)
  qed
  then have h3:"\<And>n s. Fin n < #s \<Longrightarrow> 
                snth (Suc n) (x\<cdot>(\<up>m \<Zcat> s)) \<in> A (snth n s)"
    by (metis (no_types, lifting) slen_scons snth_rt snth_scons 
        srtlen_lnsuc)
  then have h3:"\<And>n s. Fin n < #s \<Longrightarrow> 
                snth n (srt\<cdot>(x\<cdot>(\<up>m \<Zcat> s))) \<in> A (snth n s)"
    by (simp add: snth_rt)
  show"\<exists>xa g. x\<cdot>(\<up>m \<Zcat> s) = \<up>xa \<Zcat> g\<cdot>s \<and> xa \<in> A m \<and> g \<in> S"
    apply(rule_tac x="shd (x\<cdot>(\<up>m \<Zcat> s))" in exI)
    apply(rule_tac x="(\<Lambda> s. srt\<cdot>(x\<cdot>(\<up>m\<Zcat>s)))" in exI,auto)
    apply (metis a3 empty_is_shortest slen_scons snths_eq 
          stream.sel_rews(2) strictI surj_scons)
    using h1 apply auto[1]
    apply(subgoal_tac "(\<Lambda> s. srt\<cdot>(x\<cdot>(\<up>m \<Zcat> s))) \<in> 
          {uu. \<forall>n s. (Fin n < #s \<longrightarrow> 
          snth n (uu\<cdot>s) \<in> A (snth n s)) \<and> #(uu\<cdot>s) = #s \<and> uu\<cdot>\<epsilon> = \<epsilon>}")
    using a1 apply blast
    apply auto 
    using h3 h0 h2 by auto
qed

text\<open>If this holds for an arbitrary \gls{spf}, that \gls{spf} part
of the \gls{sps} defined by @{const ndetsmap}.\<close>

theorem ndsmap_elem[simp]:
  assumes "\<And>n s. Fin n < #s \<Longrightarrow> snth n (spf\<cdot>s) \<in> (T (snth n s))"
  and "\<And>s. #(spf\<cdot>s) = #s"
  shows "spf\<in> ndetsmap T"
  apply(subgoal_tac "{spf} \<subseteq> {spf |spf. \<forall>n s. 
  (Fin n < #s \<longrightarrow> snth n (spf\<cdot>s) \<in> T (snth n s)) \<and> #(spf\<cdot>s) = #s \<and> 
        spf\<cdot>\<epsilon> = \<epsilon>}")
  using ndsmap_subset
  apply (metis (mono_tags, lifting) insert_subset subset_iff)
  by (auto simp add: assms)

text\<open>If the input function of @{const ndetsmap} always maps to a
singleton, the resulting \gls{sps} is a singleton itself and its 
only function is definable as a @{const smap} mapping.\<close>

theorem ndsmap2smap:
  assumes"\<And>m. is_singleton (T m)"
  and "spf \<in> ndetsmap T"
  shows "spf = smap (\<lambda>e. SOME x. x\<in> T e)"
  apply(rule cfun_eqI)
  apply(rule snths_eq,simp)
  using assms(2) ndsmaplen apply blast 
  apply auto
proof-
  fix x::"'a stream" and n::nat
  assume a1:"Fin n < #(spf\<cdot>x)"
  then obtain out where out_def: "{out} = T (snth n x)"
    using assms(1)
    by (metis is_singleton_the_elem)
  then have "snth n (spf\<cdot>x) = out"
    using a1 assms(2) ndsmaplen by auto
  moreover have"snth n (smap (\<lambda>e::'a. SOME x::'b. x \<in> T e)\<cdot>x) = out"
    by (metis a1 all_not_in_conv assms(2) ndsmaplen out_def 
        singleton_iff smap_snth_lemma some_in_eq)
  ultimately show "snth n (spf\<cdot>x) = 
                   snth n (smap (\<lambda>e::'a. SOME x::'b. x \<in> T e)\<cdot>x)"
    by simp
qed

theorem ndsmap2singleton:
  assumes"\<And>m. is_singleton (T m)"
  shows "is_singleton (ndetsmap T)"
  apply(rule is_singletonI')
  apply(subgoal_tac "smap (\<lambda>e. SOME x. x\<in> T e) \<in> ndetsmap T",auto)
  apply(rule ndsmap_elem,auto)
  apply(simp add: smap_snth_lemma)
proof-
  fix n::nat and s::"'a stream"
  obtain e where e_def: "{e} = T (snth n s)"
    by (metis assms is_singleton_the_elem)
  then show "Fin n < #s \<Longrightarrow> 
                         (SOME x. x \<in> T (snth n s)) \<in> T (snth n s)"
    by auto
  show "\<And>x y. x \<in> ndetsmap T \<Longrightarrow> y \<in> ndetsmap T \<Longrightarrow> x = y"
    using ndsmap2smap  assms by blast
qed

lemma ndsmap_svalue[simp]:
  assumes "spf \<in> ndetsmap A"
  shows "sValues\<cdot>(spf\<cdot>s) \<subseteq> \<Union> (A ` (sValues\<cdot>s))"
  apply(auto)
  apply(simp add: sValues_def2)
  by (metis assms ndsmap_snth ndsmaplen)


subsection\<open>Non-deterministic @{const sscanl}\<close>

lemma monondetsscanl[simp]:"mono (\<lambda>H. \<lambda> state. {f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> 
                  (\<forall>m. \<exists>x e g. (e,x)\<in>(T state m) \<and> g\<in>H e \<and> 
                  (\<forall>s. f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s))})"
  apply(rule monoI)
  apply(simp add: prod.case_eq_if le_fun_def,auto)
  by (meson subset_iff)


definition ndetsscanl::
"('s::type \<Rightarrow> 'a::countable \<Rightarrow> ('s \<times> 'b::countable) set) 
                    \<Rightarrow> 's \<Rightarrow> ('a stream \<rightarrow> 'b stream) set" where
"ndetsscanl T = gfp (\<lambda>H. \<lambda> state. {f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> (\<forall>m. \<exists>x e g.  
                (e,x)\<in>(T state m) \<and> g\<in>H e
                \<and> (\<forall>s. f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s))})"


lemma ndsscanl_unfold:"ndetsscanl S = (\<lambda> state. {f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> 
                (\<forall>m. \<exists>x e g.  
                (e,x)\<in>(S state m) \<and> 
                 g\<in>ndetsscanl S e \<and> (\<forall>s. f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s))})"
  unfolding ndetsscanl_def
  apply(subst gfp_unfold)
  using monondetsscanl by auto

lemma ndsscanl_unfold2:"ndetsscanl S state = {f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> 
                (\<forall>m. \<exists>x e g. (e,x)\<in>(S state m) \<and> 
                 g\<in>ndetsscanl S e \<and> (\<forall>s. f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s))}"
  unfolding ndetsscanl_def
  apply(subst gfp_unfold)
  using monondetsscanl by auto


lemma ndsscanl_strict[simp]:"spf \<in> ndetsscanl S s \<Longrightarrow> spf\<cdot>\<epsilon>=\<epsilon>"
  using ndsscanl_unfold[of S] apply auto
  by (metis (mono_tags, lifting) mem_Collect_eq)

lemma ndsscanl_step: assumes "spf1 \<in> ndetsscanl T e"
  shows "\<exists>ns out spf2. (ns,out)\<in>(T e m) \<and> spf2\<in>(ndetsscanl T ns) \<and>  
              (\<forall>s. spf1\<cdot>(\<up>m\<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s)"
  apply (insert assms)
  using ndsscanl_unfold2[of T e] apply auto
  by blast

lemma ndsscanl_message: assumes "spf1 \<in> ndetsscanl T e"
  shows "\<exists>out\<in>(snd` T e m). spf1\<cdot>(\<up>m) = \<up>out"
  using ndsscanl_step[of spf1 T e m] assms 
  apply auto
  by (metis ndsscanl_strict sconc_snd_empty snd_conv)

lemma ndsscanl_srt: assumes "spf1 \<in> ndetsscanl T e"
  shows "\<exists>ns\<in>(fst` T e m). \<exists>spf2\<in>(ndetsscanl T ns). 
            srt\<cdot>(spf1\<cdot>(\<up>m \<Zcat>s)) = spf2\<cdot>s"
proof-
  obtain spf2 out ns where spf2_def:"(ns,out)\<in>(T e m) \<and> 
    spf2\<in>(ndetsscanl T ns) \<and> spf1\<cdot>(\<up>m \<Zcat>s) = \<up>out \<Zcat> spf2\<cdot>s"
    using ndsscanl_step[of spf1 T e m] assms by auto 
  then show ?thesis 
    using strictI surj_scons by fastforce
qed

lemma ndsscanl_len[simp]: 
  assumes "spf \<in> ndetsscanl T e"
  shows "#(spf\<cdot>s) = #s"
using assms
proof(induction s arbitrary: spf e)
  case adm
  then show ?case 
    by(simp add: len_stream_def)
next
  case bottom
  then show ?case
    using assms ndsmap_unfold by auto
next
  case (step a s)
  then show ?case
    by (smt mem_Collect_eq ndsscanl_unfold2 slen_scons step.IH 
        step.prems)
qed


theorem ndsscanl_snth[simp]: 
  assumes "spf \<in> ndetsscanl T e"
  and "Fin n<#input"
  shows "\<exists>ns. snth n (spf\<cdot>input) \<in> (snd `(T ns (snth n input)))"
  using assms
proof(induction n arbitrary: spf input T e)
  case 0
  then show ?case
    apply(cases input,auto)
    unfolding ndetsscanl_def 
    by (smt "0.prems"(1) mem_Collect_eq ndsscanl_unfold2 
        rev_image_eqI shd1 snd_conv)
next
  case (Suc n)
  then show ?case
    apply(cases input,auto)
    by(metis snth_rt ndsscanl_srt)
qed

theorem ndsscanl_snthsuc: 
  assumes "spf \<in> ndetsscanl T e"
  and "Fin (Suc n)<#(\<up>a \<Zcat> b)"
shows "\<exists>ns\<in>(fst `(T e a)). \<exists>spf2\<in>ndetsscanl T ns. 
      snth (Suc n) (spf\<cdot>(\<up>a \<Zcat> b)) = snth n (spf2\<cdot>b)"
proof-
  obtain out ns spf2 where ns_def:"spf\<cdot>(\<up>a \<Zcat> b) = \<up>out \<Zcat> spf2\<cdot>b 
    \<and> ns\<in> (fst `(T e a)) \<and> spf2\<in>ndetsscanl T ns"
    using ndsscanl_step[of spf T e a] assms(1) by fastforce
  then show ?thesis
    apply(simp add: snth_rt)
    by blast
qed

lemma ndsscanl_svalue[simp]:
  assumes "spf \<in> ndetsscanl T e"
  shows "sValues\<cdot>(spf\<cdot>s) \<subseteq>  
             \<Union> (\<Union> ( (\<lambda>e. {snd `(T x e) | x. True}) ` (sValues\<cdot>s)))"
  apply(auto)
  apply(simp add: sValues_def2)
  by (metis assms ndsscanl_snth ndsscanl_len)


lemma ndsscanl2sscanlaut:
  assumes "\<And>s m. is_singleton (T s m)"
  and "spf\<in> ndetsscanl T st"
  shows "spf = sscanlAutOne (\<lambda>s m. (SOME x . x \<in> (T s m))) st"
  apply(rule cfun_eqI)
  apply(rule snths_eq)
  using assms(2) apply simp  
  apply auto
proof-
  fix x::"'b stream" and n::nat
  show "Fin n < #(spf\<cdot>x) \<Longrightarrow> 
  snth n (spf\<cdot>x) = snth n (sscanlAutOne (\<lambda>st m. SOME x. x \<in> T st m) st\<cdot>x)"
    apply(cases x)
    using assms(2) apply auto[1]
    using assms
  proof(induction n arbitrary: spf st x)
    case 0
    moreover obtain ns nout spf2 where 
      nout_def:"T st a = {(ns,nout)} \<and> (spf\<cdot>(\<up>a \<Zcat> s)) = \<up>nout \<Zcat> spf2\<cdot>s"
      using ndsscanl_step[of spf T st a]
      by (metis calculation(3) calculation(4) is_singleton_the_elem 
          singleton_iff)
    ultimately show ?case
      by simp    
  next
    case (Suc n)
    moreover obtain ns out where out_def:"T st a = {(ns,out)}"
      by (metis assms(1) is_singletonE old.prod.exhaust)
    moreover obtain spf2 where ns_def:
      "snth (Suc n) (spf\<cdot>(\<up>a \<Zcat> s)) = snth n (spf2\<cdot>s) 
        \<and> spf2\<in>ndetsscanl T ns"
      using assms(1) out_def ndsscanl_snthsuc[of spf T st n a s]
      using calculation(2) calculation(3) calculation(5) by auto
    ultimately show ?case
      apply(simp only: ns_def out_def)
      apply(insert Suc.IH[of spf2])
    proof(cases s)
      case bottom
      then show "s = \<epsilon> \<Longrightarrow> snth n (spf2\<cdot>s) = 
                            snth (Suc n) 
                (sscanlAutOne (\<lambda>st m. SOME x. x \<in> T st m) st\<cdot>(\<up>a \<Zcat> s))"
        by (metis ndsscanl_strict ns_def sscanlautone_bot 
            sscanlaut_snth)
    next
      case (step aa ss)
      then have "Fin (Suc n) < #(\<up>a \<Zcat> s)"
        using Suc.prems(1) Suc.prems(2) 
          ndsscanl_len[of spf T st "\<up>a \<Zcat> s"]  Suc.prems(4) by auto 
      then have "Fin n < #s"
        by simp
      then have "Fin n < #(\<up>aa \<Zcat> ss)"
        by (simp add: local.step)
      then have "snth n (spf2\<cdot>(\<up>aa \<Zcat> ss)) = 
      snth n (sscanlAutOne (\<lambda>st m. SOME x. x \<in> T st m) ns\<cdot>(\<up>aa \<Zcat> ss))"
        apply(subst Suc.IH[of spf2 "\<up>aa \<Zcat> ss" aa ss ns])
        apply(subst ndsscanl_len[of spf2 T ns], simp add: ns_def)
        by(simp_all add: assms(1) ns_def)
      then show "snth n (spf2\<cdot>s) = 
  snth (Suc n) (sscanlAutOne (\<lambda>st m. SOME x. x \<in> T st m) st\<cdot>(\<up>a \<Zcat> s))"
        using local.step out_def by auto
    qed
  qed
qed

lemma ndsscanl2smap:
  assumes "\<And>s m. is_singleton (T s m)"
  and "spf\<in> ndetsscanl T (st::'a::type)"
  and "\<And>m . \<forall>s \<in> (T st m). fst s = st"
shows "spf = smap (\<lambda>m. snd (SOME x . x \<in> (T st m)))"
  apply(subst ndsscanl2sscanlaut[of T spf st])
  apply(simp_all add: assms)
  apply(rule sscanlautone2smap)
proof-
  obtain touts where touts_def:"\<And>m. \<exists>out. T st m = {(touts,out)}"
    by (metis assms(1) assms(3) eq_fst_iff is_singletonE singleton_iff)
  then have "touts = st"
    using assms(3) by fastforce
  then show "\<And>m. fst (SOME x. x \<in> T st m) = st"
    using assms(3) some_in_eq touts_def by fastforce
qed

lemma sbelowndet[simp]:assumes "S =(\<lambda> state. {spf | spf. spf\<cdot>\<epsilon> = \<epsilon> \<and> 
(\<forall>m. \<exists>x e g. (e, x) \<in> T state m \<and> g \<in> S e \<and> (\<forall>s. spf\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat> g\<cdot>s))})"
  shows "S \<le> ndetsscanl T"
  apply(subst ndetsscanl_def)
  apply(rule gfp_upperbound)
  using assms by auto

lemma ssubsetndetsscln:
  assumes"S =(\<lambda> state. {spf | spf. spf\<cdot>\<epsilon> = \<epsilon> \<and> 
(\<forall>m. \<exists>x e g. (e, x) \<in> T state m \<and> g \<in> S e \<and> (\<forall>s. spf\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat> g\<cdot>s))})"
  shows "S st \<subseteq> ndetsscanl T st"
  apply(rule le_funD[of S])
  by(insert assms,simp)
   
lemma ndsscanl_elem:
  assumes sdef:"S =(\<lambda> state. {spf | spf. spf\<cdot>\<epsilon> = \<epsilon> \<and> 
(\<forall>m. \<exists>x e g. (e, x) \<in> T state m \<and> g \<in> S e \<and> (\<forall>s. spf\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat> g\<cdot>s))})"
  and"spf\<cdot>\<epsilon>=\<epsilon>"
  and "\<And>m. \<exists>x e g.(e,x) \<in> T st m \<and> g\<in> S e \<and> (\<forall>s. spf\<cdot>(\<up>m \<Zcat> s) = \<up>x \<Zcat>g\<cdot>s)"
  shows "spf \<in> ndetsscanl T st"
  apply(subgoal_tac "spf\<in> S st")
  using ssubsetndetsscln[of S T st]
  using assms(1) apply blast
  apply(subst sdef)
  using assms (2,3) by auto
(*
lemma ndetsscanl_otherdef_h:"{f | f. (f\<cdot>\<epsilon>=\<epsilon>)  \<and> (\<forall>m. \<exists>x e g.  
                (e,x)\<in>(T state m) \<and> g\<in>H e
                \<and> (\<forall>s. f\<cdot>(\<up>m\<Zcat>s) = \<up>x \<Zcat> g\<cdot>s))}
     = {stream_step\<cdot>f | f. (\<forall>m. \<exists>x e g.  
                (e,x)\<in>(T state m) \<and> g\<in>H e
                \<and> (\<forall>s. f m\<cdot>s = \<up>x \<Zcat> g\<cdot>s))}"
  apply(auto)
  apply(rule_tac x="(\<lambda>m. \<Lambda> s. x\<cdot>(\<up>m \<Zcat> s))" in exI,auto)
  by(rule streamsplit_eqI,simp_all)
  
lemma ndetsscanl_otherdef:
"ndetsscanl T = gfp (\<lambda>H. \<lambda> state. {stream_step\<cdot>f | f. (\<forall>m. \<exists>x e g.  
                (e,x)\<in>(T state m) \<and> g\<in>H e
                \<and> (\<forall>s. f m\<cdot>s = \<up>x \<Zcat> g\<cdot>s))})"
  apply(subst ndetsscanl_def, subst ndetsscanl_otherdef_h)
  ..
*)
definition ndetsscanlout::"('s::type \<Rightarrow> 'a::countable \<Rightarrow> ('s \<times> 'b::countable) set) 
                    \<Rightarrow> 's \<Rightarrow> 'a stream \<Rightarrow> 'b stream set" where
"ndetsscanlout T state s \<equiv> (\<lambda>spf. spf\<cdot>s) ` (ndetsscanl T state)"

lemma assumes "spf \<in> ndetsscanl T state"
  shows "spf\<cdot>s \<in> ndetsscanlout T state s"
  by (simp add: assms ndetsscanlout_def)

 lemma [simp]:assumes"out \<in> ndetsscanlout T state \<epsilon>"
  shows "out = \<epsilon>"
   apply(insert assms,simp add: ndetsscanlout_def) 
   by auto

lemma ndetsscanlout2_mono[simp]:"mono (\<lambda>H. \<lambda> state s. if s= \<epsilon> then {\<epsilon>} else \<Union>((\<lambda> (nextState,outElem). (\<lambda>rest. \<up>outElem \<Zcat> rest) ` H nextState (srt\<cdot>s)) ` (T state (shd s))))"
  apply(rule monoI)
  apply(simp add: le_fun_def,auto)
  by blast

definition ndetsscanlout2::"('s::type \<Rightarrow> 'a::countable \<Rightarrow> ('s \<times> 'b::countable) set) 
                    \<Rightarrow> 's \<Rightarrow> 'a stream \<Rightarrow> 'b stream set" where
"ndetsscanlout2 T \<equiv> gfp (\<lambda>H. \<lambda> state s. if s= \<epsilon> then {\<epsilon>} else \<Union>((\<lambda> (nextState,outElem). (\<lambda>rest. \<up>outElem \<Zcat> rest) ` H nextState (srt\<cdot>s)) ` (T state (shd s))))"


lemma ndsscanlout_unfold:"ndetsscanlout2 T = (\<lambda> state s. 
                      if s= \<epsilon> then {\<epsilon>} else 
  \<Union>((\<lambda> (nextState,outElem). (\<lambda>rest. \<up>outElem \<Zcat> rest) ` ndetsscanlout2 T nextState (srt\<cdot>s)) ` (T state (shd s))))"
  unfolding ndetsscanlout2_def
  apply(subst gfp_unfold)
  using ndetsscanlout2_mono apply simp 
  by auto 

lemma ndetsscanlout_eps[code]:"ndetsscanlout2 T s \<epsilon> = {\<epsilon>}"
  by(simp add: ndsscanlout_unfold)

lemma ndetsscanlout_step [code]: "ndetsscanlout2 T state (\<up>x \<Zcat> xs) = 
  \<Union>((\<lambda> (nextState,outElem). (\<lambda>rest. \<up>outElem \<Zcat> rest) ` ndetsscanlout2 T nextState xs) ` (T state x))"
  by(subst ndsscanlout_unfold,simp)



lemma ndsscanl2ndsmap: 
  assumes "\<And>m. \<forall>out \<in>(T st m). fst out = st"
  shows "ndetsscanl T st = ndetsmap (\<lambda>m. snd ` T st m)"
  apply auto
   apply(rule ndsmap_elem,simp_all)
  oops



end
