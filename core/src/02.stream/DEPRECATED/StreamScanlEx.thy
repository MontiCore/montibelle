theory StreamScanlEx
imports stream.StreamScanl

begin


definition sscanlA ::
 "('s \<Rightarrow>'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's  \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"sscanlA f s0 \<equiv> \<Lambda> s. sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s)"


definition sscanlAg ::
"('s \<Rightarrow>'a \<Rightarrow> ('s \<times>'b)) \<Rightarrow> 's \<Rightarrow> 'a stream \<rightarrow> ('s\<times>'b) stream" where
"sscanlAg f s0 \<equiv> \<Lambda> s. (sscanl (\<lambda>(b,_). f b) (s0, undefined)\<cdot>s)"

text\<open>We first defined the general stateful @{const sscanlAg}.
The definition calls @{const sscanl} internally, @{const sscanl}
computes the output of each element depending on the input and the 
output of the last element. Likewise, it needs an initial output 
element it starts with. The general stateful function however 
only needs the previous output state, not the whole output.\<close>

text\<open>Since the semantic of an deterministic automaton does not 
return its states in each step but behaves similar in other cases,
we define another stateful function, that calls @{const sscanlAg}
but reduces its output to the message output stream. Hence, the 
state stream is omitted.\<close> 

definition %invisible sscanlAfst ::
"('s \<Rightarrow>'a \<Rightarrow> ('s\<times>'b)) \<Rightarrow> 's \<Rightarrow> 'a stream \<rightarrow> 's stream" where
"sscanlAfst f s0 \<equiv> \<Lambda> s. sprojfst\<cdot>(sscanlAg f s0\<cdot>s)"

definition sscanlAsnd ::
"('s \<Rightarrow>'a \<Rightarrow> ('s \<times>'b)) \<Rightarrow> 's  \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"sscanlAsnd f s0 \<equiv> \<Lambda> s. sprojsnd\<cdot>(sscanlAg f s0\<cdot>s)"

text\<open>A deterministic automatons semantic can then be represented by
a @{const sscanlAsnd} mapping.\<close> 


subsection \<open>@{term sscanlA}\<close>

lemma sscanla_cont: "cont (\<lambda>s. sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s))"
  by simp

lemma sscanla_len [simp]: "#(sscanlA f s0\<cdot>s) = #s"
  by (simp add: sscanlA_def slen_sprojfst)

lemma sscanla_bot [simp]: "sscanlA f s0\<cdot>\<bottom> = \<bottom>"
  by (simp add: sscanlA_def)

lemma sscanla_step [simp]: "sscanlA f s0\<cdot>(\<up>a \<Zcat> as) = \<up>(fst (f s0 a)) \<Zcat> sscanlA f (snd (f s0 a))\<cdot>as"
  apply(simp add: sscanlA_def sprojfst_def)
proof -
  have "(case f s0 a of (a, x) \<Rightarrow> f x) = (case (undefined::'a, snd (f s0 a)) of (a, x) \<Rightarrow> f x)"
by (metis (no_types) old.prod.case prod.collapse)
  then have "\<up>(shd as) \<Zcat> srt\<cdot>as = as \<longrightarrow> sscanl (\<lambda>(a, y). f y) (f s0 a)\<cdot>as = sscanl (\<lambda>(a, y). f y) (undefined, snd (f s0 a))\<cdot> (\<up>(shd as) \<Zcat> srt\<cdot>as)"
    by (metis (no_types) sscanl_scons)
  then show "\<up>(fst (f s0 a)) \<Zcat> smap fst\<cdot> (sscanl (\<lambda>(a, y). f y) (f s0 a)\<cdot> as) = \<up>(fst (f s0 a)) \<Zcat> smap fst\<cdot> (sscanl (\<lambda>(a, y). f y) (undefined, snd (f s0 a))\<cdot> as)"
    using surj_scons by force
qed

lemma sscanla_one [simp]: "sscanlA f b\<cdot>(\<up>x) = \<up>(fst (f b x))"
  apply(simp add: sscanlA_def)
  by (metis prod.collapse sconc_snd_empty sprojfst_scons strict_sprojfst)

lemma sscanla_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanlA f q\<cdot>s) = fst (f q (shd s))"
  by (metis shd1 sscanla_step surj_scons)

lemma sscanla_srt: "srt\<cdot>(sscanlA f a\<cdot>s) = sscanlA f (snd (f a (shd s)))\<cdot>(srt\<cdot>s)"
  by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanla_bot sscanla_step stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

lemma sscanla_ntimes_loop:
  assumes "\<And>r. sscanlA f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlA f state\<cdot>r)" 
  shows "sscanlA f state\<cdot>(sntimes n s) = sntimes n out"
  using assms
  by (induction n, simp_all)

lemma sscanla_inftimes_loop:
  assumes "\<And>r. sscanlA f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlA f state\<cdot>r)"
  shows "sscanlA f state\<cdot>(sinftimes s) = sinftimes out"
  using assms
  by (metis rek2sinftimes sinftimes_unfold slen_empty_eq sscanla_bot sscanla_len strict_icycle) 

subsection \<open>@{term sscanlAg}\<close>

lemma sscanlag_cont: "cont (\<lambda>s. (sscanl (\<lambda>(b,_). f b) (s0, undefined)\<cdot>s))"
  by simp

lemma sscanlag_len [simp]: "#(sscanlAg f s0\<cdot>s) = #s"
  by(simp add: sscanlAg_def slen_sprojsnd)

lemma sscanlag_bot [simp]: "sscanlAg f s0\<cdot>\<bottom> = \<bottom>"
  by (simp add: sscanlAg_def)


lemma sscanlag_one [simp]: "sscanlAg f b\<cdot>(\<up>x) = \<up>(fst(f b x), snd (f b x))"
  by(simp add: sscanlAg_def)

lemma sscanlag_step [simp]: "sscanlAg f s0\<cdot>(\<up>a \<Zcat> as) = \<up>((f s0 a)) \<Zcat> sscanlAg f (fst (f s0 a))\<cdot>as"
  apply(simp add: sscanlAg_def sprojfst_def )
  apply (rule reduce_seq)
  by(rule scases[of as];simp add: case_prod_unfold)

lemma sscanlag_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanlAg f q\<cdot>s) = (f q (shd s))"
  by (metis shd1 sscanlag_step surj_scons)

lemma sscanlag_srt: "srt\<cdot>(sscanlAg f a\<cdot>s) = sscanlAg f (fst (f a (shd s)))\<cdot>(srt\<cdot>s)"
  by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanlag_bot sscanlag_step stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

lemma snth_sscanlAg:
  assumes "Fin (Suc j)<#i"
    shows "snth (Suc j) (sscanlAg f s0\<cdot>i) = f (fst (snth j (sscanlAg f s0\<cdot>i))) (snth (Suc j) i)"
  apply(simp add: sscanlAg_def)
  by (metis (mono_tags, lifting) assms case_prod_conv prod.exhaust_sel sscanl_snth)

lemma sscanlag_ntimes_loop:
  assumes "\<And>r. sscanlAg f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAg f state\<cdot>r)" 
  shows "sscanlAg f state\<cdot>(sntimes n s) = sntimes n out"
  using assms
  by (induction n, simp_all)

lemma sscanlag_inftimes_loop:
  assumes "\<And>r. sscanlAg f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAg f state\<cdot>r)"
  shows "sscanlAg f state\<cdot>(sinftimes s) = sinftimes out"
  using assms
  by (metis rek2sinftimes sinftimes_unfold slen_empty_eq sscanlag_bot sscanlag_len strict_icycle) 

subsection \<open>@{term sscanlAfst}\<close>

lemma sscanlafst_cont: "cont (\<lambda>s. sprojfst\<cdot>(sscanlAg (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s))"
  by simp

lemma sscanlafst_len [simp]: "#(sscanlAfst f s0\<cdot>s) = #s"
  by (simp add: sscanlAfst_def slen_sprojfst)

lemma sscanlafst_bot [simp]: "sscanlAfst f s0\<cdot>\<bottom> = \<bottom>"
  by (simp add: sscanlAfst_def)

lemma sscanlafst_step [simp]: "sscanlAfst f s0\<cdot>(\<up>a \<Zcat> as) = \<up>(fst (f s0 a)) \<Zcat> sscanlAfst f (fst (f s0 a))\<cdot>as"
  apply (simp add: sscanlAfst_def sprojfst_def sscanlAg_def)
  by(cases as rule: scases;simp add: case_prod_beta')
  
lemma sscanlafst_one [simp]: "sscanlAfst f b\<cdot>(\<up>x) = \<up>(fst (f b x))"
  apply(simp add: sscanlAfst_def)
  by (metis prod.collapse sconc_snd_empty sprojfst_scons strict_sprojfst)

lemma sscanlafst_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanlAfst f q\<cdot>s) = fst (f q (shd s))"
  by (metis shd1 sscanlafst_step surj_scons)

lemma sscanlafst_srt: "srt\<cdot>(sscanlAfst f a\<cdot>s) = sscanlAfst f (fst (f a (shd s)))\<cdot>(srt\<cdot>s)"
  by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanlafst_bot sscanlafst_step stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

lemma sscanlafst_snth: assumes "Fin (Suc n) < #s" and "s2 = fst (shd (sscanlAg f state\<cdot>s))"
  shows "snth (Suc n) (sscanlAfst f state\<cdot>s) = snth n (sscanlAfst f s2\<cdot>(srt\<cdot>s))"
  apply(simp add: assms sscanlAfst_def)
  apply(subst sprojfst_snth)
  apply(simp add: assms)
  apply (meson assms(1) leD leI slen_rt_ile_eq)
  apply(subst snth_sscanlAg)
  apply(simp add: assms)
  by (metis (no_types, lifting) assms(1) empty_is_shortest shd1 snth_scons snth_sscanlAg sscanlag_step surj_scons)

lemma sscanlafst_ntimes_loop:
  assumes "\<And>r. sscanlAfst f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAfst f state\<cdot>r)" 
  shows "sscanlAfst f state\<cdot>(sntimes n s) = sntimes n out"
  using assms
  by (induction n, simp_all)

lemma sscanlafst_inftimes_loop:
  assumes "\<And>r. sscanlAfst f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAfst f state\<cdot>r)"
  shows "sscanlAfst f state\<cdot>(sinftimes s) = sinftimes out"
  using assms
  by (metis rek2sinftimes sinftimes_unfold slen_empty_eq sscanlafst_bot sscanlafst_len strict_icycle) 

subsection \<open>@{term sscanlAsnd}\<close>

lemma sscanlasnd_cont: "cont (\<lambda>s. sprojsnd\<cdot>(sscanl (\<lambda>(b,_). f b) (s0, undefined)\<cdot>s))"
  by simp

lemma sscanlasnd_len [simp]: "#(sscanlAsnd f s0\<cdot>s) = #s"
  by(simp add: sscanlAsnd_def slen_sprojsnd)

lemma sscanlasnd_bot [simp]: "sscanlAsnd f s0\<cdot>\<bottom> = \<bottom>"
  by (simp add: sscanlAsnd_def)

lemma sscanlasnd_step [simp]: "sscanlAsnd f s0\<cdot>(\<up>a \<Zcat> as) = \<up>(snd (f s0 a)) \<Zcat> sscanlAsnd f (fst (f s0 a))\<cdot>as"
  apply(simp add: sscanlAsnd_def sprojsnd_def sscanlAg_def)
proof -
  have "(case f s0 a of (x, a) \<Rightarrow> f x) = (case (fst (f s0 a), undefined::'a) of (x, a) \<Rightarrow> f x)"
    by (metis (no_types) old.prod.case prod.collapse)
  then have "\<up>(shd as) \<Zcat> srt\<cdot>as = as \<longrightarrow>(sscanl (\<lambda>(b, uu). f b) (f s0 a)\<cdot>as)= (sscanl (\<lambda>(b, uu). f b) (fst (f s0 a), undefined)\<cdot>as)"
    by (metis (no_types) sscanl_scons)
  then show "\<up>(snd (f s0 a)) \<Zcat> smap snd\<cdot>(sscanl (\<lambda>(b, uu). f b) (f s0 a)\<cdot>as) = \<up>(snd (f s0 a)) \<Zcat> smap snd\<cdot>(sscanl (\<lambda>(b, uu). f b) (fst (f s0 a), undefined)\<cdot>as)"
    using surj_scons by force
qed

lemma sscanlasnd_one [simp]: "sscanlAsnd f b\<cdot>(\<up>x) = \<up>(snd (f b x))"
  apply(simp add: sscanlAsnd_def)
  by (metis eq_snd_iff sconc_snd_empty sprojsnd_scons strict_sprojsnd)

lemma sscanlasnd_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanlAsnd f q\<cdot>s) = snd (f q (shd s))"
  by (metis shd1 sscanlasnd_step surj_scons)

lemma sscanlasnd_srt: "srt\<cdot>(sscanlAsnd f a\<cdot>s) = sscanlAsnd f (fst (f a (shd s)))\<cdot>(srt\<cdot>s)"
  by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanlasnd_bot sscanlasnd_step stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

lemma sscanlasnd_snth: assumes "Fin (Suc n)<#s" and "s2 = fst(shd(sscanlAg f state\<cdot>s))"
  shows "snth (Suc n) (sscanlAsnd f state\<cdot>s) = snth n (sscanlAsnd f s2\<cdot>(srt\<cdot>s))"
  apply(simp add: assms sscanlAsnd_def)
  apply(subst sprojsnd_snth)
   apply(simp add: assms)
  by (metis assms(1) empty_is_shortest eta_cfun rt_Sproj_2_eq smap_snth_lemma snth_rt sprojsnd_def sscanlag_len sscanlag_shd sscanlag_srt)

lemma sscanlasnd_snth2:
  assumes "Fin (Suc n) < #(\<up>a \<Zcat> s)"
  shows "snth (Suc n) (sscanlAsnd f state\<cdot>(\<up>a \<Zcat> s)) = snth n (sscanlAsnd f (fst (f state a))\<cdot>s)"
  using assms
  apply (induction s arbitrary: a rule: ind)
  by simp_all

lemma sscanlasnd_ntimes_loop:
  assumes "\<And>r. sscanlAsnd f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAsnd f state\<cdot>r)" 
  shows "sscanlAsnd f state\<cdot>(sntimes n s) = sntimes n out"
  using assms
  by (induction n, simp_all)

lemma sscanlasnd_inftimes_loop:
  assumes "\<And>r. sscanlAsnd f state\<cdot>(s \<Zcat> r) = out \<Zcat> (sscanlAsnd f state\<cdot>r)"
  shows "sscanlAsnd f state\<cdot>(sinftimes s) = sinftimes out"
  using assms
  by (metis rek2sinftimes sinftimes_unfold slen_empty_eq sscanlasnd_bot sscanlasnd_len strict_icycle) 

lemma sscanlasnd2sinftimes:
  assumes "#s=\<infinity>"
    and "sscanlAsnd f state\<cdot>s = out \<Zcat> (sscanlAsnd f state\<cdot>s)"
    and "out \<noteq> \<epsilon>"
  shows "sscanlAsnd f state\<cdot>s = sinftimes out"
  using assms rek2sinftimes by auto

lemma sscanl2smap:
  assumes "\<And>e. fst(f s e) = s"
  and "g = (\<lambda>a. snd(f s a))"
shows"sscanlAsnd f s = smap g"
  apply(rule cfun_eqI)
  by(induct_tac x rule: ind,simp_all add: assms)


lemma sscanlasnd_smap_state_loop:
  assumes"\<And>e. e \<in> sValues\<cdot>s \<Longrightarrow> fst (f state e) = state"
shows "sscanlAsnd f state\<cdot>(s) = smap (\<lambda>e. snd (f state e))\<cdot>s"
  using assms
  apply (induction s rule: ind)
  apply (rule adm_imp)
  apply (rule admI)
  apply (meson sValues_chain2lub set_rev_mp)
  by simp_all

lemma sscanla_exchange_f:
  assumes "\<And>e state. P e \<Longrightarrow> F1 state e = F2 state e" 
    and "\<forall>x \<in> sValues\<cdot>s. P x"
  shows "sscanlAsnd F1 state\<cdot>s = sscanlAsnd F2 state\<cdot>s"
  using assms
  apply (induction s arbitrary: state rule: ind)
  apply (rule adm_imp, simp)+
  apply (rule admI)
  apply (meson sValues_chain2lub subsetCE)
  by simp_all

definition sscanlAut ::
"('s::type \<Rightarrow>'a \<Rightarrow> ('s \<times>'b stream)) \<Rightarrow> 's  \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"sscanlAut f \<equiv> fix\<cdot>(\<Lambda> H. (\<lambda>st. \<Lambda> is. slookahd\<cdot>is\<cdot>(\<lambda>m. (snd (f st m)) 
\<Zcat> H (fst (f st m))\<cdot>(srt\<cdot>is))))"

definition sscanlAutOne::
"('s::type \<Rightarrow>'a \<Rightarrow> ('s \<times>'b)) \<Rightarrow> 's  \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"sscanlAutOne f s = sscanlAut (\<lambda> s a. apsnd (sup') (f s a)) s"

lemma sscnalaut_cont[simp]:
"cont (\<lambda> H. (\<lambda>st. \<Lambda> is. slookahd\<cdot>is\<cdot>(\<lambda>m. (snd (f st m)) 
\<Zcat> H (fst (f st m))\<cdot>(srt\<cdot>is))))"
  by(intro cont2cont)

lemma sscanlaut_unfold:"sscanlAut f = 
(\<lambda>st. \<Lambda> is. slookahd\<cdot>is\<cdot>(\<lambda>m. (snd (f st m)) \<Zcat> 
sscanlAut f (fst (f st m))\<cdot>(srt\<cdot>is)))"
  apply(simp add: sscanlAut_def)
  by(subst fix_eq,auto)

lemma sscanlaut_insert:"sscanlAut f st\<cdot>is = slookahd\<cdot>is\<cdot>(\<lambda>m. (snd (f st m)) \<Zcat> 
sscanlAut f (fst (f st m))\<cdot>(srt\<cdot>is))"
  by(subst sscanlaut_unfold, simp)

lemma sscanlaut_bot[simp]:"sscanlAut x xa\<cdot>\<epsilon> = \<epsilon>"
  by(subst sscanlaut_unfold,auto)

lemma sscanlautone_bot[simp]:"sscanlAutOne x xa\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: sscanlAutOne_def)

lemma sscanlaut_step[simp]:"sscanlAut f s\<cdot>(\<up>a \<Zcat> b) = (snd(f s a)) \<Zcat> 
                            sscanlAut f (fst (f s a))\<cdot>b"
  by(subst sscanlaut_unfold,auto)

lemma sscanlaut_laststep[simp]:"sscanlAut f s\<cdot>(\<up>a) = (snd(f s a))"
  by(subst sscanlaut_unfold, simp)

lemma sscanlautone_step[simp]:"sscanlAutOne f s\<cdot>(\<up>a \<Zcat> b) = 
        \<up>(snd(f s a)) \<Zcat> sscanlAutOne f (fst (f s a))\<cdot>b"
  by(simp add: sscanlAutOne_def)

lemma sscanlaut_leneq[simp]: assumes "\<And> state input. 1=#(snd (f state input))"
  shows "#s = #(sscanlAut f x\<cdot>s)"
  apply(induction s arbitrary: x,simp_all)
  apply(rule adm_all, rule adm_eq)
  apply(simp add: len_stream_def)
  apply(simp add: len_stream_def)
  using assms apply(simp add: sconc_slen2)
  by (metis add.commute lnat_plus_suc)

lemma sscanlaut_len[simp]: assumes "\<And> state input. 1\<le>#(f state input)"
  shows "#s \<le> #(sscanlAut f x\<cdot>s)"
  apply(induction s arbitrary: x,simp_all)
  apply(induction s arbitrary: x,simp_all)
  apply(rule adm_all, rule admI)
  apply(simp add: contlub_cfun_arg lub_mono2  len_stream_def)
  apply(simp add: sconc_slen2)
  by (metis add.commute assms len_prod_def 
      lessequal_addition lnat_plus_suc min.bounded_iff)

lemma sscanlautone_len[simp]:"#(sscanlAutOne f x\<cdot>s) = #s"
  apply(induction s arbitrary: x,simp_all add: sscanlAutOne_def)
  by(simp add: len_stream_def)
 
lemma sscanlaut2sscanlasnd_h:"sscanlAutOne x xa\<cdot>xb = sscanlAsnd x xa\<cdot>xb"
  by(induction xb arbitrary: xa,simp_all add: sscanlAutOne_def)
 
lemma sscanlaut2sscanlasnd:"sscanlAutOne = sscanlAsnd"
  by(metis sscanlaut2sscanlasnd_h fun_eq_iff cfun_eqI) 

lemma sscanlaut_snth[simp]:"snth (Suc n) (sscanlAutOne f x\<cdot>(\<up>a \<Zcat> s)) = 
       snth n (sscanlAutOne f (fst (f x a))\<cdot>s)"
  by simp

lemma sscanlautone_smap_state_loop:
  assumes"\<And>e. e \<in> sValues\<cdot>s \<Longrightarrow> fst (f state e) = state"
  shows "sscanlAutOne f state\<cdot>(s) = smap (\<lambda>e. snd (f state e))\<cdot>s"
  using assms
  apply (induction s)
  apply (rule adm_imp)
  apply (rule admI)
  apply (meson sValues_chain2lub set_rev_mp)
  by simp_all


lemma sscanlautone2smap:
  assumes "\<And>e. fst (f state e) = state"
  shows"sscanlAutOne f state = smap (\<lambda>e. snd (f state e))"
  apply(rule cfun_eqI)
  apply(rule sscanlautone_smap_state_loop)
  by(simp add: assms)
end