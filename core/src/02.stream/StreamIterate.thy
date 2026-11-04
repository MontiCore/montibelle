theory StreamIterate
imports Stream StreamScanl

begin

default_sort countable

text \<open>@{term siterate}: Create a stream by repeated application of
  a function to an element. The generated stream starts with \<open>a\<close>,
  \<open>f(a)\<close>, \<open>f(f(a))\<close>, and so on.\<close>
definition siterate   :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
"siterate f (a::'a) \<equiv> \<up>a \<Zcat> sscanl (\<lambda>a (b::'a). f a) a\<cdot>(SOME x. #x = \<infinity>)"

text \<open>Alternative definition similar to @{term siterate},
it is more general than @{term siterate}\<close>
definition siterateBlock:: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
"siterateBlock f \<equiv> fix \<cdot> (\<Lambda> h. (\<lambda>s. s \<Zcat> (h (f s))))"



subsection \<open>@{term siterate}\<close>

text \<open>@{term siterate} is defined by running @{term sscanl} on an arbitrary
  infinite stream. Only the stream length is relevant for the result\<close>
lemma siterate_inv_lemma:
  "\<forall>x z a. #z = #x 
     \<longrightarrow> stake n\<cdot>(sscanl (\<lambda>a b. f a) a\<cdot>x) = 
        stake n\<cdot>(sscanl (\<lambda>a b. f a) a\<cdot>z)"
apply (induct_tac n, auto)
apply (rule_tac x=x in scases, auto)
by (rule_tac x=z in scases, auto)

text \<open>@{term siterate} is well-defined (because it is independent of
  the infinite stream on which @{term sscanl} is applied)\<close>
lemma siterate_def2:
  "#x = \<infinity> \<Longrightarrow> siterate f a = \<up>a \<Zcat> sscanl (\<lambda>a b. f a) a\<cdot>x"
apply (subst siterate_def)
apply (rule someI2_ex)
apply (rule_tac x="sinftimes (\<up>(SOME a. True))" in exI, simp)
apply (rule cfun_arg_cong)
apply (rule stream.take_lemma)
by (rule siterate_inv_lemma [rule_format], simp)

text \<open>unfolding of @{term siterate} definition\<close>
lemma siterate_scons: "siterate f a = \<up>a \<Zcat> siterate f (f a)"
apply (rule stream.take_lemma [OF spec [where x="a"]])
apply (induct_tac n, auto)
apply (insert siterate_def2 [of _ f], atomize)
apply (erule_tac x="sinftimes (\<up>x)" in allE, auto)
by (subst sinftimes_unfold, simp)

primrec niterate :: "nat \<Rightarrow> ('a::type \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
    "niterate 0 = (\<lambda> F x. x)"
  | "niterate (Suc n) = (\<lambda> F x. F (niterate n F x))"

lemma niterate_Suc2: "niterate (Suc n) F x = niterate n F (F x)"
apply(induction n)
by(simp_all)

lemma niter2iter: "iterate g\<cdot>h\<cdot>x = niterate g (Rep_cfun h) x"
apply (induction g)
by(simp_all)
  
lemma iterate_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
  shows "(iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<Zcat> h (g s)))\<cdot>\<bottom>) \<epsilon> = \<epsilon>" 
using assms by (induction i, auto)
  
lemma fix_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
  shows "(\<mu> h. (\<lambda>s. s \<Zcat> h (g s))) \<epsilon> = \<epsilon>"
proof -
  have aI: "max_in_chain 0 (\<lambda>i. (iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<Zcat> h (g s)))\<cdot>\<bottom>) \<epsilon> )" by (simp add: max_in_chainI assms)
  hence "(\<Squnion>i. (iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<Zcat> h (g s)))\<cdot>\<bottom>) \<epsilon>) = \<epsilon>"  using assms by auto 
  hence " (\<Squnion> i. iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<Zcat> h (g s)))\<cdot>\<bottom>) \<epsilon> = \<epsilon>" by (simp add: lub_fun) 
  thus ?thesis using fix_def2 by (metis (no_types, lifting) lub_eq)
qed

lemma siterate_sdrop: "siterate h (h x) = sdrop 1\<cdot>(siterate h x)"
by (metis One_nat_def sdrop_0 sdrop_scons siterate_scons)

lemma siterate_drop2iter: "siterate h (niterate i h x) = sdrop i\<cdot>(siterate h x)"
apply (induction i)
apply (simp add: One_nat_def)
by (simp add: sdrop_back_rt siterate_sdrop One_nat_def)

lemma shd_siter[simp]: "shd (siterate g x) = x"
by (simp add: siterate_def)

lemma shd_siters: "shd (sdrop i\<cdot>(siterate g x)) = niterate i g x"
by (metis shd_siter siterate_drop2iter)   

text \<open>Addition of two numbers using @{term "siterate Suc"}\<close>
lemma snth_siterate_Suc: "snth k (siterate Suc j) = k + j"
apply (rule_tac x="j" in spec)
apply (induct_tac k, simp)
apply (rule allI)
by (subst siterate_scons, simp)+

lemma snth_siterate_Suc_0[simp]: "snth k (siterate Suc 0) = k"
by (simp add: snth_siterate_Suc)

lemma sdrop_siterate:
  "sdrop k\<cdot>(siterate Suc j) = siterate Suc (j + k)"
apply (rule_tac x="j" in spec)
apply (induct_tac k, simp+)
apply (rule allI)
by (subst siterate_scons, simp)

text \<open>@{term siterate} only creates infinite outputs\<close>
lemma siter_len [simp]: "#(siterate f k) = \<infinity>"
apply (rule infI)
apply (rule allI)
apply (rule_tac x="k" in spec)
apply (induct_tac k, simp+)
by (subst siterate_scons, simp)+

lemma snth_siter: "snth i (siterate g x) = niterate i g x"
by (simp add: shd_siters snth_def)

lemma snth_snth_siter: "snth (Suc i) (siterate g x) = g (snth i (siterate g x))"
by (simp add: snth_siter)

lemma sdrop_siter:  "sdrop 1\<cdot>(siterate g x) = smap g\<cdot>(siterate g x)"
apply(rule sinf_snt2eq)
apply (simp add: fair_sdrop) 
apply simp
by (simp add: smap_snth_lemma snth_sdrop snth_snth_siter One_nat_def)

lemma iterate_insert: assumes "\<forall>z. h (g z) = g (h z)"
  shows "niterate i h (g x) = g (niterate i h x)"
using assms by (induction i, auto)

lemma siterate_smap:  assumes "\<forall>z. g (h z) = h (g z)"
  shows "smap g\<cdot>(siterate h x) = siterate h (g x)"
apply (rule sinf_snt2eq, auto)
by (simp add: assms smap_snth_lemma snth_siter iterate_insert)

lemma siterate_unfold: "siterate g x = \<up>x \<Zcat> smap g\<cdot>(siterate g x)"
by (metis siterate_scons siterate_smap)

lemma siter2sinf: "siterate id x = sinftimes (\<up>x)"
by (metis id_apply s2sinftimes siterate_scons)

lemma "sdrop i\<cdot>(siterate id x) = siterate id x"
  by (metis sdrops_sinf siter2sinf)

lemma siter2sinf2: assumes "g x = x"
  shows "siterate g x = sinftimes (\<up>x)"
by (metis assms s2sinftimes siterate_scons)

lemma rek2niter: assumes "xs = \<up>x \<Zcat> (smap g\<cdot>xs)"
  shows "snth i xs = niterate i g x"
proof (induction i)
  case 0 thus ?case by (metis assms niterate.simps(1) shd1 snth_shd)
next
  case (Suc i) 
  have "#xs = \<infinity>" by (metis Inf'_def assms below_refl fix_least_below inf_less_eq lnle_def slen_scons slen_smap)
  thus ?case by (metis Fin_neq_inf Suc assms inf_ub lnle_def lnless_def niterate.simps(2) smap_snth_lemma snth_scons)
qed

lemma rek2siter: assumes "xs = \<up>x \<Zcat> (smap g\<cdot>xs)"
  shows "xs = siterate g x" 
apply (rule sinf_snt2eq, auto)
apply (metis Inf'_def assms fix_least inf_less_eq lnle_conv slen_scons slen_smap) 
by (metis assms rek2niter snth_siter)

lemma fixrek2siter: "fix\<cdot>(\<Lambda> s . (\<up>x \<Zcat> smap g\<cdot>s)) =  siterate g x"
by (metis (no_types) cfcomp1 cfcomp2 fix_eq rek2siter)

lemma sdrop2smap: "sdrop i\<cdot>(siterate g x) = smap (niterate i g)\<cdot>(siterate g x)"
by (simp add: iterate_insert siterate_drop2iter siterate_smap)



section \<open>@{term siterateBlock}\<close>

lemma siterateBlock_cont[simp]:"cont(\<lambda> h. (\<lambda>s. s \<Zcat> (h (f s))))"
  by(intro cont2cont, simp?)

lemma siterateBlock_unfold: "siterateBlock f x = x \<Zcat> siterateBlock f (f x)"
by(subst siterateBlock_def [THEN fix_eq2], auto)

lemma niterate_len[simp]: assumes "\<forall>z. #z = #(g z)" 
  shows "#((niterate i g) x) = #x"
using assms by(induction i, auto)

lemma siterateBlock_sdrop2: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" 
  shows "sdrop (y*i)\<cdot>(siterateBlock g x) = siterateBlock g ((niterate i g) x)"
apply (induction i, auto)
by (metis assms(1) assms(2) niterate_len sdrop_plus sdropl6 siterateBlock_unfold)

lemma siterateBlock_snth: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" and "#x > Fin 0" 
  shows "snth (y*i) (siterateBlock g x) = shd ((niterate i g) x)"
proof -
  have eq1: "sdrop (y*i)\<cdot>(siterateBlock g x) = siterateBlock g ((niterate i g) x)" using assms(1) assms(2) siterateBlock_sdrop2 by blast 

  have "#((niterate i g) x) > 0" by (metis Fin_02bot assms(2) assms(3) lnzero_def niterate_len)  
  hence "shd (siterateBlock g ((niterate i g) x)) = shd (((niterate i g) x))" by (metis Fin_0 minimal monofun_cfun_arg sconc_snd_empty siterateBlock_unfold snth_less snth_shd)
  thus ?thesis by (simp add: eq1 snth_def) 
qed

lemma siterateBlock_sdrop: assumes "#x = Fin y"
  shows "sdrop y\<cdot>(siterateBlock g x) = siterateBlock g (g x)"
by (metis assms sdropl6 siterateBlock_unfold)

lemma siterateBlock_eps[simp]: assumes "g \<epsilon> = \<epsilon>"
  shows "siterateBlock g \<epsilon> = \<epsilon>" 
by(simp add: siterateBlock_def assms)

lemma siterateBlock2sinf: "siterateBlock id x = sinftimes x"
by (metis id_apply rek2sinftimes siterateBlock_eps siterateBlock_unfold strict_icycle)

lemma siterBlock_inf [simp]: assumes "#s = \<infinity>"
  shows "siterateBlock f s = s"
by (metis assms sconc_fst_inf siterateBlock_unfold)

lemma siterateBlock_shd [simp]: "shd (siterateBlock g (\<up>x)) = x"
by (metis shd1 siterateBlock_unfold)

lemma smap_shd[simp]:"s \<noteq>\<epsilon> \<Longrightarrow> shd(smap g\<cdot>s) = g (shd s)"
  by(rule scases[of s];simp)

lemma siterateBlock2niter: "snth i (siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = niterate i g x" (is "snth i (?B) = ?N i")
proof -
  have f1: "#(\<up>x) = Fin 1" by simp
  have "\<forall>z. #z = #((\<lambda>s. (smap g\<cdot>s)) z)" by simp 
  hence f2: " snth (i) (siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = shd (niterate i (\<lambda>s. (smap g\<cdot>s)) (\<up>x))"
  by (metis Fin_0 Fin_Suc One_nat_def f1 lnat.con_rews lnless_def lnzero_def minimal nat_mult_1 siterateBlock_snth) 
  
  have "shd (niterate i (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = niterate i g x"
  proof (induction i)
    case 0 thus ?case by simp
  next
    case (Suc i) thus ?case
      apply simp
      apply(subst smap_shd)
      using niterate_len slen_smap  slen_zero
      apply (metis f1 lnsuc_neq_0_rev one_def one_lnat_def)
      by simp
  qed
  thus ?thesis by (simp add: f2) 
qed

lemma siterateBlock_len [simp]: "#(siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = \<infinity>"
apply (rule infI)
apply (rule allI)
apply (rule_tac x="x" in spec)
apply (induct_tac k, simp+)
apply (metis bot_is_0 lnat.con_rews siterateBlock_unfold slen_scons slen_zero)
by (metis Fin_Suc lnat.sel_rews(2) sconc_snd_empty siterateBlock_unfold slen_scons smap_scons strict_smap)

lemma siterateBlock_smap: "siterateBlock id (smap f\<cdot>x) =  smap f\<cdot>(siterateBlock id x)"
by (simp add: siterateBlock2sinf)

lemma siterateBlock2siter [simp]: "siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x) = siterate g x" 
apply (rule sinf_snt2eq, auto)
by (simp add: siterateBlock2niter snth_siter) 




end