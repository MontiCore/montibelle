theory StreamExtension
  imports stream.StreamFilter stream.StreamWhile stream.StreamScanl
begin


lemma inv_fin_suc: "inv Fin (1 + Fin x)\<star>\<up>a =  inv Fin x\<star>\<up>a \<Zcat> \<up>a "
  apply (simp add: one_lnat_def)
  using sntimes_Suc2 plus_1_eq_Suc by auto


definition sboolfilter::  "'a stream \<rightarrow> bool stream \<rightarrow> 'a stream" where
"sboolfilter \<equiv> \<Lambda> i ora.  sprojfst\<cdot>({d. snd d} \<ominus> (szip\<cdot>i\<cdot>ora))"

lemma sboolfilter_cont: "cont (\<lambda> i ora. sprojfst\<cdot>({d. snd d} \<ominus> (szip\<cdot>i\<cdot>ora)))"
  by (intro cont2cont)                                                

lemma strict_sboolfilter_fst[simp]: "sboolfilter\<cdot>\<epsilon>\<cdot>s = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma strict_sboolfilter_snd[simp]: "sboolfilter\<cdot>s\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma sboolfilter_singleton_true[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>True) = \<up>a"
  by (simp add: sboolfilter_def)
lemma sboolfilter_singleton_false[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>False) = \<epsilon>"
  by (simp add: sboolfilter_def)

lemma sboolfilter_singelton_msg_true[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>True \<Zcat> bs) =  \<up>a"
  by (simp_all add: sboolfilter_def)

lemma sboolfilter_singelton_msg_false[simp]: "sboolfilter\<cdot>(\<up>a)\<cdot>(\<up>False \<Zcat> bs) = \<epsilon>"
  by (simp_all add: sboolfilter_def)

lemma sboolfilter_sconc_true[simp]: "sboolfilter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>True \<Zcat> bs) = \<up>a \<Zcat> sboolfilter\<cdot>as\<cdot>bs"
  by (simp add: sboolfilter_def)

lemma sboolfilter_sconc_false[simp]: "sboolfilter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) = sboolfilter\<cdot>as\<cdot>bs"
  by (simp add: sboolfilter_def)

lemma slen_suc_neq: " #t < \<infinity> \<Longrightarrow> #t = #s \<Longrightarrow> lnsuc\<cdot>(#t) \<noteq> #s"
  by (simp add: order_less_imp_not_eq2)

lemma sboolfilter_len_le:
  "#(sboolfilter\<cdot>x\<cdot>ora) \<le> #x"
  apply (simp add: sboolfilter_def) 
  by (metis (no_types, lifting) min.bounded_iff slen_sfilterl1 slen_sprojfst szip_len)

lemma sboolfilter_len_eq_imp_eq: "#x = Fin k \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
proof -
  assume len_eq: "#x = #(sboolfilter\<cdot>x\<cdot>ora)" and fin: "#x = Fin k"
  show "x = sboolfilter\<cdot>x\<cdot>ora"
    using len_eq apply (induction x arbitrary: ora rule: finind2)
    using fin apply auto
    apply (case_tac ora; simp)
    apply (rename_tac s a ora b bs)
    apply (case_tac b)
    apply simp_all
    apply metis
    by (metis sboolfilter_len_le lnle_and_gt_inf(1) refl_lnle slen_suc_neq)+
qed

lemma sboolfilter_len_eq_imp_eq2: "#x \<noteq> \<infinity> \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
  using ninf2Fin sboolfilter_len_eq_imp_eq by blast

lemma sboolfilter_len_eq_imp_eq3: "#x < \<infinity> \<Longrightarrow> #x = #(sboolfilter\<cdot>x\<cdot>ora) \<Longrightarrow> x = sboolfilter\<cdot>x\<cdot>ora"
  by (meson lnat_well_h2 sboolfilter_len_eq_imp_eq)

lemma sboolfilter_refold: "(\<up>a \<Zcat> sboolfilter\<cdot>s\<cdot>ora)
      = (sboolfilter\<cdot>(\<up>a \<Zcat>s)\<cdot>(\<up>True \<Zcat>ora))"
  by simp

lemma sboolfilter_liveness_helper: "#i = \<infinity> \<longrightarrow> sprojsnd\<cdot>({d. snd d} \<ominus> szip\<cdot>i\<cdot>ora) = {True} \<ominus> ora"
proof (induction ora arbitrary:i)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (step a ora)
  then show ?case 
    apply (cases i)
     apply simp
    apply (cases a)
    by simp_all
qed

lemma sboolfilter_live [simp]:
  assumes "#y=\<infinity>"
  shows "#(sboolfilter\<cdot>y\<cdot>ora) = #({True} \<ominus> ora)"
proof -
 have a: "#(sboolfilter\<cdot>y\<cdot>ora)
            = #(sprojsnd\<cdot>({d. snd d} \<ominus> szip\<cdot>y\<cdot>ora))"
   by (simp add: sboolfilter_def slen_sprojs_eq)
  then have b: "... = #({True} \<ominus> ora)"
        using assms sboolfilter_liveness_helper by fastforce
  from a b
  show "#(sboolfilter\<cdot>y\<cdot>ora) = #({True} \<ominus> ora)" by simp
qed

lemma sboolfilter_inf_true: "sboolfilter\<cdot>y\<cdot>((\<up>True)\<^sup>\<infinity>) = y"
  apply (induction y)
  apply auto
  by (metis sboolfilter_sconc_true sinftimes_unfold)


lemma bstream_cases [case_names bottom true false]:
  assumes bottom: "x = \<bottom> \<Longrightarrow> P \<bottom>"
      and true: "\<And>as. x=(\<up>True \<Zcat> as) \<Longrightarrow> P x"
      and false: "\<And>as. x=(\<up>False \<Zcat> as) \<Longrightarrow> P x"
  shows "P x"
  using assms apply (cases x; simp)
  by (case_tac a; simp) 


definition comp  :: "(('a::cpo) \<rightarrow> ('b::cpo)) \<rightarrow> ('b \<rightarrow> ('c::cpo)) \<rightarrow> ('a \<rightarrow> 'c)" 
  where o_def: "comp = (\<Lambda> f g x. g\<cdot>(f\<cdot>x))"

abbreviation comp_syn :: "[('a::cpo) \<rightarrow> ('b::cpo), 'b \<rightarrow> ('c::cpo)] \<Rightarrow> 'a \<rightarrow> 'c"  (infixr "o" 100)
  where "f o g == comp\<cdot>f\<cdot>g"


definition mu :: "(('a stream \<times> 'b stream) \<rightarrow> ('c stream \<times> 'b stream)) \<Rightarrow> ('a stream \<rightarrow> ('c stream \<times> 'b stream))"  ("\<mu>_" [1000] 999) where
"mu f \<equiv> \<Lambda> a. fix\<cdot>(\<Lambda>(_, d). f\<cdot>(a, d))"


definition Fst :: "('a stream \<times> 'b stream) \<rightarrow> 'a stream"  where 
"Fst \<equiv> \<Lambda>(a, b). a"


definition Snd :: "('a stream \<times> 'b stream) \<rightarrow> 'b stream"  where 
"Snd \<equiv> \<Lambda>(a, b). b"


lemma comp1: "(f o g) = (\<Lambda> x. g\<cdot>(f\<cdot>x))"
by (simp add: o_def)

lemma comp2 [simp]: "(f o g)\<cdot>x = g\<cdot>(f\<cdot>x)"
by (simp add: o_def)


lemma sC_ID: "f o ID = f"
by (simp add: o_def)

lemma sC_ID2: "ID o f = f"
by (simp add: o_def)


lemma Fst_cont: "cont (\<lambda>(a, b). a)"
  by auto

lemma Fst_fst: "Fst\<cdot>(a, b) = fst (a, b)"
by (simp add: Fst_def)

lemma Fst_apply: "Fst\<cdot>(a, b) = a"
  by (simp add: Fst_def)

lemma Fst_apply2: "(\<Lambda>(a, b). a)\<cdot>(x, y) = x"
  by auto


lemma Snd_cont: "cont (\<lambda>(a, b). b)"
  by auto

lemma Snd_fst: "Snd\<cdot>(a, b) = snd (a, b)"
by (simp add: Snd_def)

lemma Snd_apply: "Snd\<cdot>(a, b) = b"
  by (simp add: Snd_def)

lemma Snd_apply2: "(\<Lambda>(a, b). b)\<cdot>(x, y) = y"
  by auto


lemma sntimes_Suc1: "(Suc n)\<star>\<up>a = \<up>a\<Zcat>(n\<star>\<up>a)" 
  apply (induction n)
apply (simp; fail)
  by (metis sntimes.simps(2))

lemma sntimes_Minus: "n>0 \<Longrightarrow> n\<star>\<up>a = \<up>a\<Zcat>((n-1)\<star>\<up>a)" 
  apply (induction n)
apply (simp; fail)
  by (metis diff_Suc_1' eq_Suc_0_numeral1 sntimes_Suc1)

lemma sconc_inj':
  assumes "\<up>a \<Zcat> u = \<up>a \<Zcat> v"
  shows   "u = v"
  using assms by (metis srt_supconc)

lemma singelton_not_empty: " x = \<up>y \<longrightarrow> x \<noteq> \<epsilon>"
  by simp

lemma sinftimes_sconc: "sinftimes (\<up>a \<Zcat> \<up>a) = sinftimes (\<up>a)"
  by (metis rek2sinftimes sconc_scons sinftimes_unfold supconc_neps2)

lemma slen_sprojs_eq2: "#(sprojfst\<cdot>x) = #(sprojsnd\<cdot>x)"
  by (simp add: slen_sprojs_eq)


lemma srcdups_slen_mono: "#(srcdups\<cdot>s) \<le> #(srcdups\<cdot>(\<up>a \<Zcat>s))"
  apply (cases s, simp_all)
  apply (rename_tac x y)
  by (case_tac "a=x", simp_all)

lemma srcdups_slen_leq: " #(srcdups\<cdot>(\<up>a \<Zcat> s)) \<le>  lnsuc\<cdot>(#(srcdups\<cdot>s))"
  using srcdups_eq[of "shd s" "srt\<cdot>s"] srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s] by fastforce

lemma slen_srcdups_adm: "adm (\<lambda>a. #(srcdups\<cdot>a) \<ge> #(srcdups\<cdot>(f\<cdot>a)))" 
  apply (subst lnle_def)
  apply (rule adm_below) 
  apply (rule cont_compose [where f="\<lambda>x.(srcdups\<cdot>(f\<cdot>x))"])
  apply simp_all
  apply (rule cont_compose [where f="\<lambda>x. srcdups\<cdot>x"])
  by simp_all

lemma srcdups_sprojsnd_swap_len_le: "#(srcdups\<cdot>(sprojsnd\<cdot>y)) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>y))"
  apply (simp add: slen_sprojsnd)
  apply (induct y, simp_all) 
   apply (simp add: slen_srcdups_adm)
  apply (case_tac a; simp)
  apply (case_tac y; simp)
  apply (case_tac ab; simp)
  apply (case_tac "b\<noteq>ba"; simp)
  apply (case_tac "aa\<noteq>ac"; simp)
  by (meson dual_order.trans less_lnsuc)


lemma srcdups_slen_filter_mono: "#(srcdups\<cdot>(sfilter A\<cdot>y)) \<le> #(srcdups\<cdot>(sfilter A\<cdot>(\<up>x) \<Zcat> sfilter A\<cdot>y))"
  by (metis dual_order.refl sconc_fst_empty sfilter_in_sup sfilter_notin_sup srcdups_slen_mono)

lemma adm_slen_srcdups_sboolfilter:
 "adm (\<lambda>a. #(srcdups\<cdot>(sboolfilter\<cdot>a\<cdot>ora)) \<le> #(srcdups\<cdot>a))" 
  apply (subst lnle_def)
  apply (rule adm_below) 
   apply (rule cont_compose [where f="\<lambda>x. srcdups\<cdot>(sboolfilter\<cdot>x\<cdot>ora)"])  
    apply simp_all
    using cont_compose_mix len_stream_cont by blast


lemma adm_slen_srcdups_sfilter:
 "adm (\<lambda>a. #(srcdups\<cdot>(A \<ominus> a)) \<le> #(srcdups\<cdot>a))" 
proof (rule admI)
  fix Y :: "nat \<Rightarrow>  'a stream"
  assume ch: "chain Y"
  assume hyp:
    "\<forall>i. #(srcdups\<cdot>(A \<ominus> (Y i))) \<le> #(srcdups\<cdot>(Y i))"

  let ?L = "\<lambda> a.  #(srcdups\<cdot>(A \<ominus> a))"
  let ?R = "\<lambda> a.  #(srcdups\<cdot>a)"

  have contL: "cont ?L" 
    using cont_compose_mix len_stream_cont by blast
  have contR: "cont ?R" 
    using cont_compose_mix len_stream_cont by blast

  from ch have L_lub: "?L (\<Squnion>i. Y i) = (\<Squnion>i. ?L (Y i))"
    using contlub_cfun_arg cont2contlubE contL by blast
  from ch have R_lub: "?R (\<Squnion>i. Y i) = (\<Squnion>i. ?R (Y i))"
    using contlub_cfun_arg cont2contlubE contR by blast

  have pw: "\<And>i. ?L(Y i) \<sqsubseteq> ?R(Y i)" using hyp by simp
  have "(\<Squnion>i. ?L(Y i)) \<le> (\<Squnion>i. ?R(Y i))"
    using ch contR ch2ch_cont contL pw lub_mono lnle_conv by blast

  thus " #(srcdups\<cdot>(A \<ominus> (\<Squnion>i. Y i))) \<le>  #(srcdups\<cdot>(\<Squnion>i. Y i))"
    by (simp add: L_lub R_lub)
qed

lemma slen_srcdups_filter_mono:
  "# (srcdups\<cdot>(A \<ominus> s)) \<le> # (srcdups\<cdot>s)"
proof (induction s)
  case adm then show ?case  by (simp add: adm_slen_srcdups_sfilter)
next
  case bottom then show ?case by simp
next
  case (step a s)
  then show ?case
    apply (cases "a \<in> A") 
     apply simp_all
    prefer 2 subgoal 
      using order.trans srcdups_slen_mono by blast
    apply (cases s, simp_all)
    apply (case_tac "a=aa", simp_all)
    apply (case_tac "aa\<in> A", simp_all)
    using srcdups_slen_leq lnsuc_lnle_emb trans_lnle by blast
qed

lemma slen_srcdups_sboolfilter_leq: 
  "#(srcdups\<cdot>(sboolfilter\<cdot>s\<cdot>ora)) \<le> #(srcdups\<cdot>(s))"
proof (induction s arbitrary:ora)
  case adm then show ?case 
    apply (rule adm_all) 
    using adm_slen_srcdups_sboolfilter by blast
next
  case bottom then show ?case by simp
next
  case (step a s)
  then show ?case
    apply (cases ora, simp_all) 
    apply (rename_tac x y)
     apply (case_tac x, simp_all)
    prefer 2
      using order.trans srcdups_slen_mono apply blast
    apply (cases s, simp_all)
    apply (rename_tac b t)
    apply (case_tac "a\<noteq>b", simp_all)
      using srcdups_slen_leq lnsuc_lnle_emb trans_lnle apply blast
      apply (case_tac y, simp)
      using neq02Suclnle slen_empty_eq srcdups_nbot supconc_neps2 apply blast
        apply (case_tac aa, simp_all)  
      apply (subst sboolfilter_refold)  
        apply blast
       apply (subst sboolfilter_refold)  
      by blast 
  qed

lemma "#(srcdups\<cdot>(sboolfilter\<cdot>(\<up>(1::nat))\<cdot>(\<up>False))) <  #(srcdups\<cdot>(\<up>1))"
  by simp
lemma "#(srcdups\<cdot>(sboolfilter\<cdot>(\<up>(1::nat))\<cdot>(\<up>True))) =  #(srcdups\<cdot>(\<up>1))"
  by simp

lemma sboolfilter_sprojsnd_distr:
  "sprojsnd\<cdot>(sboolfilter\<cdot>xs\<cdot>bs) = sboolfilter\<cdot>(sprojsnd\<cdot>xs)\<cdot>bs"
  apply (induct xs arbitrary: bs, simp_all)
  apply (case_tac a)
  apply (case_tac bs, simp_all)
  by (case_tac ab, simp_all)

lemma slen_srcdups_sprojsnd_sboolfilter_mono: 
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>s\<cdot>ora))) \<le>  #(srcdups\<cdot>(sprojsnd\<cdot>s))"
  apply (simp add: sboolfilter_sprojsnd_distr) 
  using slen_srcdups_sboolfilter_leq by blast

lemma sdropwhile_shd_neq: "y \<noteq> \<epsilon> \<Longrightarrow> shd y \<noteq> a \<Longrightarrow> y = sdropwhile (\<lambda>x. x = a)\<cdot>y"
  by (metis (full_types) sdropwhile_f shd1 streamcases)

lemma sdropwhile_shd_neq2:
  assumes "shd y \<noteq> a"
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>y = y"
  using assms 
  by (metis sdropwhile_shd_neq strict_sdropwhile)

lemma stakewhileDropwhile2: "y = stakewhile f\<cdot>y \<Zcat> (sdropwhile f\<cdot>y)"
  by (simp add: stakewhileDropwhile)

lemma dropwhile_sconc_empty:
  assumes "#sa = Fin k"
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>sa = \<epsilon> \<Longrightarrow>
         sdropwhile (\<lambda>x. x = a)\<cdot>(sa \<Zcat> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
  apply (induction sa rule: finind)
  using assms apply simp
  apply simp
  by (case_tac "a=aa"; simp)

lemma sdropwhile_eq_const_stream: "sdropwhile (\<lambda>x. x = a)\<cdot> ((\<up>a)\<^sup>\<infinity>) = \<epsilon>"
  by (metis (full_types) sdropwhile_dropstream sinf_sValues stakewhile_dom stakewhile_in_sup)

lemma sdropwhile_takewhile_neq_eps_neq_inf:
  assumes "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon>" 
  shows "#(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity>"
  using assms 
  by (metis eq_less_and_fst_inf sdropwhile_dropstream stakewhile_below stakewhile_dom)

lemma sdropwhile_neq_eps_sdrop: "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>n .sdropwhile (\<lambda>x. x = a)\<cdot>s = sdrop n\<cdot>s"
  using sdropwhile_takewhile_neq_eps_neq_inf 
  by (metis LNat.LNat.lnat.exhaust stakewhile_sdropwhilel1)

lemma sdrop_sboolfilter: "sdrop n\<cdot>s = sboolfilter\<cdot>s\<cdot>((sntimes n (\<up>False)) \<Zcat> ((\<up>True)\<^sup>\<infinity>))" 
  apply (induction n arbitrary: s; simp)
  apply (simp add: sboolfilter_inf_true)
  by (metis sboolfilter_sconc_false sdrop_forw_rt strict_sboolfilter_fst strict_sdrop surj_scons)

lemma sdrophwile_sboolfilter: "\<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sboolfilter\<cdot>s\<cdot>ora"
  by (metis sdrop_sboolfilter sdropwhile_neq_eps_sdrop strict_sboolfilter_snd)


fixrec sbool_apply :: "bool stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"sbool_apply\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"sbool_apply\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"sbool_apply\<cdot>((up\<cdot>a) && as)\<cdot>((up\<cdot>b) && bs) = 
  (if (undiscr a =  False) then (updis False) && sbool_apply\<cdot>as\<cdot>((up\<cdot>b) && bs)
                        else up\<cdot>b && sbool_apply\<cdot>as\<cdot>bs)"

lemma sbool_apply_sconc_f_t[simp]: "sbool_apply\<cdot>(\<up>True \<Zcat> xs)\<cdot>(\<up>y \<Zcat> ys) = \<up>y \<Zcat> (sbool_apply\<cdot>xs\<cdot>ys)"
  by (metis lscons_conv sbool_apply.simps(3) undiscr_Discr)

lemma sbool_apply_sconc_f_any[simp]: "sbool_apply\<cdot>(\<up>False \<Zcat> xs)\<cdot>(\<up>y \<Zcat> ys) = \<up>False \<Zcat> (sbool_apply\<cdot>xs\<cdot>(\<up>y \<Zcat> ys))"
  by (metis (no_types, lifting) lscons_conv sbool_apply.simps(3) undiscr_Discr)

lemma sboolfilter_sboolfilter: "sboolfilter\<cdot>(sboolfilter\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sboolfilter\<cdot>msg\<cdot>(sbool_apply\<cdot>ora1\<cdot>ora2 )"
  apply (induction msg arbitrary: ora1 ora2)
    apply (rule adm_all)+
    apply (rule adm_eq; simp)
    apply simp
  apply (case_tac ora1 rule: bstream_cases; simp)
  apply (case_tac ora2 rule: bstream_cases; simp)
  by (case_tac ora2 rule: bstream_cases; simp)


lemma szip_sconc_len_leq: "#ora \<le> #as \<Longrightarrow> #as = Fin k \<Longrightarrow> szip\<cdot>(as \<Zcat> bs)\<cdot>ora = szip\<cdot>as\<cdot>ora"
proof -
  assume "#ora \<le> #as" and "#as = Fin k "
  obtain n where "#ora = Fin n" and "n\<le>k"
    by (metis \<open>#as = Fin k\<close> \<open>#ora \<le> #as\<close> infI less2nat notinfI3) 
  have b1: "#(sprojfst\<cdot>(szip\<cdot>as\<cdot>ora)) = n" 
    by (metis \<open>#ora = Fin n\<close> \<open>#ora \<le> #as\<close> slen_sprojs_eq2 szip_sprojsnd)
  have "#(szip\<cdot>(as \<Zcat> bs)\<cdot>ora) = n"
    by (metis \<open>#as = Fin k\<close> \<open>#ora = Fin n\<close> \<open>#ora \<le> #as\<close> fin_le_inf less2eq min_def order_less_le sconc_snd_empty slen_conc
        szip_len)
  then have b2: "#(sprojfst\<cdot>(szip\<cdot>(as \<Zcat> bs)\<cdot>ora)) = n" 
    by (metis slen_sprojfst)
  show ?thesis using b1 b2 \<open>#as = Fin k\<close> \<open>n\<le>k \<close>  
    by (metis cont_pref_eq1I eq_slen_eq_and_less monofun_cfun_fun sconc_prefix slen_sprojfst)
qed

lemma szip_sconc_len_gr:
  assumes len_ora: "#ora > #as"
      and len_as:  "#as = Fin k"
  shows "szip\<cdot>(as \<Zcat> bs)\<cdot>ora = szip\<cdot>as\<cdot>ora \<Zcat> szip\<cdot>bs\<cdot>(sdrop k\<cdot>ora)"
  using len_ora len_as
proof (induction k arbitrary: as ora)
  case 0
  then show ?case
  proof -
    from `#as = Fin 0` have "as = \<epsilon>"
      by (cases as) auto
    then show ?thesis by simp
  qed
next
  case (Suc k)
  then show ?case
  proof -
    obtain x xs where as_def: "as = x && xs"
      by (metis lscons_conv stream.con_rews(2) surj_scons)
    from Suc.prems as_def have "#xs = Fin k"
      by (metis Fin_0 lnat_fin4 order_less_le slen_empty_eq srt_decrements_length stream.con_rews(2) stream.sel_rews(5) zero_less_Suc)
     from Suc.prems as_def have "ora \<noteq> \<epsilon>"
      by (cases ora) auto
    then obtain y ys where ora_def: "ora = y && ys"
      by (metis lscons_conv  surj_scons)

    from Suc.prems as_def ora_def have "#ys > #xs"
      by (metis \<open>#xs = Fin k\<close> \<open>ora \<noteq> \<epsilon>\<close> linorder_not_less slen_rt_ile_eq stream.con_rews(2) stream.sel_rews(5))   

    have IH: "szip\<cdot>(xs \<Zcat> bs)\<cdot>ys = szip\<cdot>xs\<cdot>ys \<Zcat> szip\<cdot>bs\<cdot>(sdrop k\<cdot>ys)"
      using Suc.IH[of xs ys] `#ys > #xs` `#xs = Fin k` by simp
    show ?thesis
      unfolding as_def ora_def
      using IH
    proof -
      have f1: "srt\<cdot>(y && ys) = ys"
        using \<open>ora \<noteq> \<epsilon>\<close> ora_def stream.con_rews(2) stream.sel_rews(5) by blast
      have f2: "szip\<cdot>((x && xs) \<Zcat> bs)\<cdot>(y && ys) = \<up>(shd (x && xs), shd (y && ys)) \<Zcat> szip\<cdot>(xs \<Zcat> bs)\<cdot>ys"
        by (metis (no_types) Fin_0 Suc.prems(2) Suc_neq_Zero \<open>ora \<noteq> \<epsilon>\<close> as_def assoc_sconc ora_def slen_empty_eq stream.con_rews(2) stream.sel_rews(5) surj_scons szip_scons)
      have "\<up>(shd (x && xs), shd (y && ys)) \<Zcat> szip\<cdot>xs\<cdot>ys = szip\<cdot>(x && xs)\<cdot>(y && ys)"
        by (metis (no_types) Fin_0 Suc.prems(2) Suc_neq_Zero \<open>ora \<noteq> \<epsilon>\<close> as_def ora_def slen_empty_eq stream.con_rews(2) stream.sel_rews(5) surj_scons szip_scons)
      then show "szip\<cdot>((x && xs) \<Zcat> bs)\<cdot>(y && ys) = szip\<cdot>(x && xs)\<cdot> (y && ys) \<Zcat> szip\<cdot>bs\<cdot>(sdrop (Suc k)\<cdot>(y && ys))"
        using f2 f1 by (metis (no_types) IH assoc_sconc sdrop_forw_rt)
    qed
  qed
qed

lemma sprojfst_sconc: "sprojfst\<cdot>as \<Zcat> sprojfst\<cdot>bs = sprojfst\<cdot>(as \<Zcat> bs)"
  by (simp add: smap_split sprojfst_def)

lemma sboolfilter_sconc: "\<exists>ora2. sboolfilter\<cdot>(as \<Zcat> bs)\<cdot>ora = sboolfilter\<cdot>as\<cdot>ora \<Zcat> sboolfilter\<cdot>bs\<cdot>ora2"
proof (cases "#as = \<infinity>")
  case True
  then show ?thesis   
    apply (simp add: sboolfilter_def)
    by (metis  sconc_snd_empty strict_sfilter strict_sprojfst strict_szip_snd)
next
  case False
  obtain k where "#as = Fin k" 
    using False infI by auto
  then show ?thesis 
    apply (cases "#ora \<le> #as")
    apply (simp_all add: sboolfilter_def)
    apply (metis szip_sconc_len_leq sconc_snd_empty strict_sfilter strict_sprojfst strict_szip_snd)
    apply (simp add: szip_sconc_len_gr add_sfilter sprojfst_sconc) 
    by blast
qed

lemma sdropwhile_filter_stakewhile_empty: "sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>"
  apply (induction s arbitrary:ora)
    apply (rule adm_all)
    apply (rule adm_eq; simp)
    apply simp
  apply (case_tac "a=aa"; simp)
  by (case_tac ora rule: bstream_cases; simp)

lemma srcdups_neq2:
  assumes "a \<noteq> shd s" 
  shows "srcdups\<cdot>(\<up>a \<Zcat> s) = \<up>a \<Zcat> srcdups\<cdot>s" 
  using assms 
  by (metis sconc_snd_empty srcdups_neq srcdups_sup strict_srcdups surj_scons)

lemma bstream_p_t_unfold: "\<exists>ora1. P (\<up>True\<Zcat>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto

lemma bstream_p_f_unfold: "\<exists>ora1. P (\<up>False \<Zcat> ora1) \<Longrightarrow> \<exists>ora2. P ora2"
by auto   

lemma sdropwhile_sboolfilter_ex:
  shows "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>y\<cdot>ora) = sboolfilter\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>y)\<cdot>ora2"
proof -
  let ?P = "\<lambda>x. x = a"
  have decomp: "y = stakewhile ?P\<cdot>y \<Zcat> sdropwhile ?P\<cdot>y"
    by (simp add: stakewhileDropwhile)
  obtain ora2 where filt_decomp:
    "sboolfilter\<cdot>(stakewhile ?P\<cdot>y \<Zcat> sdropwhile ?P\<cdot>y)\<cdot>ora
     = sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora  \<Zcat> sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2"
    using sboolfilter_sconc by blast
  hence filt_y:
    "sboolfilter\<cdot>y\<cdot>ora  = sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora  \<Zcat> sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2"
    using decomp by simp
  have drop_take_empty:
    "sdropwhile ?P\<cdot>(sboolfilter\<cdot>(stakewhile ?P\<cdot>y)\<cdot>ora) = \<epsilon>"
    using sdropwhile_filter_stakewhile_empty[of a y ora] by simp
  have lhs:
    "sdropwhile ?P\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
     = sdropwhile ?P\<cdot>(sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2)"
    using filt_y drop_take_empty 
    by (metis dropwhile_sconc_empty lncases notinfI3 sboolfilter_len_le sconc_snd_empty sdropwhile_takewhile_neq_eps_neq_inf
        strict_sboolfilter_fst strict_sdropwhile)
  obtain ora3 where lhs2: "sdropwhile ?P\<cdot>(sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>ora2) = sboolfilter\<cdot>(sdropwhile ?P\<cdot>y)\<cdot>(sbool_apply\<cdot>ora2\<cdot>ora3)"
    using sdrophwile_sboolfilter by (metis sboolfilter_sboolfilter)
  then show ?thesis
    by (metis lhs2 lhs)
qed

lemma srcdups_sboolfilter_shd: "(sboolfilter\<cdot>as\<cdot>bs) \<noteq> \<epsilon> \<Longrightarrow> shd (sboolfilter\<cdot>as\<cdot>bs) = a 
  \<Longrightarrow> srcdups\<cdot>(sboolfilter\<cdot>as\<cdot>bs) = \<up>a \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>as\<cdot>bs))"
  by (metis srcdups_eq srcdups_step surj_scons)

lemma srcdups_sboolfilter_ex:
  assumes len: "#(srcdups\<cdot>y) = Fin n"  shows "\<exists>ora2. srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora) = sboolfilter\<cdot>(srcdups\<cdot>y)\<cdot>ora2"
  using len
proof (induction n arbitrary: y ora)
  case 0
  then show ?case 
    by (metis Fin_0 slen_empty_eq srcdups_nbot strict_sboolfilter_fst)
next
  case (Suc n)
  obtain a ys where
    y_ne: "y \<noteq> \<epsilon>" and  a_def: "a = shd y" and
    srcdups_y: "srcdups\<cdot>y = \<up>a \<Zcat> srcdups\<cdot>ys" and
    ys_def: "ys = sdropwhile (\<lambda>x. x = a)\<cdot>y" and
    len_ys: "#(srcdups\<cdot>ys) = Fin n"
    by (metis (no_types, lifting) ext Fin_0 Suc.prems lnat_fin4 old.nat.distinct(1) slen_scons slen_zero srcdups_eq srcdups_step strict_srcdups
        surj_scons)
  obtain ora1 where dropwhile_filter_ys:
   "sdropwhile (\<lambda>x. x = a)\<cdot>(sboolfilter\<cdot>y\<cdot>ora)  = sboolfilter\<cdot>ys\<cdot>ora1"
    using ys_def sdropwhile_sboolfilter_ex by blast
  obtain ora2 where IH_tail:
    "srcdups\<cdot>(sboolfilter\<cdot>ys\<cdot>ora1)  = sboolfilter\<cdot>(srcdups\<cdot>ys)\<cdot>ora2"
    using Suc.IH len_ys by blast
  show ?case
  proof (cases "sboolfilter\<cdot>y\<cdot>ora = \<epsilon>")
    case True
    then show ?thesis 
      by (metis strict_sboolfilter_snd strict_srcdups)
  next
    case False
    define a' where "a' = shd (sboolfilter\<cdot>y\<cdot>ora)"
    have srcdups_filtered_unfold:
      "srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
       = \<up>a' \<Zcat> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a')\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
      using a'_def False srcdups_sboolfilter_shd[of "y" "ora" a'] by blast
    have "\<exists>ora2. srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)
                = sboolfilter\<cdot>(srcdups\<cdot>y)\<cdot>ora2" 
      using srcdups_filtered_unfold dropwhile_filter_ys IH_tail  srcdups_y  
      by (metis a'_def sboolfilter_sconc_false sboolfilter_sconc_true sdropwhile_shd_neq2)
    then show ?thesis by blast
  qed
qed

lemma srcdups_sboolfilter_id_if_fin_len_eq:
  assumes a1: "#(srcdups\<cdot>y) < \<infinity>"
      and a2: "#(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  shows "srcdups\<cdot>y = srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora)"
  using assms 
  by (metis srcdups_sboolfilter_ex lnat_well_h2 sboolfilter_len_eq_imp_eq3)

lemma srcdups_sboolfilter_len_eq_imp: "#(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>y)) \<Longrightarrow>
   #(srcdups\<cdot>(sprojsnd\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
  #(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis linorder_not_less order_le_imp_less_or_eq slen_sprojfst slen_sprojsnd slen_srcdups_sboolfilter_leq
      srcdups_sprojsnd_swap_len_le)

lemma srcdups_sboolfilter_len_eq_imp2: "
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
  #(srcdups\<cdot>y) = #(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis order_antisym_conv slen_sprojs_eq2 slen_sprojsnd slen_srcdups_sboolfilter_leq
      srcdups_sprojsnd_swap_len_le)

lemma sprojfst_srcdups_sboolfilter_id_if_fin_len_eq:
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<noteq> \<infinity> \<Longrightarrow>
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
   sprojfst\<cdot>(srcdups\<cdot>y) = sprojfst\<cdot>(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  by (metis inf_ub order_le_imp_less_or_eq slen_sprojfst srcdups_sboolfilter_id_if_fin_len_eq
      srcdups_sboolfilter_len_eq_imp2)

lemma sprojfst_srcdups_sboolfilter_id_if_fin_len_eq2:
  "#(srcdups\<cdot>y) < \<infinity> \<Longrightarrow>
   #(sprojfst\<cdot>(srcdups\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>y)) \<Longrightarrow>
   #(srcdups\<cdot>(sprojsnd\<cdot>y)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sboolfilter\<cdot>y\<cdot>ora))) \<Longrightarrow>
   sprojfst\<cdot>(srcdups\<cdot>y) = sprojfst\<cdot>(srcdups\<cdot>(sboolfilter\<cdot>y\<cdot>ora))"
  using srcdups_sboolfilter_len_eq_imp srcdups_sboolfilter_id_if_fin_len_eq by metis


lemma svalues_sfilter_in: "a \<in> sValues\<cdot>(A \<ominus> s) \<longrightarrow> a \<in> sValues\<cdot>s"
  by simp

lemma stake_shd_srt: "Fin n < #s  \<Longrightarrow> stake (Suc n)\<cdot>s = \<up>(shd s) \<Zcat> stake n\<cdot>(srt\<cdot>s)"
proof (induction n arbitrary: s)
  case 0
  then show ?case 
    by (cases s; simp)
next
  case (Suc n)
  then show ?case 
    by (cases s; simp)
qed

lemma sfilter_stake_exists:
  shows "\<exists>k. sfilter X\<cdot>(stake n\<cdot>s) = stake k\<cdot>(sfilter X\<cdot>s)"
proof (cases "Fin n < #s")
  case True
  then show ?thesis 
  proof (induction n arbitrary: s)
  case 0
  then show ?case
    by (metis Rep_cfun_strict1 stream.take_0 strict_sfilter)
  next
  case (Suc n)
  from Suc.IH[of "srt\<cdot>s"] obtain k
    where IH: " Fin n < #s \<Longrightarrow> sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s)) = stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
    by (metis Suc.prems empty_is_shortest lnat_fin8 srt_decrements_length)
    show ?case
  proof (cases "shd s \<in> X")
    case True
    have "sfilter X\<cdot>(stake (Suc n)\<cdot>s)
        = sfilter X\<cdot>(\<up>(shd s) \<Zcat> stake n\<cdot>(srt\<cdot>s))"
      using stake_shd_srt 
      by (metis Suc.prems convert_inductive_asm) 
      also from True have "... = \<up>(shd s) \<Zcat> sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s))"
      by simp
    also from IH have "... = \<up>(shd s) \<Zcat> stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
      by (metis Suc.prems convert_inductive_asm)
      also have "sfilter X\<cdot>s = \<up>(shd s) \<Zcat> sfilter X\<cdot>(srt\<cdot>s)"
      using True 
      by (metis Suc.prems sfilter_in stake_shd_srt stream.take_strict supconc_neps2 surj_scons)
      hence "\<up>(shd s) \<Zcat> stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))
         = stake (Suc k)\<cdot>(sfilter X\<cdot>s)"
      by simp
    finally show ?thesis
      by (rule exI[of _ "Suc k"])
  next
    case False
    have "sfilter X\<cdot>(stake (Suc n)\<cdot>s)
        = sfilter X\<cdot>(\<up>(shd s) \<Zcat> stake n\<cdot>(srt\<cdot>s))"
      using stake_shd_srt 
      by (metis Suc.prems convert_inductive_asm) 
    also from False have "... = sfilter X\<cdot>(stake n\<cdot>(srt\<cdot>s))"
      by simp
    also from IH have "... = stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s))"
      by (metis Suc.prems convert_inductive_asm)
    also from False have "sfilter X\<cdot>s = sfilter X\<cdot>(srt\<cdot>s)"
      by (metis Suc.prems sfilter_nin stake_shd_srt stream.take_strict supconc_neps2 surj_scons)
    hence "stake k\<cdot>(sfilter X\<cdot>(srt\<cdot>s)) = stake k\<cdot>(sfilter X\<cdot>s)"
      by simp
    finally show ?thesis
      by (rule exI[of _ k])
  qed
qed
next
  case False
  have "sfilter X\<cdot>(stake n\<cdot>s) = sfilter X\<cdot>s" 
    using False
    by (metis fin2stake_lemma fin_le_inf less2nat linorder_le_less_linear ninf2Fin)  
  then show ?thesis 
    by (metis False fin2stake fin_le_inf ninf2Fin sfilterl4)
qed



end
