theory hwl_core_ext
  imports
    TsynStreamExtension
begin



lemma tsyn2ustream_ne_eps: "#(tsyn2ustream\<cdot>s) \<noteq> #s \<Longrightarrow> Eps \<in> sValues\<cdot>s"
  apply(simp add: tsyn2ustream_def)
  by (metis (mono_tags, lifting) Collect_mono mem_Collect_eq not_Eps_eq sValues_def2 sfilter_sValuesl3)

lemma
  tsyn2ustream_eq_no_eps:
  assumes"#(tsyn2ustream\<cdot>s) = #s"
    and "#s \<noteq> \<infinity>"
  shows "(Eps \<notin> sValues\<cdot>s)"
  apply(insert assms)
  apply(induct s, simp_all add: tsyn2ustream_def)
   apply(simp add: adm_def)
   apply(auto)
  using inf_chainl4 l42 apply force
   apply (metis less_lnsuc lnle_and_gt_inf(1) order_antisym_conv slen_sfilterl1)
  by (metis (no_types, lifting) LNat.lnat.sel_rews(2) lnle_and_gt_inf(2) sfilter_in sfilter_nin slen_scons slen_sfilterl1)

lemma tsyn2ustream_no_eps_eq: "Eps \<notin> sValues\<cdot>s \<Longrightarrow> #(tsyn2ustream\<cdot>s) = #s"
  apply(simp add: tsyn2ustream_def)
  apply(insert sfilter_sValuesl3[of s])
  by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono not_Eps_eq)

lemma map_tsyn_values1: "\<sim> \<notin> sValues\<cdot>(smap (map_tsyn f)\<cdot>s) \<Longrightarrow> \<sim> \<notin> sValues\<cdot>s"
  and map_tsyn_values2: "\<sim> \<notin> sValues\<cdot>s \<Longrightarrow> \<sim> \<notin> sValues\<cdot>(smap (map_tsyn f)\<cdot>s)"
  by (simp add: image_iff smap_sValues)+


lemma tsyn2ustream_conc: "#a \<noteq> \<infinity> \<Longrightarrow> tsyn2ustream\<cdot>(a \<Zcat> s) = tsyn2ustream\<cdot>a \<Zcat> tsyn2ustream\<cdot>s"
  by (simp add: tsyn2ustream_def add_sfilter2 order_less_le smap_split)

lemma
  sfilter_smap_len:
  assumes "\<forall>a :: 'a::{countable}. ((f a) \<in> (B :: 'b::{countable} set) \<longleftrightarrow> a \<in> A)"
  shows "#(A \<ominus> s) = #(B \<ominus> (smap f)\<cdot>s)"
  apply(induct s, simp_all)
   apply(rule adm_eq)
    apply(simp add: cont_compose_mix)
   apply(rule cont_compose_mix)+
   apply(simp)
  by(case_tac "a \<in> A", simp_all add: assms)

lemma tsyn2ustream_len: "#(tsyn2ustream\<cdot>s) = #(tsyn2ustream\<cdot>(smap (map_tsyn f)\<cdot>s))"
  by (simp add: tsyn2ustream_def sfilter_smap_len)

lemma tsynLen_smap_map_tsyn: " #\<^sub>-s = #\<^sub>-(smap (map_tsyn f)\<cdot>s)"
  apply(simp add: tsynLen_def)
  apply(subst beta_cfun, simp add: len_stream_def)+
  by(simp add: tsyn2ustream_len)


lemma
  szip_sfilter_infty_len:
  assumes "#(M \<ominus> ora) = \<infinity>"
    and "#s = \<infinity>"
  shows "#(szip\<cdot>ora\<cdot>s) = \<infinity>"
  apply(insert assms, simp)
  using sfilterl4 by blast

lemma sfilter_tpl_sprojfst: "sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> tpls) = M \<ominus> (sprojfst\<cdot>tpls)"
  apply(induction tpls, simp_all)
  by (metis (no_types, lifting) Product_Type.old.prod.exhaust case_prod_conv mem_Collect_eq sfilter_in sfilter_nin sprojfst_scons)

lemma sfilter_szip_sprojfst: "#s \<ge> #ora \<Longrightarrow> sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> szip\<cdot>ora\<cdot>s) = M \<ominus> ora"
proof -
  assume assms: "#s \<ge> #ora"
  have belowness: "sprojfst\<cdot>(szip\<cdot>ora\<cdot>s) \<sqsubseteq> ora"
    by(rule sprojfst_szip_below[of ora s])
  then have equallity: "sprojfst\<cdot>(szip\<cdot>ora\<cdot>s) = ora"
    by (simp add: assms eq_slen_eq_and_less slen_sprojfst)
  
  have "sprojfst\<cdot>({(m, x) . m \<in> M} \<ominus> (szip\<cdot>ora\<cdot>s)) = M \<ominus> (sprojfst\<cdot>(szip\<cdot>ora\<cdot>s))"
    by (rule sfilter_tpl_sprojfst)

  thus ?thesis
    using equallity by argo
qed


lemma Abs_cfun_id_x: "Abs_cfun id\<cdot>x = x"
  using eq_id_iff by fastforce



lemma tsynZip_nonempty_insert: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> (tsynZip\<cdot>z\<cdot>s) = (
  if (shd z) = Eps then \<up>Eps \<Zcat> tsynZip\<cdot>(srt\<cdot>z)\<cdot>s
  else \<up>(TSynMsg ((invMsg (shd z)), (shd s))) \<Zcat> tsynZip\<cdot>(srt\<cdot>z)\<cdot>(srt\<cdot>s) 
)"
  apply(auto)
  by (metis TsynStream.tsynZip.simps(1,2) surj_scons tsynzip_sconc_msg tsynzip_sconc_Eps)+

lemma tsynZip_nonempty_shd: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (tsynZip\<cdot>z\<cdot>s) = (
  if (shd z) = Eps then Eps
  else TSynMsg ((invMsg (shd z)), (shd s))
)"
  by (metis shd1 tsynZip_nonempty_insert)

lemma tsynZip_nonempty_srt: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> srt\<cdot>(tsynZip\<cdot>z\<cdot>s) \<in> {tsynZip\<cdot>(srt\<cdot>z)\<cdot>s, tsynZip\<cdot>(srt\<cdot>z)\<cdot>(srt\<cdot>s)}"
  apply(subst tsynZip_nonempty_insert)
  by auto

lemma tsynZip_nonempty_shd_not_eps: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> shd (tsynZip\<cdot>z\<cdot>s) \<noteq> \<sim> \<Longrightarrow> shd z \<noteq> \<sim>"
  apply(simp add: tsynZip_nonempty_shd)
  by (metis not_Eps_eq)

lemma tsynlen_inf_srt_ne: "#\<^sub>-s = \<infinity> \<Longrightarrow> srt\<cdot>s \<noteq> \<epsilon>"
  apply(simp add: sdrop_def tsynlen_insert tsyn2ustream_def)
  by (metis sfilter_srt_sinf slen_zero strict_sfilter tsynlen_inf_nbot tsynlen_strict)

lemma tsynlen_inf_drop_ne: "#\<^sub>-s = \<infinity> \<Longrightarrow> sdrop i\<cdot>s \<noteq> \<epsilon>"
  apply(induction i, simp_all add: tsynlen_inf_nbot)
  apply(simp add: sdrop_def)
  by (metis Inf'_neq_0 fair_sdrop inf_less_eq sdrop_back_rt sdrop_def slen_zero tsynlen_slen)

lemma tsynZip_sdrop_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity> \<Longrightarrow> \<exists>j \<le> i. sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>(sdrop j\<cdot>s)"
  apply(induction i, simp_all)
  apply(simp add: sdrop_def)
proof -
  fix ia :: nat
  assume a1: "\<exists>j\<le>ia. iterate ia\<cdot>srt\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(iterate ia\<cdot>srt\<cdot>z)\<cdot> (iterate j\<cdot>srt\<cdot>s)"
  assume "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
  then have "\<infinity> = #(tsynZip\<cdot>z\<cdot>s)"
    by (metis (no_types) antisym inf_ub tsynlen_slen)
  then show "\<exists>n\<le>Suc ia. srt\<cdot>(iterate ia\<cdot>srt\<cdot>(tsynZip\<cdot>z\<cdot>s)) = tsynZip\<cdot>(srt\<cdot>(iterate ia\<cdot>srt\<cdot>z))\<cdot> (iterate n\<cdot>srt\<cdot>s)"
    using a1 by (metis (no_types) Inf'_neq_0 Suc_leD Suc_le_mono emptyE fair_sdrop insertE only_empty_has_length_0 sdrop_back_rt sdrop_def tsynZip_nonempty_srt)
qed

lemma tsynApplyElem_def2: "tsynApplyElem = map_tsyn"
  apply (subgoal_tac "\<And> f c. tsynApplyElem f c = map_tsyn f c")
  apply auto
  by(case_tac c, simp_all)

lemma tsynMap_def2: "tsynMap f = smap (map_tsyn f)"
  by(simp add: tsynMap_def tsynApplyElem_def2)

lemma
  SOME_inj_f_eq_insert:
  assumes "inj (Rep_cfun f)"
  shows "(SOME x. (\<lambda>c. f\<cdot>x) = (\<lambda>c. f\<cdot>y)) = y"
proof-
  have "(SOME x. (\<lambda>c. f\<cdot>x) = (\<lambda>c. f\<cdot>y)) = (SOME x. x = y)"
    by (metis assms inj_def)
  thus ?thesis
    by simp
qed



lemma tsynLen_TSynMsg_sfilter: "#\<^sub>-((TSynMsg ` A) \<ominus> s) = #((TSynMsg ` A) \<ominus> s)"
  apply(simp add: tsynlen_insert tsyn2ustream_def)
  apply(subgoal_tac "{e::'a tsyn. \<exists>y::'a. e = TSynMsg y} \<inter> TSynMsg ` A = TSynMsg ` A")
   apply(simp)
  by(blast)

lemma tsynLen_tsynFilter1: "#\<^sub>-(A \<ominus>\<^sub>- s) =  #((TSynMsg ` A) \<ominus> s)"
  apply(simp add: tsynlen_insert tsyn2ustream_def tsynFilter_def)
  apply(rule sfilter_smap_len[symmetric])
  apply(auto)
  apply(case_tac "a = Eps", simp_all)
  by (metis TSynDatatype.tsyn.simps(3) TsynStream.tsynFilterElem.simps(2) rev_image_eqI)

lemma tsynLen_tsynFilter2: "#\<^sub>-(A \<ominus>\<^sub>- s) =  #\<^sub>-((TSynMsg ` A) \<ominus> s)"
  by(simp add: tsynLen_TSynMsg_sfilter tsynLen_tsynFilter1)

lemma "#\<^sub>-s = \<infinity> \<Longrightarrow> #({e . e \<noteq> Eps} \<ominus> s) = \<infinity>"
  by (metis (no_types, lifting) ext Collect_mono Int_def mem_Collect_eq sValues_sfilter sfilter_sValuesl3 tsynEps_tsynEps2slen_infinite_msg tsynabs_insert
      tsynlen_insert)

lemmas sfilter_smap_len_symmetric = sfilter_smap_len[symmetric]


lemma TSynMsg_image_eq: "TSynMsg ` A = {x . (\<exists>y. x = TSynMsg y) \<and> inv TSynMsg x \<in> A}"
  by auto


lemma tsynZip_sfilter_snth: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = \<infinity> \<Longrightarrow> x = TSynMsg (xa, y) \<Longrightarrow> snth i (tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = TSynMsg (xa, y) \<Longrightarrow> y \<in> A"
  apply(case_tac "x")
   apply auto
  apply(subgoal_tac "tsynZip\<cdot>z\<cdot>(A \<ominus> s) \<noteq> \<epsilon>")
   defer
  using tsynlen_inf_nbot apply blast
  apply(subgoal_tac "\<exists>j \<le> i. sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>(sdrop j\<cdot>(A \<ominus> s))")
   defer
  using tsynZip_sdrop_inf apply blast
  apply(simp add: snth_def)
  by (smt Int_iff Product_Type.prod.simps(1) TSynDatatype.inverseMsg.simps(2) TSynDatatype.tsyn.simps(3) TsynStream.tsynZip.simps(2) drop_not_all fin_le_inf inf_less_eq
      rek2sinftimes sValues_sfilter sconc_snd_empty sdrop_back_rt sdrop_sValues sfilter_nin sfilter_sValuesl3 sfilter_sinftimes_nin supconc_neps surj_scons tsynZip_nonempty_shd
      tsynlen_slen)

lemma tsynZip_sfilter_sValues: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) = \<infinity> \<Longrightarrow> sValues\<cdot>(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) \<subseteq> {x. x = Eps \<or> inv TSynMsg x \<in> {(x, y). y \<in> A}}"
  apply(simp add: sValues_def)
  apply(subst beta_cfun, rule sValues_cont)
  apply(simp add: tsynEps_tsynEps2slen_infinite_msg)
  apply auto
  by (simp add: tsynZip_sfilter_snth)

lemma tsynZip_helper_todo: "#\<^sub>-(tsynZip\<cdot>z\<cdot>(A \<ominus> s)) =  #({x . x \<noteq> \<sim> } \<ominus> tsynZip\<cdot>z\<cdot>(A \<ominus> s))"
  apply(simp only: tsynlen_insert)
  by (simp add: tsynabs_insert)



lemma tsynZip_eps_impl_cp: "s \<noteq> \<epsilon> \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon>"
proof -
  assume sne: "s \<noteq> \<epsilon>"
    and zne: "z \<noteq> \<epsilon>"
  obtain a as b bs where
    zeq: "z = up\<cdot>a && as"
and seq: "s = up\<cdot>b && bs"
    by (metis scases' sne upE zne)

  have alteq: "tsynZip\<cdot>z\<cdot>s = tsynZip\<cdot>(up\<cdot>a && as)\<cdot>(up\<cdot>b && bs)"
    by(simp only: seq zeq)
  show ?thesis
    by(simp add: alteq tsynZip.simps(3))
qed

lemma tsynZip_eps_impl: "tsynZip\<cdot>z\<cdot>s = \<epsilon> \<Longrightarrow> z = \<epsilon> \<or> s = \<epsilon>"
  using tsynZip_eps_impl_cp by blast

lemma
  tsynZip_snth_not_eps:
  assumes "#s = \<infinity>"
  and "snth j z \<noteq> Eps"
  and "#\<^sub>-z = \<infinity>"
shows "snth j (tsynZip\<cdot>z\<cdot>s) \<noteq> Eps"
  apply(subgoal_tac "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>")
  defer
   apply (simp add: assms(1,3) tsynzip_tsynlen)
  apply(simp add: snth_def)
  apply(insert tsynZip_sdrop_inf[of z s j])
  apply auto
  by (metis assms(2) snth_def tsynZip_nonempty_shd tsynlen_inf_drop_ne)

lemma no_msg_before_least: 
  assumes "k = (LEAST k. snth k z \<noteq> Eps)"
  shows "\<forall>i < k. snth i z = Eps"
  using assms not_less_Least by blast

lemma
  tsynZip_until_first_msg_only_eps:
  assumes "#s = \<infinity>"
  and "#\<^sub>-z = \<infinity>"
  and "k = (LEAST k. snth k z \<noteq> Eps)"
shows "i < k \<Longrightarrow> snth i (tsynZip\<cdot>z\<cdot>s) = Eps"
proof(induction i)
  case 0
  assume kg0: "0 < k"
  have zip_tslen_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
    by (simp add: assms(1,2) tsynzip_tsynlen)

  have neps: "tsynZip\<cdot>z\<cdot>s \<noteq> \<epsilon>"
    using zip_tslen_inf by force

  show ?case
    apply(simp add: tsynZip_nonempty_insert[OF neps])
    apply(subst snth_shd[symmetric])
    using assms(3) kg0 not_less_Least by blast
next
  case (Suc i)
  assume kgsi: "Suc i < k"

  have zip_tslen_inf: "#\<^sub>-(tsynZip\<cdot>z\<cdot>s) = \<infinity>"
    by (simp add: assms(1,2) tsynzip_tsynlen)

  show ?case
    by (metis no_msg_before_least[OF assms(3)] kgsi snth_def tsynZip_nonempty_shd tsynZip_sdrop_inf tsynlen_inf_drop_ne zip_tslen_inf)
qed

lemma
  tsynZip_until_first_msg_no_consumption:
  assumes "#s = \<infinity>"
  and "#\<^sub>-z = \<infinity>"
  and "k = (LEAST k. snth k z \<noteq> Eps)"
shows "i \<le> k \<Longrightarrow> sdrop i\<cdot>(tsynZip\<cdot>z\<cdot>s) = tsynZip\<cdot>(sdrop i\<cdot>z)\<cdot>s"
  apply(induction i)
   apply(simp add: assms)+
  apply(subst tsynZip_nonempty_insert)
   apply (simp add: assms(1,2) tsynlen_inf_nbot tsynzip_tsynlen)
  apply(insert no_msg_before_least[OF assms(3)])
  by (smt Suc_le_eq TSynDatatype.tsyn.exhaust assms(1,2,3) not_less_Least sdrop_back_rt snth_def srt_supconc tsynZip_nonempty_insert tsynlen_inf_drop_ne
      tsynlen_inf_nbot tsynzip_tsynlen)

lemma tsynFst_def2: "tsynFst = map_tsyn fst"
  by(rule ext, case_tac x, auto)

lemma tsynSnd_def2: "tsynSnd = map_tsyn snd"
  by(rule ext, case_tac x, auto)


end
