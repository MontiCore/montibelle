
theory TimedStreamFunction
imports StreamWhile StreamAltMap
begin

definition tsrt::"'a::{tlen,countable} stream \<rightarrow> 'a stream"where
"tsrt = srtdw (\<lambda>e. #\<^sub>\<surd>e = 0)"

lemma tsrt_def_2: "tsrt = srt oo sdropwhile (\<lambda>e. #\<^sub>\<surd>e = 0)"
  by (simp add: tsrt_def srtdw_def oo_def)

lemma shows tsrt_msg [simp]:"#\<^sub>\<surd>h = 0 \<Longrightarrow> tsrt\<cdot>(\<up>h \<Zcat> s) = tsrt\<cdot>s"
  and tsrt_tick[simp]:"#\<^sub>\<surd>h \<noteq> 0 \<Longrightarrow> tsrt\<cdot>(\<up>h \<Zcat> s) = s"
  and tsrt_eps[simp]: "tsrt\<cdot>\<epsilon> = \<epsilon>"
  and tsrt_allmsg[simp]: "(\<forall>e \<in> sValues\<cdot>s. #\<^sub>\<surd>e = 0) \<Longrightarrow> tsrt\<cdot>s = \<epsilon>"
  apply (simp_all add: tsrt_def)
  apply (induction s)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union; fail)
   apply (simp; fail)
  by simp
  

lemma tsrt_svalues:
  "sValues\<cdot>(tsrt\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply (induction s)
  apply (subst less_set_def[symmetric])
  apply (rule adm_below)
  apply (intro cont2cont)+
  apply (simp; fail)
  apply (subgoal_tac "tsrt\<cdot>(\<up>a \<Zcat> s) = tsrt\<cdot>s \<or> tsrt\<cdot>(\<up>a \<Zcat> s) = s")
  apply (simp add: subset_insertI2)
  apply (metis subset_insertI subset_insertI2) 
  using tsrt_msg tsrt_tick by fastforce

lemma tsrt_tlenleq[simp]:"#\<^sub>\<surd>(tsrt\<cdot>s) \<le> #\<^sub>\<surd>s"
  apply (induction s,simp_all)
  apply (subst lnle_def)
  apply (rule adm_below)
    apply (simp add: cont_compose; fail)
   apply(simp; fail)
  by (metis tsrt_msg tsrt_tick add.commute add.right_neutral dual_order.refl lessequal_addition lnmin_smaller_addition strict_lnmin_snd)

lemma tsrt_srt_len:
  "#(tsrt\<cdot>s) \<le> #(srt\<cdot>s)"
  apply (induction s)
  apply (subst lnle_def)
  apply (rule adm_below)
  apply (rule cont_compose [where f="\<lambda>x. tsrt\<cdot>x"])
  apply (intro cont2cont)+
  apply (rule cont_compose [where f="\<lambda>x. srt\<cdot>x"])
  apply simp_all
  by (metis Orderings.order_eq_iff tsrt_msg tsrt_tick tsrt_eps dual_order.trans less_lnsuc srt_decrements_length)

lemma tsrt_srt_tlen:
  "#\<^sub>\<surd>(tsrt\<cdot>s) \<le> #\<^sub>\<surd>(srt\<cdot>s)"
  apply (induction s)
  apply (subst lnle_def)
  apply (rule adm_below)
  apply (rule cont_compose [where f="\<lambda>x. tsrt\<cdot>x"], simp_all)
  apply (rule cont_compose [where f="\<lambda>x. srt\<cdot>x"], simp_all)
  by (metis tsrt_msg tsrt_tick tsrt_tlenleq order_refl)

lemma tlen_tsrt[simp]: assumes "\<And>msg::'m. #\<^sub>\<surd>msg \<le> 1"
  shows "#\<^sub>\<surd>(tsrt\<cdot>xs) = lnpred\<cdot>(#\<^sub>\<surd>(xs:: 'm::{countable,tlen} stream))"
  apply(induction xs)
     apply(simp add: tlen_stream_def)
    apply (simp add: lnzero_def)
  apply simp
  apply(rename_tac msg rest, case_tac "#\<^sub>\<surd>msg=1")
   apply(subst tsrt_tick; simp add: one_lnat_def)
  using One_nat_def lnat.sel_rews(2) lnat_suc_plus one_lnat_def apply presburger
  by (metis add.commute add.right_neutral assms lnat.exhaust lnsuc_lnle_emb one_def order_antisym_conv tsrt_msg zero_least)

definition tsdrop :: "nat \<Rightarrow> 'a::{tlen,countable} stream \<rightarrow> 'a::{tlen,countable} stream" where
"tsdrop n \<equiv> Fixrec.iterate n\<cdot>tsrt"

lemma tsdrop_nothing[simp]:"tsdrop 0\<cdot>s = s"
  by (simp add: tsdrop_def)

lemma tsdrop_empty[simp]:"tsdrop n\<cdot>\<epsilon> = \<epsilon>"
  apply (induction n,simp)
  by (simp add: tsdrop_def)

lemma lub_const_conc: "chain Y \<Longrightarrow> (\<Squnion>x. f s\<cdot>(Y x)) = f s\<cdot>(\<Squnion>x. (Y x))"
  by (metis cont_Rep_cfun2 cont_def lub_eqI)

lemma conc_cont:
  assumes "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> g\<cdot>x \<noteq>\<bottom> \<Longrightarrow> f\<cdot>x = f\<cdot>y"
  shows "cont (\<lambda>s. (f\<cdot>s) \<Zcat>\<Zcat> (g\<cdot>s))"
  apply(rule contI2)
  apply(rule monofunI)
  apply (case_tac "g\<cdot>x \<noteq>\<bottom>")
  apply (simp add: assms monofun_cfun_arg)
  apply (metis (no_types, opaque_lifting) below_trans botconc2 cont_pref_eq1I)
  apply(case_tac "g\<cdot>(\<Squnion>i::nat. Y i) = \<bottom>", simp)
   apply (metis (no_types, lifting) botconc2 ch2ch_Rep_cfunR contlub_cfun_arg lub_mono minimal monofun_cfun_arg)
proof -
  fix Y::"nat \<Rightarrow> 'a"
  assume ch_Y: "chain Y" and ch_2:"chain (\<lambda>i::nat. f\<cdot>(Y i)\<Zcat>\<Zcat>g\<cdot>(Y i))"
      and lub_g: "g\<cdot>(\<Squnion>i::nat. Y i) \<noteq> \<bottom>"
  obtain i where i_def: "g\<cdot>(Y i) \<noteq> \<bottom>"
    by (metis (full_types) ch2ch_Rep_cfunR ch_Y contlub_cfun_arg lub_eq_bottom_iff lub_g)
  have lub_f: "f\<cdot>(\<Squnion>i::nat. Y i) = f\<cdot>(Y i)"
    by (metis assms ch_Y i_def is_ub_thelub)
  have "\<And>n. f\<cdot>(Y (n+i)) = f\<cdot>(Y (i))" 
    apply(rule assms[symmetric], rule chain_mono)
    by(auto simp add: ch_Y i_def)
  thus "f\<cdot>(\<Squnion>i::nat. Y i)\<Zcat>\<Zcat>g\<cdot>(\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. f\<cdot>(Y i)\<Zcat>\<Zcat>g\<cdot>(Y i))" 
    apply(subst(3) lub_range_shift2 [where j=i], simp add: ch_2)
    apply (simp add: lub_f)
    apply(subst lub_const_conc, simp add: ch_Y chain_shift)
    apply(rule monofun_cfun_arg)
    apply(subst contlub_cfun_arg, simp add: ch_Y)
    apply(subst lub_range_shift2 [where j=i]; simp add: ch_Y)
    done
qed

lemma conc_cont_nc:
  assumes "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> g x \<noteq>\<bottom> \<Longrightarrow> f x = f y"
    and "cont g" and "cont f"
  shows "cont (\<lambda>s. (f s) \<Zcat>\<Zcat> (g s))"
  apply(subst(6) Abs_cfun_inverse2[symmetric], simp add: assms)
  apply(subst(10) Abs_cfun_inverse2[symmetric], simp add: assms)
  apply(rule conc_cont)
  using assms by auto

lemma tsdrop_tick[simp]: "#\<^sub>\<surd>x \<noteq> 0 \<Longrightarrow> tsdrop (Suc n)\<cdot>(\<up>x \<Zcat> xs) = tsdrop n\<cdot>xs"
  unfolding iterate_Suc2 tsdrop_def
  by(rule cfun_arg_cong, simp)

lemma tsdrop_msg[simp]: "#\<^sub>\<surd>x = 0 \<Longrightarrow> tsdrop (Suc n)\<cdot>(\<up>x \<Zcat> xs) = tsdrop (Suc n)\<cdot>xs" 
  unfolding iterate_Suc2 tsdrop_def
  by(rule cfun_arg_cong, simp)

context
begin

definition tshd :: "'a::{tlen,countable} stream \<rightarrow> 'a stream" where
"tshd = stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)"

private primrec tstake_nc :: "nat \<Rightarrow> 'a::{countable,tlen} stream \<Rightarrow> 'a stream" where
"tstake_nc    0    _ = \<epsilon>" | 
"tstake_nc (Suc n) s = (tshd\<cdot>s) \<Zcat>\<Zcat> tstake_nc n (tsrt\<cdot>s)" 

private lemma tstake_nc_stwbl_eq:
  assumes "x\<sqsubseteq>y" and "(tstake_nc n (tsrt\<cdot>x)) \<noteq> \<epsilon>"
  shows "(stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>x) = (stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>y)"
  using assms apply(induction n arbitrary: x y)
  apply(rule stwbl_eq_dw, metis tstake_nc.simps(1))
   apply(simp; fail)
  apply(simp add: tshd_def)
  by (metis sconc_fst_empty srtdw_eps strict_stwbl stwbl_eq_dw tsrt_def)

private lemma tstake_cont[cont2cont]: "cont (tstake_nc n)"
  apply(induction n; simp only: tstake_nc.simps)
  apply simp
  apply(rule conc_cont_nc)
    apply(simp add: tshd_def)
    apply(rule tstake_nc_stwbl_eq; simp)
  by (auto simp add: cont_compose_mix)

private lemma tstake_nc_prefix: "tstake_nc n x \<sqsubseteq> x"
  apply(induction n arbitrary: x)
   apply auto[2]
  apply(subst(7) stwbl_srtdw[symmetric, where f="(\<lambda>e. #\<^sub>\<surd>e = 0)"])
  by (simp add: cont_pref_eq1I tsrt_def tshd_def)

private lemma tstake_nc_mono: "tstake_nc n x \<sqsubseteq> tstake_nc (Suc n) x"
  apply(induction n arbitrary: x; simp)
  by (simp add: monofun_cfun)

private lemma tstake_nc_mono2: 
  assumes "n \<le> m" 
  shows "tstake_nc n x \<sqsubseteq> tstake_nc m x"
proof - 
  have "\<And>i. tstake_nc n x \<sqsubseteq> tstake_nc (n+i) x"
    apply(induct_tac i, simp)
    using tstake_nc_mono by (metis add_Suc_right rev_below_trans)
  thus ?thesis by (metis assms ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
qed

lemma [cont2cont]: "chain Y \<Longrightarrow> (\<And>i. cont (Y i)) \<Longrightarrow> cont (\<Squnion>i. Y i)"
  by (simp add: fun_chain_iff lub_fun)

lemma lnat_belowinf_lnsuc[simp]: "ln < \<infinity> \<Longrightarrow> lnsuc\<cdot>(ln) < \<infinity>"
  by (metis fold_inf inf_less_eq linorder_le_less_linear lnat.injects)

(*
lemma tstake_nc_conc_h:
  assumes "#t < \<infinity>"
  and "\<And>s. tstake_nc n (t \<Zcat> s) = t \<Zcat> tstake_nc n s"
  and "\<forall>e. #\<^sub>\<surd> e \<noteq> 0 \<longrightarrow> e \<noteq> a \<and> e \<notin> sValues\<cdot>t"
shows "tstake_nc n (\<up>a \<Zcat> t \<Zcat> s) = \<up>a \<Zcat> t \<Zcat> tstake_nc n s"
  apply (subgoal_tac "#\<^sub>\<surd>a = 0")
  apply (subgoal_tac "tstake_nc n (\<up>a \<Zcat> t \<Zcat> s) = \<up>a \<Zcat> t \<Zcat> (tstake_nc n s)")
  apply blast
  apply (cases "n = 0")
  using assms(2) apply force 
  apply (subgoal_tac "stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>(\<up>a \<Zcat> t \<Zcat> s) = \<up>a \<Zcat> stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>(t \<Zcat> s)") 
  apply (subgoal_tac "(tstake_nc (n - 1) (tsrt\<cdot>(\<up>a \<Zcat> t \<Zcat> s))) = (tstake_nc (n - 1) (tsrt\<cdot>(t \<Zcat> s)))")
  apply (metis tsrt_msg tstake_nc.simps(2) assms(2) assoc_sconc conc_stream_def list_decode.cases)
  apply (metis tsrt_msg)
  apply (meson stwbl_t)
  using assms(3) by auto

lemma tstake_msgs [simp]: 
  assumes "(\<forall>e. #\<^sub>\<surd>e \<noteq> 0 \<longrightarrow> e \<notin> sValues\<cdot>xs)" 
  and "#xs < \<infinity>"
  shows "tstake_nc n (xs \<Zcat>  s) = xs \<Zcat> tstake_nc n s"
  using assms apply(induction xs arbitrary: s rule: finind3)
  using assms(2) apply force
  apply auto[1]
  by (simp add: tstake_nc_conc_h)
*)
private lemma [simp]: "tstake_nc n \<epsilon> = \<epsilon>"
  by(induction n; simp add: tshd_def)

definition tstake :: "nat \<Rightarrow> 'a::{countable,tlen} stream \<rightarrow> 'a stream" where
"tstake n = Abs_cfun (tstake_nc n)" 

end

lemma tstake_def_unfold[simp]:
  fixes n and s
  shows "tstake 0\<cdot>s = \<epsilon>"
  and "tstake (Suc n)\<cdot>s = (stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>s) \<Zcat>\<Zcat> (tstake n\<cdot>(tsrt\<cdot>s))"
  by(simp add: tstake_def tshd_def)+

lemma tstake_epsilon[simp]: "tstake n\<cdot>\<epsilon> = \<epsilon>"
  apply (induction n, simp)
  apply (subgoal_tac "(stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>\<epsilon>) \<Zcat>\<Zcat> (tstake n\<cdot>(tsrt\<cdot>\<epsilon>)) = \<epsilon>")
  apply (subgoal_tac "tstake (Suc n)\<cdot>\<epsilon> = (stwbl (\<lambda>e. #\<^sub>\<surd>e = 0)\<cdot>\<epsilon>) \<Zcat>\<Zcat> (tstake n\<cdot>(tsrt\<cdot>\<epsilon>))")
  by force+

lemma tstake_sValues[simp]: "sValues\<cdot>(tstake n\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply (rule sValues_prefix)
  apply (induction n arbitrary: s)
  apply auto[2]
  apply (subst(7) stwbl_srtdw[symmetric, where f="(\<lambda>e. #\<^sub>\<surd>e = 0)"])
  by (simp add: cont_pref_eq1I tsrt_def)

definition tsnth :: "nat \<Rightarrow> 'a::{tlen,countable} stream \<rightarrow> 'a stream" where
"tsnth n \<equiv> tshd oo (tsdrop n)"

lemma tsdrop_sValues[simp]: "sValues\<cdot>(tsdrop n\<cdot>s) \<subseteq> sValues\<cdot>s"
  apply (induction n)
  apply (simp; fail)
  apply (subgoal_tac "sValues\<cdot>((srt oo sdropwhile (\<lambda>e. #\<^sub>\<surd>e = 0))\<cdot>(tsdrop n\<cdot>s)) \<subseteq> sValues\<cdot>s")
  apply (simp add: tsdrop_def tsrt_def_2; fail)
  apply (subgoal_tac "sValues\<cdot>((sdropwhile (\<lambda>e. #\<^sub>\<surd>e = 0))\<cdot>(tsdrop n\<cdot>s)) \<subseteq> sValues\<cdot>s")
  apply (metis (mono_tags, lifting) tsrt_def_2 tsrt_svalues subset_trans)
  by (meson order_trans sdropwhile_sValues)

end
