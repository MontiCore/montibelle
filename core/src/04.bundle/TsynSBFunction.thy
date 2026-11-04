theory TsynSBFunction

imports SBFin stream.TsynStream

begin


definition tsynMsgToMStream :: "msg tsyn stream \<rightarrow> M stream"  where
  "tsynMsgToMStream = (smap (Timed o Tsyn))"

definition toTsynMsgStream :: "M stream \<rightarrow> msg tsyn stream"  where
  "toTsynMsgStream = (smap ((inv Tsyn) o (inv Timed)))"

definition is_lifted_stream_fn :: "('a::{chan}\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> (M stream \<rightarrow> M stream) \<Rightarrow> bool" where
  "is_lifted_stream_fn sbFn sFn \<equiv> \<forall>sb c. (sbFn\<cdot>sb) \<^enum> c = sFn\<cdot>(sb \<^enum> c)"

definition is_lifted_tsyn_stream_fn :: "('a::{chan}\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> (msg tsyn stream \<rightarrow> msg tsyn stream) \<Rightarrow> bool" where
  "is_lifted_tsyn_stream_fn sbFn sFn \<equiv> is_lifted_stream_fn sbFn (tsynMsgToMStream oo sFn oo toTsynMsgStream)"

text \<open>@{term tsynLenM}: @{term tsynLenM}, but over M streams.\<close>
definition tsynLenM :: "M stream \<rightarrow> lnat"  where
"tsynLenM = (tsynLen oo toTsynMsgStream)"


lemma totsynmsgstream_tsynmsgtomstream:
  assumes "toTsynMsgStream\<cdot>sa = sb"
    and "sValues\<cdot>sa \<subseteq> range (Timed \<circ> Tsyn)"
  shows "sa = tsynMsgToMStream\<cdot>sb"
proof-
  obtain sb where sb_in: "sa = smap (Timed o Tsyn)\<cdot>sb"
    using assms(2) smap_obtainin by blast

  show ?thesis
    apply(subst assms(1)[symmetric])
    apply(simp add: toTsynMsgStream_def tsynMsgToMStream_def)
    apply(subst(2) sb_in)
    apply(simp add: smaps2smap)
    by(simp add: sb_in)
qed

lemma tsynmsgtomstream_svalues: "sValues\<cdot>(tsynMsgToMStream\<cdot>s) \<subseteq> Timed ` Tsyn ` sValues\<cdot>s"
  apply(simp add: tsynMsgToMStream_def smap_sValues)
  by blast

lemma totsynmsgstream_svalues: "sValues\<cdot>(toTsynMsgStream\<cdot>s) \<subseteq> (inv Tsyn) ` (inv Timed) ` sValues\<cdot>s"
  apply(simp add: toTsynMsgStream_def  smap_sValues)
  by blast

lemma toTsynMsgStream_smap_Timed_Tsyn: "toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn)\<cdot>s) = s"
  by(simp add: toTsynMsgStream_def smaps2smap)

lemma toTsynMsgStream_smap_Timed_Tsyn_f: "toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn \<circ> f)\<cdot>s) = smap f\<cdot>s"
  by(simp add: toTsynMsgStream_def smaps2smap)

lemma toTsynMsgStream_tsynMsgToMStream_id[simp]: "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>s) = s"
  by (simp add: toTsynMsgStream_smap_Timed_Tsyn tsynMsgToMStream_def)


definition tsynSBlen::"'cs::{tsynchan} sb \<Rightarrow> lnat" where
"tsynSBlen sb \<equiv> if chDomEmpty TYPE('cs) then \<infinity>
                else LEAST n . n\<in>{tsynLenM\<cdot>(sb \<^enum> c) | c. True}"

theorem tsynSBlen_rule:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
      and "\<And>c. k \<le> tsynLenM\<cdot>(sb \<^enum> c)"
      and "\<exists>c. tsynLenM\<cdot>(sb \<^enum> c) = k"
  shows   "tsynSBlen sb = k"
  by (smt LeastI_ex Least_le Orderings.order_class.dual_order.eq_iff assms(1,2,3) mem_Collect_eq tsynSBlen_def)

theorem tsynSBlen_ruleD:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "chDom TYPE('cs) \<noteq> {}"
      and "tsynSBlen sb = k"
    shows "\<And>c. k \<le> tsynLenM\<cdot>(sb \<^enum> c)"
      and "\<exists>c. tsynLenM\<cdot>(sb \<^enum> c) = k"
  by (smt assms tsynSBlen_def Least_le LeastI_ex assms(1) mem_Collect_eq)+


theorem tsynSBlen_le:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen sb \<le> tsynLenM\<cdot>(sb \<^enum> c)"
  apply(simp add: tsynSBlen_def assms)
  apply(rule Least_le)
  by blast


theorem tsynSBlen_infty:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen sb = \<infinity> \<Longrightarrow> \<forall>c. tsynLenM\<cdot>(sb \<^enum> c) = \<infinity>"
  by (metis assms inf_less_eq tsynSBlen_le)

theorem tsynSBlen_le_rule:
  fixes sba::"'ca::{tsynchan}\<^sup>\<Omega>"
  fixes sbb::"'cb::{tsynchan}\<^sup>\<Omega>"
  fixes ca::"'ca"
  fixes cb::"'cb"
  assumes "\<not>chDomEmpty TYPE('ca)"
      and "\<not>chDomEmpty TYPE('cb)"
      and "\<And>ca'. tsynLenM\<cdot>(sba  \<^enum>  ca) \<le> tsynLenM\<cdot>(sba  \<^enum>  ca')"
      and "\<And>cb'. tsynLenM\<cdot>(sbb  \<^enum>  cb) \<le> tsynLenM\<cdot>(sbb  \<^enum>  cb')"
      and "tsynLenM\<cdot>(sba  \<^enum>  ca) \<le> tsynLenM\<cdot>(sbb  \<^enum>  cb)"
  shows "tsynSBlen sba \<le> tsynSBlen sbb"
proof-
  have lhs: "(LEAST n::lnat. \<exists>c::'ca. n = tsynLenM\<cdot>(sba  \<^enum>  c)) = tsynLenM\<cdot>(sba  \<^enum>  ca) "
    by (smt LeastI Least_le nle_le assms)

  have rhs: "(LEAST n::lnat. \<exists>c::'cb. n = tsynLenM\<cdot>(sbb  \<^enum>  c)) = tsynLenM\<cdot>(sbb  \<^enum>  cb)"
    by (smt LeastI Least_le nle_le assms)

  show ?thesis
    by(auto simp add: tsynSBlen_def assms lhs rhs)
qed

lemma tsynsblen_cont[simp]:"cont (tsynSBlen::'cs::{tsynchan,finite} sb \<Rightarrow> lnat)"
  unfolding tsynSBlen_def
  apply(intro cont2cont)
  apply(subst least2min)
  apply(simp only: len_stream_def finite_lenset)
  using finite_lenset[of slen]
  apply blast
  apply(simp only: tsynLenM_def len_stream_def,rule Min_cont)
  apply(rule fun_eqI)
  using lnle_def by blast

theorem exists_least:
  assumes"\<not>chDomEmpty TYPE('Out::tsynchan)"
  shows"\<exists>spf::('In::chan)\<^sup>\<Omega> \<rightarrow> ('Out::tsynchan)\<^sup>\<Omega>. \<forall>sb. tsynSBlen (spf\<cdot>sb) = 0"
  apply(rule_tac x="Cpo.pcpo_class.bottom" in exI)
  apply (simp add: tsynSBlen_def)
  using assms apply auto
  apply(simp add: tsynLenM_def toTsynMsgStream_def)
  by (metis (full_types) LeastI)

lemma helper[simp]:
  assumes"\<not>chDomEmpty TYPE('cs::tsynchan)"
  shows"lsb_well (\<lambda>c::'cs::tsynchan. \<up>(Timed (Tsyn \<sim>))\<^sup>\<infinity>)"
  apply(auto simp add: lsb_well_def)
  apply(subst ctype_def, simp add: assms)
  by (meson assms ctype_empty_iff dom2ctypenempty)

theorem exists_max:
  assumes"\<not>chDomEmpty TYPE('cs::tsynchan)"
  shows"\<exists>sb::'cs\<^sup>\<Omega>.  #sb = \<infinity> \<and> #\<^sub>\<surd> sb = \<infinity> \<and> tsynSBlen (sb) = 0"
  apply(rule_tac x="Abs_lsb(\<lambda>c::'Out::tsynchan. smap (Timed o Tsyn)\<cdot>(\<up>Eps\<^sup>\<infinity>))" in exI)
  apply (simp add: tsynSBlen_def)
  using assms apply auto
    apply(rule sblen_rule,simp_all add: assms)
     apply(simp add: sbgetch_insert2 assms)+
  apply(rule sbtlen_rule)
     apply(simp add: sbgetch_insert2 assms one_def steam_tlen_inf)+
  apply(simp add: tsynLenM_def toTsynMsgStream_def tsynlen_insert tsyn2ustream_def)
  by (metis (full_types) LeastI)



definition "tsynSBRemDups_raw" :: "'cs::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>" where
  "tsynSBRemDups_raw \<equiv> \<lambda>sb. Abs_lsb (\<lambda>c. (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb\<^enum>c))"


lemma tsynSBRemDups_raw_sValues_se:
  assumes "sValues\<cdot>s \<subseteq> range(Timed o Tsyn)"
  shows   "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))) \<subseteq> sValues\<cdot>s \<union> {Timed (Tsyn \<sim>)}"
proof -
  have "sValues\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s)) \<subseteq>
        sValues\<cdot>(toTsynMsgStream\<cdot>s) \<union> {\<sim>}"
    using svalues_tsynremdups_subset_input_union_eps by auto

  then have "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))) \<subseteq>
             (Timed o Tsyn) ` (sValues\<cdot>(toTsynMsgStream\<cdot>s) \<union> {\<sim>})"
    by (metis smap_sValues subset_image_iff
        tsynMsgToMStream_def)

  also have "... = (Timed o Tsyn) ` (sValues\<cdot>(toTsynMsgStream\<cdot>s)) \<union> {(Timed o Tsyn) \<sim>}"
    by auto

  also have "(Timed o Tsyn) ` (sValues\<cdot>(toTsynMsgStream\<cdot>s)) =
             (Timed o Tsyn) ` ((inv Tsyn o inv Timed) ` (sValues\<cdot>s))"
    by (simp add: smap_sValues
        toTsynMsgStream_def)

  also have h: "... = ((Timed o Tsyn) o (inv Tsyn o inv Timed)) ` (sValues\<cdot>s)"
    by (simp add: image_comp)

  also have "... = id ` (sValues\<cdot>s)"
    apply (auto simp: Channel.inj_timed Channel.inj_tsyn)
    using assms image_def inv_into_into apply auto[1]
    apply (auto simp: image_def)
    using assms
    apply (simp add: f_inv_into_f range_eqI)
    using subset_iff by fastforce

  also have "... = sValues\<cdot>s"
    by simp

  also have "sValues\<cdot>s \<union> {(Timed o Tsyn) \<sim>} = sValues\<cdot>s \<union> {Timed (Tsyn \<sim>)}"
    by (simp add: comp_def)

  finally show ?thesis .
qed

lemma cMsg_nonempty_tsynchan:
  assumes "chDom TYPE ('cs) \<noteq> {}"
  shows "cMsg (Rep (c::'cs::{tsynchan})) \<noteq> {}"
proof -
  fix c :: "'cs::tsynchan"
  have "Rep c \<in> chDom TYPE('cs)"
    unfolding chDom_def
    using assms cnotempty_rule by blast
  then show ?thesis
    using cnotempty_cdom ctype_empty_iff dom2ctypenempty by blast
qed

lemma Eps_ctype_Rep_c :
  assumes "chDom TYPE ('cs) \<noteq> {}"
  shows "{Timed (Tsyn \<sim>)} \<subseteq> ctype (Rep (c::'cs::tsynchan))"
  apply auto
  proof-
    have h1: "cTime (Rep c) = TTsyn"
      by (simp add: assms)
    have h2: "cMsg (Rep c) \<noteq> {}"
      using cMsg_nonempty_tsynchan assms
      by auto
    then show "Timed (Tsyn \<sim>) \<in> ctype (Rep c)"
      using h1 ctype_def by force
  qed

lemma tsynchan_svalues: "sValues\<cdot>((sb :: 'cs::{tsynchan}\<^sup>\<Omega>)  \<^enum>  c) \<subseteq> Timed ` Tsyn ` UNIV"
  apply(insert sbgetch_ctypewell[of c sb])
  apply(simp add: ctype_def)
  apply(case_tac "chDomEmpty TYPE('cs)", simp_all add: cMsg_nonempty_tsynchan)
  by blast

lemma tsynSBRemDups_raw_sValues_subset_ctype_chDom_not_empty:
  assumes NichtLeer: "chDom TYPE('cs::{tsynchan}) \<noteq> {}"
  shows "\<And>sb::'cs::{tsynchan}\<^sup>\<Omega>. \<forall>c::'cs::{tsynchan}.
    sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)"
proof (intro allI)
  fix sb :: "'cs::{tsynchan}\<^sup>\<Omega>"
  fix c :: "'cs::{tsynchan}"

  have h: "{Timed (Tsyn \<sim>)} \<subseteq> ctype (Rep c)"
    using NichtLeer Eps_ctype_Rep_c by simp
  have h1: "sValues\<cdot>(sb \<^enum> c) \<subseteq> range (Timed \<circ> Tsyn)"
  proof -
    have "sValues\<cdot>(sb \<^enum> c) \<subseteq> ctype (Rep c)"
      using sbgetch_ctypewell by blast
    moreover have "ctype (Rep c) \<subseteq> range (Timed \<circ> Tsyn)"
    proof -
      have ct: "cTime (Rep c) = TTsyn"
        by (simp add: assms)
      show ?thesis
      proof (cases "cMsg (Rep c) = {}")
        case True
        then show ?thesis
          by (simp add: ctype_def)
      next
        case False
        with ct show ?thesis
          by (auto simp: ctype_def)
      qed
    qed
    ultimately show ?thesis by blast
  qed
  have h2:
    "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
       \<subseteq> sValues\<cdot>(sb \<^enum> c) \<union> {Timed (Tsyn \<sim>)}"
    using h1 tsynSBRemDups_raw_sValues_se by presburger

  have "sValues\<cdot>(sb \<^enum> c) \<subseteq> ctype (Rep c)"
    using sbgetch_ctypewell by blast
  with h have "sValues\<cdot>(sb \<^enum> c) \<union> {Timed (Tsyn \<sim>)} \<subseteq> ctype (Rep c)"
    by auto
  with h2 show
    "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
       \<subseteq> ctype (Rep c)"
    by blast
qed

lemma tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty:
  assumes "chDom TYPE('cs::{tsynchan}) = {}"
  shows "\<forall>c::'cs. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) = {}"
  apply (auto simp: sbGetCh_def assms toTsynMsgStream_def
      tsynRemDups_def sscanlAOne_def tsynMsgToMStream_def)
  done

lift_definition tsynSBRemDups :: "'cs::{tsynchan}\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" is
"tsynSBRemDups_raw"
  apply (simp add: tsynSBRemDups_raw_def)
  apply (intro cont2cont)
  apply (simp add: lsb_well_def)
proof -
  fix sb :: "'cs::{tsynchan}\<^sup>\<Omega>"
  have "chDom TYPE('cs::{tsynchan}) = {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)"
    using Channel.dom2ctypeempty tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty
    by blast
  have "chDom TYPE('cs::{tsynchan}) \<noteq> {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)"
    using tsynSBRemDups_raw_sValues_subset_ctype_chDom_not_empty by blast
  show "\<forall>c::'cs.
          sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
            \<subseteq> ctype (Rep c)"
    using \<open>chDom TYPE('cs) \<noteq> {} \<Longrightarrow> \<forall>c::'cs. sValues\<cdot> (tsynMsgToMStream\<cdot> (tsynRemDups\<cdot> (toTsynMsgStream\<cdot>((sb::'cs\<^sup>\<Omega>) \<^enum> c)))) \<subseteq> ctype (Rep c)\<close>
    \<open>chDomEmpty TYPE('cs) \<Longrightarrow> \<forall>c::'cs. sValues\<cdot> (tsynMsgToMStream\<cdot> (tsynRemDups\<cdot> (toTsynMsgStream\<cdot>((sb::'cs\<^sup>\<Omega>) \<^enum> c)))) \<subseteq> ctype (Rep c)\<close> by blast
qed

lemma tsynSBRemDups_rule:
  assumes "\<And>c. (sbo \<^enum> c) = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbi \<^enum> c)"
  shows "tsynSBRemDups\<cdot>sbi = sbo"
proof (rule sb_eqI)
  fix c
  show "(tsynSBRemDups\<cdot>sbi) \<^enum> c = sbo \<^enum> c"
  proof -
    have "(tsynSBRemDups\<cdot>sbi) \<^enum> c = sbGetCh c\<cdot>(tsynSBRemDups\<cdot>sbi)"
      by simp

    moreover have "... = sbGetCh c\<cdot>(tsynSBRemDups_raw sbi)"
      by (simp add: tsynSBRemDups.rep_eq)

    moreover have "... = Rep_lsb (tsynSBRemDups_raw sbi) c"
      using sbgetch_insert2 by blast

    moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbi \<^enum> c)"
      by (metis (no_types, lifting) ext
          abs_rep_sb_sb assms sbgetch_insert2
          tsynSBRemDups_raw_def)

    moreover have "... = sbo \<^enum> c"
      using assms by presburger

    ultimately show ?thesis
      by (metis)
  qed
qed

lemma tsynSBRemDups_raw_sValues_se_ch:
  fixes sb :: "'cs::tsynchan \<^sup>\<Omega>"
  fixes c  :: "'cs::tsynchan"
  shows
    "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
       \<subseteq> sValues\<cdot>(sb \<^enum> c) \<union> {Timed (Tsyn \<sim>)}"
proof -
  have sv_subset_ctype: "sValues\<cdot>(sb \<^enum> c) \<subseteq> ctype (Rep c)"
    using sbgetch_ctypewell by blast
  have ctype_subset_range: "ctype (Rep c) \<subseteq> range (Timed \<circ> Tsyn)"
  proof -
    show ?thesis
    proof (cases "cMsg (Rep c) = {}")
      case True
      then show ?thesis
        by (simp add: ctype_def)
    next
      case False
      have ct: "cTime (Rep c) = TTsyn"
        using False ctype_empty_iff dom2ctypeempty sometsynchan by blast
      then show ?thesis
        by (auto simp: ctype_def)
    qed
  qed
  have sv_subset_range: "sValues\<cdot>(sb \<^enum> c) \<subseteq> range (Timed \<circ> Tsyn)"
    using sv_subset_ctype ctype_subset_range by blast

  have
    "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))
       \<subseteq> sValues\<cdot>(sb \<^enum> c) \<union> {Timed (Tsyn \<sim>)}"
    by (rule tsynSBRemDups_raw_sValues_se[OF sv_subset_range])

  thus ?thesis .
qed


lemma tsynSBRemDups_raw_lsb_well:
  shows "lsb_well (\<lambda>(c::'cs::tsynchan). (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c))"
  unfolding lsb_well_def
proof (intro allI)
  fix c :: 'cs
  show "sValues\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c))
        \<subseteq> ctype (Rep c)"
  proof-
    have "chDom TYPE('cs::{tsynchan}) = {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)"
      using Channel.dom2ctypeempty tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty  by blast
    have "chDom TYPE('cs::{tsynchan}) \<noteq> {} \<Longrightarrow> \<forall>c::'cs::{tsynchan}. sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))) \<subseteq> ctype (Rep c)"
      using tsynSBRemDups_raw_sValues_subset_ctype_chDom_not_empty by blast
    then show ?thesis by (metis cfcomp2 empty_subsetI tsynSBRemDups_raw_sValues_subset_ctype_chDom_empty)
  qed
qed


lemma tsynSBRemDups_insert:
  shows "Rep_lsb (tsynSBRemDups\<cdot>(sb::'cs\<^sup>\<Omega>)) = (\<lambda>(c::'cs::tsynchan). (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>((Rep_lsb sb) c))"
proof (rule ext)
  fix c :: "'cs::tsynchan"
  have "lsb_well (\<lambda>c. tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))))"
    using tsynSBRemDups_raw_lsb_well by auto

  then have
      "Rep_lsb (Abs_lsb (\<lambda>c.
         tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))))) c
       = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c)))"
    by (simp)


  then have "Rep_lsb (tsynSBRemDups_raw sb) c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
    by (metis sb_rep_abs tsynSBRemDups_raw_def tsynSBRemDups_raw_lsb_well)

  moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sbGetCh c\<cdot>sb)"
    by simp

  moreover have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(Rep_lsb sb c)"
    by (metis (no_types) sbgetch_insert2)

  ultimately show "Rep_lsb (tsynSBRemDups\<cdot>(sb::'cs\<^sup>\<Omega>)) c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(Rep_lsb sb c)"
    by (metis (mono_tags, lifting) tsynSBRemDups.rep_eq tsynSBRemDups_raw_def)
qed


lemma tsynSBRemDups_tsynSBlen_le_h:
  "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) \<le> tsynLenM\<cdot>s"
proof -
  have lhs: "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) =
            tsynLen\<cdot>(toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))))"
    by (simp add: tsynLenM_def oo_def)

  have conversion_eq: "\<And>x. toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = x"
  proof -
    fix x
    have "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = smap ((inv Tsyn) o (inv Timed))\<cdot>(smap (Timed o Tsyn)\<cdot>x)"
      by (simp add: toTsynMsgStream_def tsynMsgToMStream_def)
    also have "... = smap (((inv Tsyn) o (inv Timed)) o (Timed o Tsyn))\<cdot>x"
      by (simp add: smapsmap2smap)
    also have "... = x"
  proof -
    have "\<forall>s. toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>s) = s \<or> inv Tsyn \<circ> inv Timed \<circ> (Timed \<circ> Tsyn) \<noteq> id"
      by (metis (no_types) smap_id smapsmap2smap toTsynMsgStream_def tsynMsgToMStream_def)
    then show ?thesis
      using toTsynMsgStream_def tsynMsgToMStream_def
      using calculation by auto
  qed
    finally show "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>x) = x" .
  qed

  then have "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))) = tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s)"
    by simp

  with lhs have lhs_simplified: "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s) =
                               tsynLen\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))"
    by simp

  have "tsynLen\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s)) \<le> tsynLen\<cdot>(toTsynMsgStream\<cdot>s)"
    using tsynlen_tsynremdups_le by auto

  also have "tsynLen\<cdot>(toTsynMsgStream\<cdot>s) = tsynLenM\<cdot>s"
    by (simp add: tsynLenM_def)

  finally show ?thesis
    by (metis lhs_simplified)
qed

lemma tsynSBRemDups_tsynSBlen_le:
  "tsynSBlen (tsynSBRemDups\<cdot>sb) \<le> tsynSBlen sb"
proof (cases "chDomEmpty TYPE('a)")
  case True
  then have "tsynSBlen sb = \<infinity>" unfolding tsynSBlen_def by simp
  then show ?thesis using  tsynSBlen_def
    by simp
next
  case False
  have h1: "\<forall>c. tsynLenM\<cdot>((tsynSBRemDups\<cdot>sb) \<^enum> c) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
    proof
      fix c::'a
      have stream_eq: "(tsynSBRemDups\<cdot>sb) \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
        by (metis (no_types, lifting) ext Rep_cfun_inverse cfcomp2 tsynSBRemDups.rep_eq sb_rep_abs sbgetch_insert2 tsynSBRemDups_raw_def
          tsynSBRemDups_raw_lsb_well)

      have "tsynLenM\<cdot>((tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
        using tsynSBRemDups_tsynSBlen_le_h by auto

      then show "tsynLenM\<cdot>((tsynSBRemDups\<cdot>sb) \<^enum> c) \<le> tsynLenM\<cdot>(sb \<^enum> c)"
        by (simp add: stream_eq)
    qed
  show ?thesis
    using h1 by (metis (mono_tags, opaque_lifting) False trans_lnle tsynSBlen_ruleD(1,2))
qed

lemma tsynsblen_strict [simp]:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
  shows "tsynSBlen (\<bottom>:: ('cs::tsynchan)\<^sup>\<Omega>) = 0"
  apply (simp add: tsynLenM_def Least_equality tsynSBlen_def)
proof
  show "chDom TYPE('cs::tsynchan) \<noteq> {}" using assms by simp
next
  show "chDom TYPE('cs::tsynchan) \<noteq> {} \<longrightarrow> #\<^sub>-(toTsynMsgStream\<cdot>\<epsilon>) = 0"
    apply (auto simp: toTsynMsgStream_def)
    done
qed

text \<open>Prefixing @{term "TSynMsg a"} on a channel increases its @{term tsynLenM} by one.\<close>
lemma tsynsblen_sconc_msg:
  "tsynLenM \<cdot> (\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> (sbGetCh c\<cdot>sb))
   = lnsuc \<cdot> (tsynLenM \<cdot> (sbGetCh c\<cdot>sb))"
  apply (auto simp: tsynLenM_def toTsynMsgStream_def)
  using tsynlen_sconc_msg
  by blast

lemma tsynsblen_sconc_msg2:
  assumes Hne: "\<And>c::'cs::{tsynchan}. (inv Tsyn \<circ> inv Timed) (sbegetch c sbe) \<noteq> Eps"
  shows "tsynSBlen (sbe \<Zcat>\<^sup>\<surd> (sb::'cs::{tsynchan}\<^sup>\<Omega>)) = lnsuc\<cdot>(tsynSBlen sb)"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  have "tsynSBlen sb = \<infinity>"
    by (simp add: tsynSBlen_def True)
  moreover have "tsynSBlen (sbe \<Zcat>\<^sup>\<surd> sb) = \<infinity>"
    by (metis True calculation sb_empty_eq)
  ultimately show ?thesis
    by (simp add: fold_inf)
next
  case False
  have dom: "chDom TYPE('cs) \<noteq> {}"
    using False by simp

  let ?k = "tsynSBlen sb"

  have k_lb: "\<And>c::'cs. ?k \<le> tsynLenM\<cdot>(sb \<^enum> c)"
    using tsynSBlen_ruleD(1)[OF dom refl] .

  have k_ex: "\<exists>c0::'cs. tsynLenM\<cdot>(sb \<^enum> c0) = ?k"
    using tsynSBlen_ruleD(2)[OF dom refl] .

  have Split:
    "\<And>c::'cs. (sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
  proof -
    fix c :: 'cs
    have "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = (sbe2sb sbe \<^enum> c) \<Zcat> (sb \<^enum> c)"
      by (simp add: SB.sbh_sbecons SB.sbrt_sbecons SB.sbconc_well) 
    also have "sbe2sb sbe \<^enum> c = \<up>(sbegetch c sbe)"
      using dom by (simp add: SB.sbe2sb_getch)
    finally show "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
      by simp
  qed

  have Len_step:
    "\<And>c::'cs. tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c) = lnsuc\<cdot>(tsynLenM\<cdot>(sb \<^enum> c))"
  proof -
    fix c :: 'cs
    have Split:
      "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
      using dom
      by (simp add: SB.sbe2sb_getch SB.sbh_sbecons SB.sbrt_sbecons)

    have ne: "(inv Tsyn \<circ> inv Timed) (sbegetch c sbe) \<noteq> Eps" 
      using assms by simp
    show "tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c) = lnsuc\<cdot>(tsynLenM\<cdot>(sb \<^enum> c))"
      unfolding tsynLenM_def
      using Split ne tsynlen_sconc_msg2
      by (metis (no_types, lifting) cfcomp2 smap_scons toTsynMsgStream_def)
  qed


  have lb2: "\<And>c::'cs. lnsuc\<cdot>?k \<le> tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c)"
  proof -
    fix c :: 'cs
    have "lnsuc\<cdot>?k \<le> lnsuc\<cdot>(tsynLenM\<cdot>(sb \<^enum> c))"
      using k_lb[of c] by (simp add: lnsuc_lnle_emb)
    also have "... = tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c)"
      using Len_step by presburger
    finally show "lnsuc\<cdot>?k \<le> tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c)" .
  qed

  obtain c0 :: 'cs where c0_eq: "tsynLenM\<cdot>(sb \<^enum> c0) = ?k"
    using k_ex by blast

  have ex2: "\<exists>c0::'cs. tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c0) = lnsuc\<cdot>?k"
    using c0_eq 
    by (metis Len_step)

  show ?thesis
    using tsynSBlen_rule[OF dom lb2 ex2]
    by simp
qed

lemma tsynsblen_sconc_Eps:
  assumes Hne: "\<And>c::'cs::{tsynchan}. (inv Tsyn \<circ> inv Timed) (sbegetch c sbe) = Eps"
  shows "tsynSBlen (sbe \<Zcat>\<^sup>\<surd> (sb::'cs::{tsynchan}\<^sup>\<Omega>)) = tsynSBlen sb"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  have "tsynSBlen sb = \<infinity>"
    by (simp add: tsynSBlen_def True)
  moreover have "tsynSBlen (sbe \<Zcat>\<^sup>\<surd> sb) = \<infinity>"
    by (metis True calculation sb_empty_eq)
  ultimately show ?thesis
    by (simp add: fold_inf)
next
  case False
  have dom: "chDom TYPE('cs) \<noteq> {}"
    using False by simp

  let ?k = "tsynSBlen sb"

  have k_lb: "\<And>c::'cs. ?k \<le> tsynLenM\<cdot>(sb \<^enum> c)"
    using tsynSBlen_ruleD(1)[OF dom refl] .

  have k_ex: "\<exists>c0::'cs. tsynLenM\<cdot>(sb \<^enum> c0) = ?k"
    using tsynSBlen_ruleD(2)[OF dom refl] .

  have Split:
    "\<And>c::'cs. (sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
  proof -
    fix c :: 'cs
    have "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = (sbe2sb sbe \<^enum> c) \<Zcat> (sb \<^enum> c)"
      by (simp add: SB.sbh_sbecons SB.sbrt_sbecons SB.sbconc_well) 
    also have "sbe2sb sbe \<^enum> c = \<up>(sbegetch c sbe)"
      using dom by (simp add: SB.sbe2sb_getch)
    finally show "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
      by simp
  qed

  have Len_step:
    "\<And>c::'cs. tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c) = (tsynLenM\<cdot>(sb \<^enum> c))"
  proof -
    fix c :: 'cs
    have Split:
      "(sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c = \<up>(sbegetch c sbe) \<Zcat> (sb \<^enum> c)"
      using dom
      by (simp add: SB.sbe2sb_getch SB.sbh_sbecons SB.sbrt_sbecons)

    have ne: "(inv Tsyn \<circ> inv Timed) (sbegetch c sbe) = Eps" 
      using assms by simp
    show "tsynLenM\<cdot>((sbe \<Zcat>\<^sup>\<surd> sb) \<^enum> c) = (tsynLenM\<cdot>(sb \<^enum> c))"
      unfolding tsynLenM_def
      using Split ne tsynlen_sconc_Eps
      by (metis (no_types, lifting) cfcomp2 smap_scons toTsynMsgStream_def)
  qed
  

  show ?thesis
    using tsynSBlen_rule[OF dom]
    by (metis Len_step dom tsynSBlen_ruleD(1,2))
qed

lemma totsynlsgstream_sconc: "toTsynMsgStream\<cdot>(s1 \<Zcat> s2) = toTsynMsgStream\<cdot>(s1) \<Zcat> toTsynMsgStream\<cdot>(s2)"
  unfolding toTsynMsgStream_def
  by (simp add: smap_split)

lemma tsynlen_sconc: assumes "#s1 < \<infinity>" shows "tsynLen\<cdot>(s1  \<Zcat> s2) = tsynLen\<cdot>(s1) + tsynLen\<cdot>(s2)"
  unfolding tsynLen_def
  using totsynlsgstream_sconc assms sconc_slen2 tsynabs_sconc
  by (metis (lifting) ext tsynLen_def tsynlen_insert)

lemma tsynlenm_sbconc:
  assumes "\<And> c1. #((sb1  \<^enum>  c1)) < \<infinity>"
  shows "\<And>c. tsynLenM\<cdot>((sbConc (sb1::'cs::{tsynchan}\<^sup>\<Omega>)\<cdot>sb2) \<^enum> c) =  tsynLenM\<cdot>(sb1 \<^enum> c) + tsynLenM\<cdot>(sb2 \<^enum> c)"
  apply (auto simp: sbconc_getch tsynLenM_def totsynlsgstream_sconc)
proof-
  have "\<And>c. #(toTsynMsgStream\<cdot>(sb1  \<^enum>  c)) < \<infinity>" using assms toTsynMsgStream_def by (metis slen_smap)
  then show "\<And>c::'cs. #\<^sub>-(toTsynMsgStream\<cdot>(sb1  \<^enum>  c) \<Zcat> toTsynMsgStream\<cdot>(sb2  \<^enum>  c)) = #\<^sub>-(toTsynMsgStream\<cdot>(sb1  \<^enum>  c)) + #\<^sub>-(toTsynMsgStream\<cdot>(sb2  \<^enum>  c))"
    using tsynlen_sconc by auto
qed

lemma tsynsblen_sconc_finite:
  fixes c :: "'cs::{tsynchan}" and k n :: nat
  assumes "\<And> c1. #((sb1  \<^enum>  c1)) < \<infinity>"
  assumes sb1_min: "tsynSBlen (sb1::'cs::{tsynchan}\<^sup>\<Omega>) = Fin k"
  assumes sb2_min: "tsynSBlen (sb2::'cs::{tsynchan}\<^sup>\<Omega>) = Fin n"
  assumes sameLeast:
    "tsynLenM\<cdot>(sbGetCh c\<cdot>sb1) = Fin k \<and> tsynLenM\<cdot>(sbGetCh c\<cdot>sb2) = Fin n"
  shows "tsynSBlen (sbConc sb1\<cdot>sb2) = Fin (k + n)"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  have a1: "tsynSBlen sb1 = \<infinity>" unfolding tsynSBlen_def using True by simp
  have "tsynSBlen sb2 = \<infinity>" unfolding tsynSBlen_def using True by simp
  then show ?thesis using a1 assms by auto
next
  case False  
  have SplitConc: "\<And>d::'cs. (sbConc sb1\<cdot>sb2) \<^enum> d = (sb1 \<^enum> d) \<Zcat> (sb2 \<^enum> d)"
    using sbconc_getch by simp

  have dom: "chDom TYPE('cs) \<noteq> {}"
    using False by simp

  have lb1: "\<And>d::'cs. Fin k \<le> tsynLenM\<cdot>(sb1 \<^enum> d)"
    using tsynSBlen_ruleD(1)[OF dom sb1_min] .
  
  have lb2: "\<And>d::'cs. Fin n \<le> tsynLenM\<cdot>(sb2 \<^enum> d)"
    using tsynSBlen_ruleD(1)[OF dom sb2_min] .

  have LB:
  "\<And>d::'cs. Fin (k+n) \<le> tsynLenM\<cdot>((sbConc sb1\<cdot>sb2) \<^enum> d)"
  proof -
    fix d :: 'cs    
    have d1: "tsynLenM\<cdot>(sbGetCh d\<cdot>(sbConc sb1\<cdot>sb2)) = tsynLenM\<cdot>((sbGetCh d\<cdot>sb1 ) \<Zcat> sb2 \<^enum> d)"
      using SplitConc by simp
    
    moreover have "Fin (k+n) \<le> (tsynLenM\<cdot>(sb1 \<^enum> d)) + (tsynLenM\<cdot>(sb2 \<^enum> d))"
      using lb1[of d] lb2[of d]
      by (metis lessequal_addition lnat_plus_fin)
    ultimately show "Fin (k+n) \<le> tsynLenM\<cdot>((sbConc sb1\<cdot>sb2) \<^enum> d)"
      apply (auto simp: sbconc_getch)
      using assms
      by (metis d1 tsynlenm_sbconc)
  qed

  have ex : "tsynLenM\<cdot>((sbConc sb1\<cdot>sb2) \<^enum> c) =  Fin (k+n)" 
    using tsynlenm_sbconc assms by (metis lnat_plus_fin)
  then show ?thesis 
    using LB ex dom tsynSBlen_rule by blast
qed

lemma tsynlenm_sconc_infinite:
  assumes A: "tsynLenM\<cdot>as = Fin k"
      and B: "tsynLenM\<cdot>bs = Fin n"
  shows   "tsynLenM\<cdot>(as \<Zcat> bs) \<le> Fin (k+n)"
  using tsynlen_sconc_infinite assms
  by (simp add: tsynLenM_def toTsynMsgStream_def Stream.smap_split)

lemma tsynsblen_sconc_infinite:
  fixes c :: "'cs::{tsynchan}" and k n :: nat
  assumes "tsynSBlen sb1 = Fin k" and "tsynSBlen sb2 = Fin n"
  assumes sameLeast:
    "tsynLenM\<cdot>(sbGetCh c\<cdot>sb1) = Fin k \<and> tsynLenM\<cdot>(sbGetCh c\<cdot>sb2) = Fin n"
  shows "tsynSBlen (sbConc (sb1::'cs::{tsynchan}\<^sup>\<Omega>)\<cdot>sb2) \<le> Fin (k + n)"
proof (cases "chDomEmpty TYPE('cs)")
  case True
  have a1: "tsynSBlen sb1 = \<infinity>" unfolding tsynSBlen_def using True by simp
  have "tsynSBlen sb2 = \<infinity>" unfolding tsynSBlen_def using True by simp
  then show ?thesis using a1 assms by auto
next
  case False
  have SBlen_conc:
  "tsynSBlen (sbConc sb1\<cdot>sb2) =
   (LEAST l. l \<in> {tsynLenM\<cdot>((sb1 \<^enum> d) \<Zcat> (sb2 \<^enum> d)) | d. True})"
    unfolding tsynSBlen_def using False
    by (simp add: sbconc_getch)
  let ?S = "{tsynLenM\<cdot>((sb1 \<^enum> d) \<Zcat> (sb2 \<^enum> d)) | d. True}"
  let ?x = "tsynLenM\<cdot>((sb1 \<^enum> c) \<Zcat> (sb2 \<^enum> c))"
  have x_in: "?x \<in> ?S" by auto
  have least_le_x: "(LEAST l. l \<in> ?S) \<le> ?x"
    using x_in by (rule Least_le)
  have len1: "tsynLenM\<cdot>(sb1 \<^enum> c) = Fin k" and len2: "tsynLenM\<cdot>(sb2 \<^enum> c) = Fin n"
    using sameLeast by auto
  have x_le: "?x \<le> Fin (k+n)"
    unfolding Let_def
    using tsynlenm_sconc_infinite[OF len1 len2] .

  show ?thesis
    unfolding SBlen_conc
    using least_le_x x_le by (rule order_trans)

qed

lemma tsynlenm_slen:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
  shows "\<And>c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>(sb::'cs::{tsynchan}\<^sup>\<Omega>)) \<le> #(sbGetCh c\<cdot>(sb::'cs::{tsynchan}\<^sup>\<Omega>))"
  unfolding tsynLenM_def toTsynMsgStream_def
  apply (simp add: tsynabs_slen tsynlen_insert)
  by (metis slen_smap tsynabs_slen)

lemma tsynsblen_slen:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
  shows "tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) \<le> #sb"
  apply (auto simp: tsynSBlen_def)
  using assms tsynlenm_slen
  by (metis (mono_tags, lifting) Least_le dual_order.trans sblen2slen)

lemma tsynlenm_singleton_msg:
  assumes "sbGetCh c\<cdot>sb = \<up>(Timed (Tsyn (TSynMsg a)))"
  shows "tsynLenM\<cdot>(sbGetCh c\<cdot>sb) = Fin 1"
  unfolding tsynLenM_def
proof-
  have "(tsynLen oo toTsynMsgStream)\<cdot>(sb  \<^enum>\<^sub>\<star>  c) = tsynLen\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
    by (auto simp: oo_def)
  have "tsynLen\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>\<^sub>\<star>  c)) = tsynLen\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg a)))))"
    using assms by simp
  have b: "toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg a)))) = \<up>(TSynMsg a)"
    unfolding toTsynMsgStream_def by simp
  have a: "tsynLen\<cdot>(\<up>(TSynMsg a)) = Fin 1"
    by (simp add: tsynlen_singleton_msg)

  show "(tsynLen oo toTsynMsgStream)\<cdot>(sb  \<^enum>\<^sub>\<star>  c) = Fin 1"
    by (simp add: a b assms)
qed

lemma tsynsblen_singleton_msg:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
    and "\<exists> c. sbGetCh c\<cdot>sb = \<up>(Timed (Tsyn (TSynMsg a)))"
    and "\<forall> c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) \<noteq> Fin 0"
  shows "tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) = Fin 1"
proof-
  have a1: "tsynSBlen sb \<ge> 1" 
    using assms
    by (metis less_one linorder_not_less lnat_well_h1 one_lnat_def tsynSBlen_ruleD(2))
  moreover have "tsynLenM \<cdot> (\<up>(Timed (Tsyn (TSynMsg a)))) = 1" 
    using assms(2) one_lnat_def tsynlenm_singleton_msg by force
  then have a2: "\<exists> c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) = 1" using assms 
    by (metis sbgetch_insert sbgetch_insert2 sup_noteps)
  show ?thesis using assms(2) a1 a2 
    by (metis assms(1) less2eq one_lnat_def tsynSBlen_ruleD(1))
qed

lemma tsynlenm_singleton_eps:
  assumes "sbGetCh c\<cdot>sb = \<up>(Timed (Tsyn (Eps)))"
  shows "tsynLenM\<cdot>(sbGetCh c\<cdot>((sb::'cs::{tsynchan}\<^sup>\<Omega>))) = 0"
  unfolding tsynLenM_def
proof-
  have "(tsynLen oo toTsynMsgStream)\<cdot>(sb  \<^enum>\<^sub>\<star>  c) = tsynLen\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
    by (auto simp: oo_def)
  have "tsynLen\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>\<^sub>\<star>  c)) = tsynLen\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (Eps)))))"
    using assms by simp
  have b: "toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (Eps)))) = \<up>(Eps)"
    unfolding toTsynMsgStream_def by simp
  have a: "tsynLen\<cdot>(\<up>(Eps)) = 0"
    by (simp add: tsynlen_singleton_Eps)

  show "(tsynLen oo toTsynMsgStream)\<cdot>(sb  \<^enum>\<^sub>\<star>  c) = 0"
    by (simp add: a b assms)
qed

lemma tsynsblen_singleton_eps:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
    and "\<exists> c::'cs::tsynchan. sbGetCh c\<cdot>sb = \<up>(Timed (Tsyn (Eps)))"
  shows "tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) = 0"
proof-
  have a:"tsynLenM\<cdot>(\<up>(Timed (Tsyn (Eps)))) = 0" 
    by (metis assms(2) tsynlenm_singleton_eps) 
  then have "\<exists> c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) = 0"
    by (metis assms(2))
  show ?thesis 
    using assms
    by (metis a tsynSBlen_le zero_eq)
qed

lemma tsynsblen_sfoot_msg_geq:
  assumes fin:  "#(sbGetCh c\<cdot>sb) < \<infinity>"
      and ne:   "sbGetCh c\<cdot>sb \<noteq> \<epsilon>"
      and foot: "sfoot (toTsynMsgStream\<cdot>(sbGetCh c\<cdot>sb)) = TSynMsg m"
    shows "Fin 1 \<le> tsynLenM\<cdot>(sbGetCh c\<cdot>sb)"
  using assms
proof -
  let ?s = "toTsynMsgStream\<cdot>(sbGetCh c\<cdot>sb)"

  have fin': "#?s < \<infinity>"
    using fin
    by (simp add: toTsynMsgStream_def)

  have ne': "?s \<noteq> \<epsilon>"
    using ne
    apply (simp add: toTsynMsgStream_def)
    by (metis eq_slen_eq_and_less minimal slen_smap strict_smap)

  have "Fin 1 \<le> tsynLen\<cdot>?s"
    using tsynlen_sfoot_msg_geq[OF fin' ne' foot] .

  thus ?thesis
    by (simp add: tsynLenM_def)
qed

lemma tsynlen_sfoot_msg_geq:
  assumes "chDom TYPE('cs::tsynchan) \<noteq> {}"
    and "\<exists> c::'cs::tsynchan. sfoot (toTsynMsgStream\<cdot>(sbGetCh c\<cdot>sb)) = TSynMsg m"
    and "\<forall> c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) \<noteq> Fin 0"
  shows "tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) \<ge> Fin 1"
proof-
  have a1: "tsynSBlen sb \<noteq> Fin 0" 
    using assms tsynSBlen_ruleD(2) by blast
  then have a2: "\<exists> c::'cs::tsynchan. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) \<ge> Fin 1"
    using assms by (metis less_one linorder_le_less_linear lnat_well_h1)
  show ?thesis 
    using assms a1 a2
    by (metis less_one linorder_le_less_linear lnat_well_h1)
qed

lemma tsynLenM_inf_nbot:
  assumes inf: "tsynLenM\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
proof
  assume "s = \<epsilon>"
  hence "tsynLenM\<cdot>s = 0"
    by (simp add: tsynLenM_def toTsynMsgStream_def)
  with inf show False by simp
qed


lemma tsynSBRemDups_to_tsynRemDups:
  "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
     by (metis (no_types, lifting) cfcomp2 tsynSBRemDups.rep_eq sb_rep_abs sbgetch_insert2 tsynSBRemDups_raw_def
        tsynSBRemDups_raw_lsb_well)

lemma totsynmsgstream_strict[simp]: "toTsynMsgStream\<cdot>\<epsilon>=\<epsilon>"
  by (simp add: toTsynMsgStream_def)

lemma tsyntomstream_strict[simp]: "tsynMsgToMStream\<cdot>\<epsilon>=\<epsilon>"
  by (simp add: tsynMsgToMStream_def)
find_theorems toTsynMsgStream

lemma toTsynMsgStream_scons:
  "toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn x))\<Zcat>s) = \<up>x\<Zcat>toTsynMsgStream\<cdot>s"
  unfolding toTsynMsgStream_def
  by (simp)

lemma tsynMsgToMStream_scons:
  "tsynMsgToMStream\<cdot>(\<up>x\<Zcat>s) = \<up>(Timed (Tsyn x))\<Zcat>tsynMsgToMStream\<cdot>s"
  unfolding tsynMsgToMStream_def
  by (simp)

lemma tsynsbremdups_strict[simp]: "tsynSBRemDups\<cdot>\<bottom> = \<bottom>"
  apply (rule sb_eqI)
  apply (simp add: sbgetch_insert2)
  apply (simp add: tsynSBRemDups.rep_eq tsynSBRemDups_raw_def)
  apply (subst Rep_lsb_strict)
  by (simp add: bot_sb tsynRemDups_def sscanlAOne_def)

lemma tsynsbremdups_sup[simp]:
  shows "tsynSBRemDups\<cdot>(sbe2sb (sbe::'cs::{tsynchan}\<^sup>\<surd>)) = sbe2sb sbe"
proof (cases "chDom TYPE('cs) = {}")
  case True
  then show ?thesis
    by (simp)

next
  case False
  then have nonempty_dom: "chDom TYPE('cs) \<noteq> {}" by simp

  show ?thesis
  proof (rule sb_eqI)
    fix c :: "'cs::{tsynchan}"
    assume inside_dom: "Rep c \<in> chDom TYPE('cs)"

    have cTime_Tsyn: "cTime (Rep c) = TTsyn"
      using inside_dom
      by simp

    have ctype_form: "ctype (Rep c) = (Timed \<circ> Tsyn) ` ({\<sim>} \<union> TSynMsg ` cMsg (Rep c))"
      apply (simp add: ctype_def cTime_Tsyn)
      by (simp add: nonempty_dom cMsg_nonempty_tsynchan)

    have sbe_in_ctype: "sbegetch c sbe \<in> ctype (Rep c)"
      by (simp add: nonempty_dom)

    from sbe_in_ctype ctype_form obtain x where
      is_ttsyn:"sbegetch c sbe = Timed (Tsyn x)" and "x \<in> {\<sim>} \<union> TSynMsg ` cMsg (Rep c)"
      by auto

    have sbe_stream: "sbe2sb sbe \<^enum> c = \<up>(Timed (Tsyn x))"
      by (simp add: sbe2sb_getch inside_dom is_ttsyn)

    have tsynSB_stream: "tsynSBRemDups\<cdot>(sbe2sb sbe) \<^enum> c =
                        (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn x)))"
      by (simp add: tsynSBRemDups_to_tsynRemDups sbe_stream)

    also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn x)))))"
      by (simp add: cfcomp1)

    also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>x))"
      by (simp add: toTsynMsgStream_def)

    also have "... = tsynMsgToMStream\<cdot>(\<up>x)"
      apply (cases x)
      by (simp_all add: tsynRemDups_def sscanlAOne_def)

    also have "... = \<up>(Timed (Tsyn x))"
      by (simp add: tsynMsgToMStream_def)

    finally show "tsynSBRemDups\<cdot>(sbe2sb sbe)  \<^enum>  c = sbe2sb sbe  \<^enum>  c"
      by (simp add: sbe_stream)
  qed
qed

lemma tsynsbremdups_unfold:
  "Rep_lsb (tsynSBRemDups\<cdot>sb) =
    (\<lambda>c. tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))))"
  unfolding tsynSBRemDups_raw_def tsynRemDups_def
  by (metis (no_types, opaque_lifting) cfcomp2 sbgetch_insert2 tsynRemDups_def tsynSBRemDups_insert)

lemma tsynSBRemDups_channel_step_init:
  assumes "sb \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>s"
  shows "tsynSBRemDups\<cdot>sb \<^enum> c =
         \<up>(Timed (Tsyn (snd (tsynRemDups_h \<sim> a))))\<Zcat>
         (tsynMsgToMStream oo sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a)) oo toTsynMsgStream)\<cdot>s"
proof -
  have "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)

  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>s)"
    by (simp add: assms)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>s)))"
    by (simp)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>a\<Zcat>toTsynMsgStream\<cdot>s))"
    by (simp add: toTsynMsgStream_scons)

  also have "... = tsynMsgToMStream\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a))\<Zcat>
                    ((sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a)))\<cdot>(toTsynMsgStream\<cdot>s)))"
    by (simp add: tsynRemDups_def tsynremdups_sscanlAOne_step)

  also have "... = \<up>(Timed (Tsyn (snd (tsynRemDups_h \<sim> a))))\<Zcat>
                    tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a)))\<cdot>(toTsynMsgStream\<cdot>s))"
    by (simp add: tsynMsgToMStream_scons)

  also have "... = \<up>(Timed (Tsyn (snd (tsynRemDups_h \<sim> a))))\<Zcat>
                    (tsynMsgToMStream oo sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a)) oo toTsynMsgStream)\<cdot>s"
    by (simp)

  finally show ?thesis .
qed

lemma tsynSBRemDups_eps_stream:
  "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot> (\<up>(Timed (Tsyn \<sim>)) \<Zcat> s) =
    \<up>(Timed (Tsyn \<sim>)) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s"
proof -
  have f1:"toTsynMsgStream\<cdot> (\<up>(Timed (Tsyn \<sim>)) \<Zcat> s) =
        \<up>(\<sim>) \<Zcat> toTsynMsgStream\<cdot>s"
    by (simp add: toTsynMsgStream_def)
  have f2: " tsynRemDups\<cdot>(\<up>(\<sim>) \<Zcat> toTsynMsgStream\<cdot>s) =  \<up>\<sim> \<Zcat> (tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))"
    by (simp add: tsynremdups_sconc_eps)
  have f3: "tsynMsgToMStream\<cdot>( \<up>\<sim> \<Zcat> (tsynRemDups\<cdot>(toTsynMsgStream\<cdot>s))) =  \<up>(Timed (Tsyn \<sim>)) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s "
    by (simp add: tsynMsgToMStream_def)
  then show ?thesis
  apply (simp add: cfun_eq_iff)
    by (simp add: f1 tsynremdups_sconc_eps)
qed

lemma tsynSBRemDups_eps:
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c =  \<up>(Timed (Tsyn \<sim>)) \<Zcat> s"
  assumes "sb2 \<^enum> c = s"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = \<up>(Timed (Tsyn \<sim>)) \<Zcat> tsynSBRemDups\<cdot>sb2 \<^enum> c"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot> (\<up>(Timed (Tsyn \<sim>)) \<Zcat> s)"
    by (simp add: assms(1))
  also have "... =  \<up>(Timed (Tsyn \<sim>)) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>s"
    using tsynSBRemDups_eps_stream by blast
  also have "... =  \<up>(Timed (Tsyn \<sim>)) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb2 \<^enum> c)"
    by (simp add: assms(2))
  also have "... =  \<up>(Timed (Tsyn \<sim>)) \<Zcat> tsynSBRemDups\<cdot>sb2 \<^enum> c"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  finally show ?thesis .
qed


lemma tsynSBRemDups_msg_eq_stream:
  "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> s) =
   (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s)"
proof -
  have f1:"toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> s) =
        \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg a) \<Zcat> toTsynMsgStream\<cdot>s"
    by (simp add: toTsynMsgStream_def)

  have f2: "toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s) =
        \<up>(TSynMsg a) \<Zcat> \<up>\<sim> \<Zcat> toTsynMsgStream\<cdot>s"
    by (simp add: toTsynMsgStream_def)

  then show ?thesis
  apply (simp add: cfun_eq_iff)
  by (simp add: f1 tsynremdups_msg_eq)
qed

lemma tsynSBRemDups_msg_eq:
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> s"
  assumes "sb2 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = tsynSBRemDups\<cdot>sb2 \<^enum> c"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> s)"
    by (simp add: assms(1))
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s)"
  using tsynSBRemDups_msg_eq_stream by blast
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb2 \<^enum> c)"
    by (simp add: assms(2))
  also have "... = tsynSBRemDups\<cdot>sb2 \<^enum> c"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  finally show ?thesis .
qed

lemma tsynremdups_msg_neq:
  "a\<noteq>b \<Longrightarrow> tsynRemDups\<cdot>(\<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> s) = \<up>(TSynMsg a) \<Zcat>  tsynRemDups\<cdot>(\<up>(TSynMsg b) \<Zcat> s)"
  by(simp add: tsynRemDups_def sscanlAOne_def)

lemma tsynSBRemDups_composition_msg_neq:
  assumes "a \<noteq> b"
  shows "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s) =
         \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s)"
proof -
  have a:"toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s) =
        \<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s"
    by (simp add: toTsynMsgStream_def)

  have b:"tsynRemDups\<cdot>(\<up>(TSynMsg a) \<Zcat> \<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s) =
        \<up>(TSynMsg a) \<Zcat> tsynRemDups\<cdot>(\<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s)"
    using assms by (simp add: tsynremdups_msg_neq)

  have c:"tsynMsgToMStream\<cdot>(\<up>(TSynMsg a) \<Zcat> tsynRemDups\<cdot>(\<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s)) =
        \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s))"
    by (simp add: tsynMsgToMStream_def)

  have d:"toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s) = \<up>(TSynMsg b) \<Zcat> toTsynMsgStream\<cdot>s"
    by (simp add: toTsynMsgStream_def)

  then show ?thesis
  by (simp add: a b c)
qed

lemma tsynSBRemDups_msg_neq:
  assumes "a \<noteq> b"
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s"
  assumes "sb2 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> (tsynSBRemDups\<cdot>sb2 \<^enum> c)"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s)"
    by (simp add: assms(2))
  also have "... = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s)"
    using assms(1) tsynSBRemDups_composition_msg_neq by blast
  also have "... = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> (tsynSBRemDups\<cdot>sb2 \<^enum> c)"
    by (simp add: assms(3) tsynSBRemDups_to_tsynRemDups)
  finally show ?thesis .
qed

lemma tsynSBRemDups_msg_eq_2:
  assumes "a = b"
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg b))) \<Zcat> s"
  assumes "sb2 \<^enum> c = \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = tsynSBRemDups\<cdot>sb2 \<^enum> c"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> s)"
    by (simp add: assms(1,2))
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn (TSynMsg a))) \<Zcat> \<up>(Timed (Tsyn \<sim>)) \<Zcat> s)"
  using tsynSBRemDups_msg_eq_stream by blast
  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb2 \<^enum> c)"
    by (simp add: assms(3))
  also have "... = tsynSBRemDups\<cdot>sb2 \<^enum> c"
    by (simp add: tsynSBRemDups_to_tsynRemDups)
  finally show ?thesis .
qed

lemma tf_inverse_tsyn:
  "smap (inv Tsyn \<circ> inv Timed)\<cdot>(smap (Timed \<circ> Tsyn)\<cdot>(x :: msg tsyn stream)) = x"
  unfolding o_def
  apply (simp add: smapsmap2smap)
  by (metis (no_types, lifting) ext comp_apply inj_timed inj_tsyn inv_f_f smap_lambdaid)

lemma tsynSBRemDups_idem: "tsynSBRemDups\<cdot>(tsynSBRemDups\<cdot>(sb::'cs::{tsynchan}\<^sup>\<Omega>)) = tsynSBRemDups\<cdot>sb"
  apply (rule sb_eqI)
  apply (simp add: tsynSBRemDups_to_tsynRemDups)
  apply (simp add: toTsynMsgStream_def tsynMsgToMStream_def tf_inverse_tsyn tsynremdups_idem)
  done

lemma tsynSBRemDups_channel_step:
  assumes "sb \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>s"
  shows "tsynSBRemDups\<cdot>sb \<^enum> c =
         \<up>(Timed (Tsyn a))\<Zcat>
         (tsynMsgToMStream oo sscanlAOne tsynRemDups_h a oo toTsynMsgStream)\<cdot>s"
proof -
  have "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)

  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>s)"
    by (simp add: assms)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>s)))"
    by (simp)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>a\<Zcat>toTsynMsgStream\<cdot>s))"
    by (simp add: toTsynMsgStream_scons)

  also have "... = tsynMsgToMStream\<cdot>(\<up>a\<Zcat>((sscanlAOne tsynRemDups_h a)\<cdot>(toTsynMsgStream\<cdot>s)))"
    by (simp add: tsynremdups_step)

  also have "... = \<up>(Timed (Tsyn a))\<Zcat>tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h a)\<cdot>(toTsynMsgStream\<cdot>s))"
    by (simp add: tsynMsgToMStream_scons)

  also have "... = \<up>(Timed (Tsyn a))\<Zcat>
                    (tsynMsgToMStream oo sscanlAOne tsynRemDups_h a oo toTsynMsgStream)\<cdot>s"
    by (simp)

  finally show ?thesis .
qed

lemma tsynsbremdups_eq3:
  assumes "a = b"
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s"
  assumes "sb2 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>
                    (tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h b)\<cdot>(\<up>\<sim>\<Zcat>toTsynMsgStream\<cdot>s)))"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = sb2 \<^enum> c"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)

  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s)"
    by (simp add: assms(2))

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s)))"
    by (simp add: cfcomp1)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>a\<Zcat>\<up>b\<Zcat>toTsynMsgStream\<cdot>s))"
    by (simp add: toTsynMsgStream_scons)

  also have "... = tsynMsgToMStream\<cdot>(\<up>a\<Zcat>((sscanlAOne tsynRemDups_h b)\<cdot>(\<up>\<sim>\<Zcat>toTsynMsgStream\<cdot>s)))"
    using assms(1) by (simp add: tsynremdups_eq3)

  also have "... = \<up>(Timed (Tsyn a))\<Zcat>tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h b)\<cdot>(\<up>\<sim>\<Zcat>toTsynMsgStream\<cdot>s))"
    by (simp add: tsynMsgToMStream_scons)

  also have "... = sb2 \<^enum> c"
    by (simp add: assms(3))

  finally show ?thesis .
qed

lemma tsynsbremdups_eq4:
  assumes "a = b"
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s"
  assumes "sb2 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn \<sim>))\<Zcat>
                    (tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h b)\<cdot>(toTsynMsgStream\<cdot>s)))"
  shows "tsynSBRemDups\<cdot>sb1 \<^enum> c = sb2 \<^enum> c"
proof -
  have "tsynSBRemDups\<cdot>sb1 \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb1 \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)

  also have "... = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s)"
    by (simp add: assms(2))

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(\<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn b))\<Zcat>s)))"
    by (simp add: cfcomp1)

  also have "... = tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(\<up>a\<Zcat>\<up>b\<Zcat>toTsynMsgStream\<cdot>s))"
    by (simp add: toTsynMsgStream_scons)

  also have "... = tsynMsgToMStream\<cdot>(\<up>a\<Zcat>\<up>\<sim>\<Zcat>((sscanlAOne tsynRemDups_h b)\<cdot>(toTsynMsgStream\<cdot>s)))"
    using assms(1) by (simp add: tsynremdups_eq4)

  also have "... = \<up>(Timed (Tsyn a))\<Zcat>\<up>(Timed (Tsyn \<sim>))\<Zcat>
                  tsynMsgToMStream\<cdot>((sscanlAOne tsynRemDups_h b)\<cdot>(toTsynMsgStream\<cdot>s))"
    by (simp add: tsynMsgToMStream_scons)

  also have "... = sb2 \<^enum> c"
    by (simp add: assms(3))

  finally show ?thesis .
qed

lemma tsynsbremdups_ex:
  assumes "sb1 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>s"
  shows "\<exists>y. tsynSBRemDups\<cdot>sb1 \<^enum> c = \<up>(Timed (Tsyn a))\<Zcat>y"
  by (metis assms sbgetch_insert2 toTsynMsgStream_scons tsynMsgToMStream_scons tsynremdups_step tsynsbremdups_unfold)

lemma tsynMsgToMStream_toTsynMsgStream_inverse:
  "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(x :: msg tsyn stream)) = x"
  unfolding toTsynMsgStream_def tsynMsgToMStream_def
  by (simp add: tf_inverse_tsyn)

lemma tsynchan_ctype_form:
  fixes c :: "'cs::{tsynchan}"
  assumes "Rep c \<in> chDom TYPE('cs)"
  shows "ctype (Rep c) = (if cMsg (Rep c) = {} then {}
                         else (Timed \<circ> Tsyn) ` ({\<sim>} \<union> TSynMsg ` cMsg (Rep c)))"
proof -
  have cTime_Tsyn: "cTime (Rep c) = TTsyn"
    using assms by simp

  show ?thesis
    by (simp add: ctype_def cTime_Tsyn)
qed

lemma tsynchan_stream_first_element:
  fixes sb :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "chDom TYPE('cs) \<noteq> {}"
  assumes "Rep c \<in> chDom TYPE('cs)"
  assumes "sb \<^enum> c \<noteq> \<epsilon>"
  obtains x s where "sb \<^enum> c = \<up>(Timed (Tsyn x))\<Zcat>s"
proof -
  from assms(3) obtain m s' where stream_eq: "sb \<^enum> c = \<up>m\<Zcat>s'"
    by (metis scases)

  have cTime_Tsyn: "cTime (Rep c) = TTsyn"
    using assms(2) by simp

  have ctype_form: "ctype (Rep c) = (Timed \<circ> Tsyn) ` ({\<sim>} \<union> TSynMsg ` cMsg (Rep c))"
    apply (simp add: ctype_def cTime_Tsyn)
    by (simp add: assms(1) cMsg_nonempty_tsynchan)

  have m_in_ctype: "m \<in> ctype (Rep c)"
    using assms(2) sbgetch_ctypewell stream_eq
    by (metis insert_is_Un insert_subset sValues2un)

  from m_in_ctype ctype_form obtain x where
    "m = Timed (Tsyn x)" and "x \<in> {\<sim>} \<union> TSynMsg ` cMsg (Rep c)"
    by auto

  with stream_eq show ?thesis
    using that by blast
qed

lemma tsyn_channel_conversion_inverse:
  assumes "Rep c \<in> chDom TYPE('cs::{tsynchan})"
  shows "tsynMsgToMStream\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c)) = sb \<^enum> c"
proof -

  have cTime_Tsyn: "cTime (Rep c) = TTsyn"
    by (metis assms(1) rep_reduction tsynchan_ctime)

  have ctype_form: "ctype (Rep c) = (Timed \<circ> Tsyn) ` ({\<sim>} \<union> TSynMsg ` cMsg (Rep c))"
    by (metis assms(1) cdom_notempty cempty_rule dom2ctypenempty rep_reduction tsynchan_ctype_form)

  have elem_form: "\<forall>m \<in> sValues\<cdot>(sb \<^enum> c). \<exists>x. m = Timed (Tsyn x)"
  proof
    fix m
    assume inv: "m \<in> sValues\<cdot>(sb \<^enum> c)"
    have "m \<in> ctype (Rep c)"
      using inv sbgetch_ctypewell by blast
    with assms show "\<exists>x. m = Timed (Tsyn x)"
      using cTime_Tsyn ttsyn_ex by blast
  qed

  have func_eq: "\<And>m. m \<in> sValues\<cdot>(sb \<^enum> c) \<Longrightarrow> (Timed \<circ> Tsyn \<circ> (inv Tsyn \<circ> inv Timed)) m = id m"
  proof -
    fix m
    assume "m \<in> sValues\<cdot>(sb \<^enum> c)"
    with elem_form obtain x where "m = Timed (Tsyn x)"
      by blast
    then have "(Timed \<circ> Tsyn \<circ> (inv Tsyn \<circ> inv Timed)) m = m"
      by simp
    then show "(Timed \<circ> Tsyn \<circ> (inv Tsyn \<circ> inv Timed)) m = id m"
      by simp
  qed

  show ?thesis
    unfolding toTsynMsgStream_def tsynMsgToMStream_def
    by (metis (no_types) comp_def func_eq id_def npsmap_well rangeI subsetI tf_inverse_tsyn)
qed

lemma tsynSBRemDups_prefix_neq:
  fixes sb1 sb2 :: "'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "chDom TYPE('cs) \<noteq> {}"
  and "sb1 \<sqsubseteq> sb2"
  and "tsynSBRemDups\<cdot>sb1 \<noteq> sb1"
  shows "tsynSBRemDups\<cdot>sb2 \<noteq> sb2"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence eq: "tsynSBRemDups\<cdot>sb2 = sb2" by simp

  from \<open>tsynSBRemDups\<cdot>sb1 \<noteq> sb1\<close> obtain c where
    neq: "tsynSBRemDups\<cdot>sb1 \<^enum> c \<noteq> sb1 \<^enum> c"
    by (metis sb_eqI)

  have c_in_dom: "Rep c \<in> chDom TYPE('cs)"
    by (simp add: assms(1))

  let ?f = "tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream"
  let ?x = "sb1 \<^enum> c"
  let ?y = "sb2 \<^enum> c"

  have f_neq: "?f\<cdot>?x \<noteq> ?x"
    by (metis neq tsynSBRemDups_to_tsynRemDups)

  have prefix: "?x \<sqsubseteq> ?y"
    by (simp add: assms(2) monofun_cfun_arg)

  have conv_inv_x: "tsynMsgToMStream\<cdot>(toTsynMsgStream\<cdot>?x) = ?x"
    using c_in_dom tsyn_channel_conversion_inverse by blast

  have conv_inv_y: "tsynMsgToMStream\<cdot>(toTsynMsgStream\<cdot>?y) = ?y"
    using c_in_dom tsyn_channel_conversion_inverse by blast

  let ?x_tsyn = "toTsynMsgStream\<cdot>?x"
  let ?y_tsyn = "toTsynMsgStream\<cdot>?y"

  have tsyn_prefix: "?x_tsyn \<sqsubseteq> ?y_tsyn"
    by (simp add: monofun_cfun_arg prefix)

  have tsyn_neq: "tsynRemDups\<cdot>?x_tsyn \<noteq> ?x_tsyn"
  proof
    assume "tsynRemDups\<cdot>?x_tsyn = ?x_tsyn"
    then have "tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>?x_tsyn) = tsynMsgToMStream\<cdot>?x_tsyn"
      by simp
    hence "?f\<cdot>?x = tsynMsgToMStream\<cdot>?x_tsyn"
      by (simp add: cfcomp1)
    also have "... = ?x"
      by (simp add: conv_inv_x)
    finally have "?f\<cdot>?x = ?x" .
    with f_neq show False by simp
  qed

  have "tsynRemDups\<cdot>?y_tsyn \<noteq> ?y_tsyn"
    using tsyn_prefix tsyn_neq tsynremdups_prefix_neq by blast

  have f_neq_y: "?f\<cdot>?y \<noteq> ?y"
  proof
    assume "?f\<cdot>?y = ?y"
    then have "tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>?y_tsyn) = ?y"
      by (simp add: cfcomp1)
    also have "... = tsynMsgToMStream\<cdot>?y_tsyn"
      by (simp add: conv_inv_y)
    finally have eq1: "tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>?y_tsyn) = tsynMsgToMStream\<cdot>?y_tsyn" .

    have "toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>?y_tsyn)) =
          toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>?y_tsyn)"
      by (simp add: eq1)

    from \<open>toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>?y_tsyn)) = toTsynMsgStream\<cdot>(tsynMsgToMStream\<cdot>?y_tsyn)\<close>
    have "tsynRemDups\<cdot>?y_tsyn = ?y_tsyn"
      by (metis tsynMsgToMStream_toTsynMsgStream_inverse)

    with \<open>tsynRemDups\<cdot>?y_tsyn \<noteq> ?y_tsyn\<close> show False by simp
  qed

  have "tsynSBRemDups\<cdot>sb2 \<^enum> c \<noteq> sb2 \<^enum> c"
    by (metis f_neq_y tsynSBRemDups_to_tsynRemDups)

  with eq have "sb2 \<^enum> c \<noteq> sb2 \<^enum> c" by simp
  thus False by simp
qed

lemma tsynRemDups_sValues_se_h:
  "sValues\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>s) \<subseteq> sValues\<cdot>(tsynRemDups\<cdot>s) \<union> {\<sim>}"
proof -
  have tsyn_def: "tsynRemDups\<cdot>s = sscanlAOne tsynRemDups_h \<sim>\<cdot>s"
    by (simp add: tsynRemDups_def)
  
  show ?thesis
  proof (induction s arbitrary: state)
    case adm
    then show ?case
      unfolding subset_iff
      apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
      using adm_cmp apply force 
      apply (simp add: SetPcpo.adm_in2)
      proof-
          fix t :: "'a tsyn"
          show "adm (\<lambda>x::'a tsyn stream. t = \<sim> \<or> t \<in> sValues\<cdot>(tsynRemDups\<cdot>x))"
          proof (cases "t = \<sim>")
            case True
            then show ?thesis
              by simp
          next
            case False
            then show ?thesis
              apply (simp add: SetPcpo.adm_in2)
              using adm_cmp adm_in2 by fastforce
          qed
      qed
  next
    case bottom
      have sscanl_eps: "sscanlAOne tsynRemDups_h state\<cdot>\<epsilon> = \<epsilon>" unfolding sscanlAOne_def
        by simp
      
      have tsyn_eps: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"  unfolding tsynRemDups_def sscanlAOne_def
        by (simp add: tsynRemDups_def)
      
      have svalues_eps: "sValues\<cdot>\<epsilon> = {}"
        by (simp add:)

    then show ?case
      by (simp add: sscanl_eps) 
  next
    case (step a s)
      have step_eq1: "sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s) = 
            sup' (snd (tsynRemDups_h state a)) \<Zcat>\<Zcat> 
            sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s"
        by (simp add: sscanlaone_step)
      
      have step_eq2: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
            sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat>\<Zcat> 
            sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
        by (simp add: tsynRemDups_def sscanlaone_step)
      
      have svalues_conc1: "sValues\<cdot>(sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s)) = 
            sValues\<cdot>(sup' (snd (tsynRemDups_h state a))) \<union> 
            sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s)"
        by (simp add: sscanlaone_step)


      then show ?case 
        apply (cases a; auto)
        apply (metis (no_types, lifting) Un_commute
            conc_stream_def fst_eqD
            tsynRemDups_h.simps(1)
            insert_is_Un insert_subset
            mk_disjoint_insert snd_eqD srcdups_dom
            srcdups_dom_h step step_eq2
            tsynRemDups_def)
        using step_eq2 apply fastforce
        using step_eq2 apply auto[1]
        using step_eq2 by force  
    qed
  qed

lemma tsynRemDups_sValues_se:
  "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq>  sValues\<cdot>s \<union> {\<sim>} " 
proof (induction s )
  case adm
  then show ?case 
    apply auto 
    unfolding subset_iff
      apply (intro adm_all adm_imp SetPcpo.adm_in2 Cpo.adm_const)
    using adm_cmp apply force
    apply (simp add: SetPcpo.adm_in2)
    done
next
  case bottom
  then show ?case unfolding tsynRemDups_def sscanlAOne_def by simp
next
  case (step a s)
    have step_eq: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat>\<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
      by (simp add: tsynRemDups_def sscanlaone_step) 
    
    have svalues_conc: "sValues\<cdot>(tsynRemDups\<cdot>(\<up>a \<Zcat> s)) = 
          sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<union> 
          sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s)"
      by (simp add: step_eq)
    
    
    have part2: "sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>s" using step tsynRemDups_sValues_se_h
      by blast 
    
    have "sValues\<cdot>s \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s)"
      by (auto)
    then have part2': "sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
      using part2 by blast
    

      have step_eq: "tsynRemDups\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h \<sim> a)) \<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s"
        by (simp add: tsynRemDups_def sscanlaone_step)  

      have step_eq2: "sscanlAOne tsynRemDups_h state\<cdot>(\<up>a \<Zcat> s) = 
          sup' (snd (tsynRemDups_h state a)) \<Zcat>\<Zcat> 
          sscanlAOne tsynRemDups_h (fst (tsynRemDups_h state a))\<cdot>s"
      by (simp add: sscanlaone_step)

    have part1: "sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
    proof -
      have "snd (tsynRemDups_h \<sim> a) \<in> {a, \<sim>}"
        by (cases a) (auto)
      then have "sValues\<cdot>(sup' (snd (tsynRemDups_h \<sim> a))) \<subseteq> {a, \<sim>}"
        by simp
      also have "{a, \<sim>} \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
        by simp
      finally show ?thesis .
    qed
    
    have part2: "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>s"
      using step by auto
    
    have "sValues\<cdot>s \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s)"
      by auto
    then have part2': "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq> {\<sim>} \<union> sValues\<cdot>(\<up>a \<Zcat> s)"
      using part2 by blast

    have "sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a)))\<union> sValues\<cdot>(sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s) =
           sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a)) \<Zcat> sscanlAOne tsynRemDups_h (fst (tsynRemDups_h \<sim> a))\<cdot>s)"
      by auto

    have "sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> a))) \<subseteq> sValues\<cdot>(\<up>a \<Zcat> s) \<union> {\<sim>}"
      using part1 by blast

    have " sValues\<cdot>(tsynRemDups\<cdot>(s::'a tsyn stream)) \<subseteq> sValues\<cdot>s \<union> {\<sim>}"
      using step by blast 

    show ?case 
      apply (subst step_eq)
      using
        \<open>sValues\<cdot>(\<up>(snd (tsynRemDups_h \<sim> (a::'a tsyn)))) \<subseteq> sValues\<cdot>(\<up>a \<Zcat> (s::'a tsyn stream)) \<union> {\<sim>}\<close>
        part2 tsynRemDups_sValues_se_h
      by fastforce
      
  qed

lemma tsynSBRemDups_getCh: "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
  by (metis (no_types, lifting) cfcomp2 tsynSBRemDups.rep_eq sb_rep_abs sbgetch_insert2 tsynSBRemDups_raw_def
          tsynSBRemDups_raw_lsb_well)

lemma tsynMsgToMStream_tsynRemDup_toTsynMsgStream:
  assumes "inj f"
  shows "tsynMsgToMStream\<cdot>(\<alpha>\<^sub>-(toTsynMsgStream\<cdot>(smap (Timed \<circ> Tsyn \<circ> map_tsyn f)\<cdot>s))) 
      = smap (Timed \<circ> Tsyn \<circ> map_tsyn f)\<cdot>(\<alpha>\<^sub>-s)"
  apply(simp add: toTsynMsgStream_smap_Timed_Tsyn_f)
  apply(simp add: assms tsynRemDups_smap[symmetric] tsyn.inj_map)
  by (simp add: smapsmap2smap tsynMsgToMStream_def)


lemma tsynsbremdups_tsynsblen_ex:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "\<exists>c. tsynLenM\<cdot>(tsynMsgToMStream\<cdot>(\<alpha>\<^sub>-(toTsynMsgStream\<cdot>(sb \<^enum> c)))) = tsynSBlen (tsynSBRemDups\<cdot>(sb))"
proof-

  obtain c where c_def: "tsynLenM\<cdot>(tsynSBRemDups\<cdot>(sb)  \<^enum>  c) = tsynSBlen (tsynSBRemDups\<cdot>(sb))"
    using assms tsynSBlen_ruleD(2) by blast

  have eq: "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c) = (tsynSBRemDups\<cdot>(sb) \<^enum> c)"
    using tsynSBRemDups_getCh[symmetric] by blast

  show ?thesis
    apply(rule_tac x=c in exI)
    by(simp add: eq[simplified] c_def)
qed



lemma tsynSBRemDups_is_lifted: "is_lifted_tsyn_stream_fn tsynSBRemDups tsynRemDups"
  apply(simp add: is_lifted_tsyn_stream_fn_def is_lifted_stream_fn_def)
  by (metis cfcomp2 tsynSBRemDups_getCh)

lemma toTsynMsgStream_neq_bot: "s \<noteq> \<epsilon> \<Longrightarrow> toTsynMsgStream\<cdot>s \<noteq> \<epsilon>"
  unfolding toTsynMsgStream_def
  by (rule smap_neq_bot)

lemma tsynsbremdups_nbot:
  assumes "sb \<noteq> \<bottom>"
  shows "tsynSBRemDups\<cdot>sb \<noteq> \<bottom>"
proof
  assume bebot: "tsynSBRemDups\<cdot>sb = \<bottom>"

  from assms obtain c where
    nonempty: "sb \<^enum> c \<noteq> \<epsilon>"
    using sbbot_getch by blast

  have "tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)"
    by (simp add: tsynSBRemDups_to_tsynRemDups)

  have "(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c) \<noteq> \<epsilon>"
  proof -

    have notbot:"toTsynMsgStream\<cdot>(sb \<^enum> c) \<noteq> \<bottom>"
      by (simp add: nonempty toTsynMsgStream_neq_bot)

    then have "tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c)) \<noteq> \<bottom>"
      by (simp add: notbot tsynremdups_nbot)

    then have "tsynMsgToMStream\<cdot>(tsynRemDups\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))) \<noteq> \<epsilon>"
      by (metis tsynMsgToMStream_toTsynMsgStream_inverse tsyntomstream_strict)

    then show ?thesis
      by (metis bebot sbbot_getch sbgetch_insert2 tsynsbremdups_unfold)
  qed

  with \<open>tsynSBRemDups\<cdot>sb = \<bottom>\<close> have "tsynSBRemDups\<cdot>sb \<^enum> c = \<epsilon>"
    by simp

  thus False
    using \<open>tsynSBRemDups\<cdot>sb \<^enum> c = (tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c)\<close>
          \<open>(tsynMsgToMStream oo tsynRemDups oo toTsynMsgStream)\<cdot>(sb \<^enum> c) \<noteq> \<epsilon>\<close>
    by simp
qed


lemma is_lifted_stream_fn_apply: "is_lifted_stream_fn sbFn sFn \<Longrightarrow> (sbFn\<cdot>sb) \<^enum> c = sFn\<cdot>(sb \<^enum> c)"
  by(simp add: is_lifted_stream_fn_def)

lemma is_lifted_stream_fn_conc:
  assumes "is_lifted_stream_fn F f"
      and "is_lifted_stream_fn G g"
    shows "is_lifted_stream_fn (F oo G) (f oo g)"
  using assms by(auto simp add: is_lifted_stream_fn_def)

lemma is_lifted_tsyn_stream_fn_conc:
  assumes "is_lifted_tsyn_stream_fn F f"
      and "is_lifted_tsyn_stream_fn G g"
    shows "is_lifted_tsyn_stream_fn (F oo G) (f oo g)"
proof-
  have 1: "is_lifted_stream_fn F (tsynMsgToMStream oo f oo toTsynMsgStream)"
    using assms(1) is_lifted_tsyn_stream_fn_def by blast
  have 2: "is_lifted_stream_fn G (tsynMsgToMStream oo g oo toTsynMsgStream)"
    using assms(2) is_lifted_tsyn_stream_fn_def by blast

  show ?thesis
    apply(subst is_lifted_tsyn_stream_fn_def)
    apply(insert is_lifted_stream_fn_conc[OF 1 2])
    by (simp add: oo_def tsynMsgToMStream_def toTsynMsgStream_def smaps2smap)
qed

theorem tsynSBlen_rule_liftedSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "M stream \<rightarrow> M stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c))"
      and "\<exists>c. tsynLenM\<cdot>(f\<cdot>(sb \<^enum> c)) = k"
      and "is_lifted_stream_fn F f"
    shows "tsynSBlen (F\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
    apply(simp add: assms)
   apply(insert is_lifted_stream_fn_apply[OF assms(4)])
  using assms(2) apply presburger
  apply(insert is_lifted_stream_fn_apply[OF assms(4)])
  using assms(3) by presburger

theorem tsynSBlen_rule_liftedTsynSpf:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
    and f:: "msg tsyn stream \<rightarrow> msg tsyn stream"
  assumes "\<not>chDomEmpty TYPE('cs)" 
      and "\<And>c. k \<le> tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c)))"
      and "\<exists>c. tsynLen\<cdot>(f\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> c))) = k"
      and "is_lifted_tsyn_stream_fn F f"
    shows "tsynSBlen (F\<cdot>sb) = k"
  apply(rule tsynSBlen_rule)
    apply(simp add: assms)
   apply(insert is_lifted_stream_fn_apply[OF assms(4)[simplified is_lifted_tsyn_stream_fn_def]])
   apply (simp add: assms(2) tsynLenM_def)
  apply(insert is_lifted_stream_fn_apply[OF assms(4)[simplified is_lifted_tsyn_stream_fn_def]])
  by (metis assms(3) cfcomp2 toTsynMsgStream_tsynMsgToMStream_id tsynLenM_def)



definition tsynSBBoolFilter_raw :: "'cs::{tsynchan}\<^sup>\<Omega> \<Rightarrow> ('cs \<Rightarrow> bool stream) \<rightarrow> 'cs\<^sup>\<Omega>" where
  "tsynSBBoolFilter_raw \<equiv> \<lambda>sb. \<Lambda> f. Abs_lsb (\<lambda>c. (tsynMsgToMStream oo (\<Lambda> s. tsynBoolFilter\<cdot>s\<cdot>(f c)) oo toTsynMsgStream)\<cdot>(sb\<^enum>c))"

lemma
  tsynsbboolfilter_well_pre:
  assumes "sValues\<cdot>s \<subseteq> Timed ` Tsyn ` UNIV"
  shows "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> sValues\<cdot>(s) \<union> {Timed (Tsyn \<sim>)}"
proof-
  have "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> Timed ` Tsyn ` (sValues\<cdot>(toTsynMsgStream\<cdot>(s)) \<union> {\<sim>})"
    by (meson dual_order.trans subset_image_iff tsynboolfilter_subset tsynmsgtomstream_svalues)
  then have 1: "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(s))\<cdot>y)) \<subseteq> (Timed ` Tsyn ` sValues\<cdot>(toTsynMsgStream\<cdot>(s))) \<union> {Timed (Tsyn \<sim>)}"
    by blast

  have 2: "Timed ` Tsyn ` sValues\<cdot>(toTsynMsgStream\<cdot>s) \<subseteq> sValues\<cdot>s"
    using assms by(auto simp add: toTsynMsgStream_def  smap_sValues image_def)

  show ?thesis
    using "1" "2" by blast
qed


lemma tsynsbboolfilter_well:
  "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>((x :: 'cs::{tsynchan}\<^sup>\<Omega>)  \<^enum>  c))\<cdot>y)) \<subseteq> ctype (Rep c)"
proof (cases "chDomEmpty TYPE('cs)")
  case c: True
  then have "x  \<^enum>  c = \<epsilon>"
    by simp
  then have "sValues\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(x  \<^enum>  c))\<cdot>y)) = {}"
    by (metis strict_smap toTsynMsgStream_def tsynMsgToMStream_def tsynboolfilter_strict(3) svalues_eps)
  then show ?thesis
    by blast
next
  case c: False
  then have "ctype (Rep c) = (Timed o Tsyn) ` ({Eps} \<union> (TSynMsg ` (cMsg (Rep c))))"
    by (simp add: cMsg_nonempty_tsynchan ctype_def)
  then show ?thesis
    by (meson Eps_ctype_Rep_c c Un_least order.trans sbgetch_ctypewell tsynchan_svalues tsynsbboolfilter_well_pre)
qed

lift_definition tsynSBBoolFilter :: "'cs::{tsynchan}\<^sup>\<Omega> \<rightarrow> ('cs \<Rightarrow> bool stream) \<rightarrow> 'cs\<^sup>\<Omega>" is
  "tsynSBBoolFilter_raw"
  apply(simp add: tsynSBBoolFilter_raw_def)
  apply(intro cont2cont)
  apply(simp add: lsb_well_def)
  by(simp add: tsynsbboolfilter_well)

lemma tsynsbboolfilter_getch:
  "tsynSBBoolFilter\<cdot>sb\<cdot>oraf \<^enum> c = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  c))\<cdot>(oraf c))"
  apply(simp add: tsynSBBoolFilter_def tsynSBBoolFilter_raw_def)
  apply(subst beta_cfun, intro cont2cont, simp add: lsb_well_def tsynsbboolfilter_well)+
  apply(subst sbgetch_insert2, subst sb_rep_abs, rule lsbwellI, rule tsynsbboolfilter_well)
  ..

lemma
  tsynsbboolfilter_insert:
  assumes "\<And>c. sbo \<^enum> c = tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb \<^enum> (cf c)))\<cdot>(oraf (cf c)))"
    and "\<And>c. ctype (Rep (cf c)) \<subseteq> ctype (Rep c)"  
  shows "sbo = sbRenameCh cf\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)"
  by (metis assms(1,2) sb_eqI sbrenamech_getch tsynsbboolfilter_getch)


lemma tsynsblen_tsynlenm_leq: "tsynLenM\<cdot>(tsynMsgToMStream\<cdot>(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>s)\<cdot>ora)) \<le> tsynLenM\<cdot>s"
  apply(simp add: tsynLenM_def)
  apply(insert tsynlen_boolfilter[of "toTsynMsgStream\<cdot>s" ora])
  by (metis toTsynMsgStream_smap_Timed_Tsyn tsynMsgToMStream_def)


lemma tsynsbboolfilter_live:
  assumes "tsynSBlen (sb :: 'cs::{tsynchan}\<^sup>\<Omega>) = \<infinity>"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>oraf) = (LEAST n . n\<in>{(#({True} \<ominus> oraf c)) | c . True})"
  apply(insert tsynSBlen_infty[of sb], simp add: assms)
  apply(subst tsynSBlen_rule)
     apply (auto simp add: tsynsbboolfilter_getch)
    apply(simp_all add: tsynLenM_def tsynMsgToMStream_def toTsynMsgStream_smap_Timed_Tsyn)
  apply (smt Least_le)
  by (smt LeastI_ex)


lemma tsynsbboolfilter_live_single:
  assumes "tsynSBlen (sb :: 'cs::{tsynchan}\<^sup>\<Omega>) = \<infinity>"
    and "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>_.ora)) = #({True} \<ominus> ora)"
  by (smt LeastI_ex assms mem_Collect_eq tsynsbboolfilter_live)


lemma tsynsbboolfilter_live_single_rename:
  fixes sb :: "'ca::{tsynchan}\<^sup>\<Omega>"
    and cf :: "'cb::{tsynchan} \<Rightarrow> 'ca"
  assumes "tsynSBlen sb = \<infinity>"
    and "\<not>chDomEmpty TYPE('ca)"
    and "\<not>chDomEmpty TYPE('cb::{tsynchan})"
    and "\<And>c. ctype (Rep (cf c)) \<subseteq> ctype (Rep c)"
  shows "tsynSBlen (sbRenameCh cf\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>_.ora))) = #({True} \<ominus> ora)"
  apply(subst tsynsbboolfilter_live_single[OF assms(1,2), symmetric])
  apply(rule tsynSBlen_rule)
    apply(simp add: assms(3))
   apply (metis assms(2,4) sbrenamech_getch tsynSBlen_le)
proof -
  have "\<forall>c. tsynLenM\<cdot> (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora) \<^enum> c) = #({True} \<ominus> ora)"
    by (metis (lifting) assms(1,2) cfcomp2 toTsynMsgStream_smap_Timed_Tsyn tsynLenM_def tsynMsgToMStream_def tsynSBlen_infty tsynboolfilter_live tsynsbboolfilter_getch)
  then show "\<exists>c. tsynLenM\<cdot> (sbRenameCh cf\<cdot> (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora)) \<^enum> c) = tsynSBlen (tsynSBBoolFilter\<cdot>sb\<cdot>(\<lambda>c. ora))"
    by (metis (no_types) assms(2,4) dual_order.eq_iff sbrenamech_getch tsynSBlen_rule)
qed


lemma tsynsblen_inf_nbot:
  assumes "tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) = \<infinity>" 
    and "chDom TYPE('cs::{tsynchan}) \<noteq> {}" 
  shows "sb \<noteq> \<bottom>"
proof
  have a: "\<forall> c. tsynLenM\<cdot>(sbGetCh (c::'cs::{tsynchan})\<cdot>sb) = \<infinity>"
    using tsynSBlen_infty assms 
    by blast
  then have "\<exists>c::'cs::{tsynchan}. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) = 0 \<Longrightarrow> False"
    by (simp add: assms(1,2) tsynSBlen_infty)
  then have "\<exists>c::'cs::{tsynchan}. tsynSBlen sb = 0 \<Longrightarrow> False"
    using Inf'_neq_0_rev assms(1) by presburger
  thus " sb = \<bottom> \<Longrightarrow> False"
    using a tsynLenM_inf_nbot 
    by (meson sbbot_getch)
qed

lift_definition sbInfTimes :: "'cs::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cs::{tsynchan}\<^sup>\<Omega>"  is
  "\<lambda> sb. (\<lambda>c. (sb \<^enum> c)\<^sup>\<infinity>)"
  apply(auto simp add: lsb_well_def)
  done

lemma tsynLenM_sinftimes_inf:
  assumes fin: "#s < \<infinity>"
      and pos: "tsynLenM\<cdot>s \<noteq> 0"
    shows "tsynLenM\<cdot>(s\<^sup>\<infinity>) = \<infinity>"
  unfolding tsynLenM_def toTsynMsgStream_def using assms tsynlen_inftimes_finite
  by (metis (no_types, lifting) cfcomp2 linorder_less_linear lnat_le_zero lnzero_def slen_smap smap2sinf toTsynMsgStream_def
      tsynLenM_def)

lemma tsynsblen_inftimes_finite:
  assumes nz: "0 \<noteq> tsynSBlen sb" and "#sb < \<infinity>" and "\<And> c::'cs. #(sbGetCh c\<cdot>sb) < \<infinity>"
  shows "tsynSBlen (sbInfTimes (sb::'cs::{tsynchan}\<^sup>\<Omega>)) = \<infinity>"
proof (cases "chDomEmpty TYPE('cs::{tsynchan})")
  case True
  then show ?thesis
    unfolding tsynSBlen_def by simp
next
  case False
  have a1: "\<And>c::'cs. tsynLenM\<cdot>(sbGetCh c\<cdot>sb) \<noteq> 0"
  proof-
    fix c :: 'cs
    have lb: "tsynSBlen sb \<le> tsynLenM\<cdot>(sbGetCh c\<cdot>sb)"
      using tsynSBlen_ruleD(1)[OF False] by simp
    show "tsynLenM\<cdot>(sbGetCh c\<cdot>sb) \<noteq> 0"
    proof
      assume z: "tsynLenM\<cdot>(sbGetCh c\<cdot>sb) = 0"
      then have "tsynSBlen sb \<le> 0"
        using lb by simp
      hence "tsynSBlen sb = 0"
        by (cases "tsynSBlen sb") auto
      thus False using nz by simp
    qed
  qed

  have ch_fin: "\<And>c::'cs. #(sbGetCh c\<cdot>sb) < \<infinity>"
    using assms by simp

  have inf_each: "\<And>c::'cs. tsynLenM\<cdot>(sbGetCh c\<cdot>(sbInfTimes sb)) = \<infinity>"
  proof -
    fix c :: 'cs
    have get: "sbGetCh c\<cdot>(sbInfTimes sb) = (sbGetCh c\<cdot>sb)\<^sup>\<infinity>"
      unfolding sbInfTimes_def
      by (metis (mono_tags, lifting) sbInfTimes.rep_eq sbInfTimes_def sbgetch_insert2)
    then show "tsynLenM\<cdot>(sbGetCh c\<cdot>(sbInfTimes sb)) = \<infinity>"
      unfolding tsynLenM_def 
      using assms ch_fin tsynLenM_sinftimes_inf 
      by (metis a1 tsynLenM_def)
  qed

  have set_eq: "{tsynLenM\<cdot>(sbGetCh c\<cdot>(sbInfTimes sb)) | c::'cs. True} = {\<infinity>}"
    using inf_each by auto

  show ?thesis
    unfolding tsynSBlen_def
    using False set_eq
    by (metis (no_types, lifting) Least1I inf_ub singleton_iff)
qed

lemma tsynsblen2nEps:
  assumes "tsynSBlen sb > 0"
    and "chDom TYPE('cs::tsynchan) \<noteq> {}"
  shows "(sb::'cs::{tsynchan}\<^sup>\<Omega>) \<noteq> \<bottom>"
  unfolding tsynSBlen_def using assms 
  by (metis order_less_imp_not_less tsynsblen_strict)

lemma tsynsblen_not_inf_eq_inf:" \<not> tsynSBlen (sb::'cs::{tsynchan}\<^sup>\<Omega>) < \<infinity> \<Longrightarrow> tsynSBlen sb = \<infinity>"
  using inf_great linorder_less_linear by blast

lemma tsynlenm_inf_lub: "chain Y \<Longrightarrow> tsynLenM\<cdot>(Y i) = \<infinity> \<Longrightarrow> tsynLenM\<cdot>(\<Squnion>i. Y i) = \<infinity>"
  by (metis below_antisym inf_ub is_ub_thelub lnle_def monofun_cfun_arg)

lemma tsynsblen_inf_lub:
  fixes Y ::"nat \<Rightarrow>'cs::{tsynchan}\<^sup>\<Omega>"
  assumes dom: "chDom TYPE('cs::tsynchan) \<noteq> {}"
  shows "chain Y \<Longrightarrow> tsynSBlen (Y i) = \<infinity> \<Longrightarrow> tsynSBlen (\<Squnion>i. Y i) = \<infinity>"
proof -
  assume ch: "chain Y" and infi: "tsynSBlen (Y i) = \<infinity>"
  have ne: "\<not> chDomEmpty TYPE('cs)" using dom by simp

  have infYi: "\<forall>c. tsynLenM\<cdot>((Y i) \<^enum> c) = \<infinity>"
    using tsynSBlen_infty assms infi by blast

  have Yi_le: "Y i \<sqsubseteq> (\<Squnion>j. Y j)"
    using ch 
    by (simp add: is_ub_thelub)

  have infLub: "\<forall>c. tsynLenM\<cdot>((\<Squnion>j. Y j) \<^enum> c) = \<infinity>"
    using infYi Yi_le tsynlenm_inf_lub
    by (metis inf_less_eq lnle_def monofun_cfun_arg)

  show "tsynSBlen (\<Squnion>j. Y j) = \<infinity>"
    unfolding tsynSBlen_def using ne infLub
    by (metis tsynSBlen_def tsynSBlen_ruleD(2))
qed

lemma
  tsynsblen_tsynsbremdups_tsynsbboolfilter_leq:
  fixes sb::"'cs::{tsynchan}\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('cs)"
  shows "tsynSBlen (tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>(sb)\<cdot>(oraf))) \<le> tsynSBlen (tsynSBRemDups\<cdot>sb)"
proof-

  obtain ca where ca: "\<And>c. tsynLenM\<cdot>(tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)  \<^enum>  ca) \<le> tsynLenM\<cdot>(tsynSBRemDups\<cdot>(tsynSBBoolFilter\<cdot>sb\<cdot>oraf)  \<^enum>  c)"
    by (metis assms tsynSBlen_le tsynSBlen_ruleD(2))

  obtain cb where cb: "\<And>c. tsynLenM\<cdot>(tsynSBRemDups\<cdot>sb  \<^enum>  cb) \<le> tsynLenM\<cdot>(tsynSBRemDups\<cdot>sb  \<^enum>  c)"
    by (metis assms tsynSBlen_ruleD(1,2))

  show ?thesis
    apply(rule tsynSBlen_le_rule[of ca _ cb])
        apply(auto simp add: assms ca cb)
    apply(auto simp add: tsynSBRemDups_getCh tsynsbboolfilter_getch tsynLenM_def)
    apply (cases "#\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  ca))\<cdot>(oraf ca))) \<le> #\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>(toTsynMsgStream\<cdot>(sb  \<^enum>  cb))\<cdot>(oraf cb)))")
    using trans_lnle tsynlen_remdups_boolfilter_leq apply blast
    by (metis (no_types, lifting) ca cfcomp2 toTsynMsgStream_tsynMsgToMStream_id tsynLenM_def tsynSBRemDups_getCh tsynsbboolfilter_getch)
qed

end

