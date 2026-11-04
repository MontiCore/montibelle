theory SBFin
  imports SB
begin

declare %invisible[[show_types]]

default_sort %invisible"{finite,chan}"

subsection \<open>SB Functions with finite Domains\<close> 
text\<open>\label{sub:sbfin}\<close>

text\<open>This section will provide some additional functions and
properties that only hold, if the domain of a \gls{sb} is finite. We
also introduce locales for constructing \Gls{sb}.\<close>

(*<*)
subsubsection \<open>Continuous Version of sbHdElem\_h\<close> 
text\<open>\label{subsub:sbhdelemc}\<close>
(*>*)

text\<open>The @{const sbHdElem_h} \ref{subsub:sbhdelem} operator is in
general monotone, but not continuous. The following theorem shows 
why bundle chains with infinite domains cause continuity problems.
One can construct a chain of bundle with an infinite domain, where
the first chain element is \<open>\<bottom>\<close> and the next element of all elements
in the chain always have one more stream that is not \<open>\<epsilon>\<close> anymore.
This results in an infinite chain where all chain bundles have
infinitely many empty stream but the least upper bound has none.\<close>

text\<open>Thus @{const sbHdElem_h} function will output \<open>\<bottom>\<close> for each 
chain element, but for the chains loop, it returns a @{type sbElem}.
This is proven in the following theorem, where the chain is 
formulated in assumptions.\<close> 

theorem sbhdelem_h_n_cont:
  fixes   Y::"nat \<Rightarrow> ('cs::chan)\<^sup>\<Omega>"
  assumes "chain Y"
  and     "\<And>i. \<not>sbHdElemWell (Y i)"
  and     "sbHdElemWell (\<Squnion>i. Y i)"  
  shows   "(\<Squnion>i. sbHdElem_h (Y i)) \<noteq> sbHdElem_h (\<Squnion>i. Y i)"
  apply(auto simp add: sbHdElem_h_def assms)[1]
  using assms(3) sbHdElemWell_def apply auto[1]
proof-
  assume a1:"Iup (Abs_sbElem (Some (\<lambda>c. shd ((\<Squnion>x. Y x)  \<^enum>  c))))=\<bottom>"
  have "\<not>sbElem_well (Some (\<lambda>c. shd ((\<Squnion>x. Y x)  \<^enum>  c))) \<and> 
         sbElem_well (Some (\<lambda>c. shd ((\<Squnion>x. Y x)  \<^enum>  c)))"
    by (metis a1 inst_up_pcpo u.distinct(1))
  then show False
    by blast
qed

text\<open>Nevertheless, the additional restriction to a finite domain is
enough for gaining this property. Hence, we introduce a continuous 
lifted version of @{const sbHdElem_h}.\<close>

lemma cont_h2:
  assumes"\<exists>s. s\<in>UNIV \<and> s\<notin>{c::'c. \<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>}"
  shows"{c::'c. \<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>}\<noteq>UNIV"
  using assms by auto

lemma sbisleastadm[simp]:
  "adm (sbIsLeast::('cs::{finite,chan})\<^sup>\<Omega>\<Rightarrow>bool)"
  apply(simp only: sbHdElemWell_def,simp)
  proof(rule admI)
    fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume chain:"chain Y"
    assume epsholds:"\<forall>i::nat. \<exists>c::'a. Y i  \<^enum>  c = \<epsilon>"
    have well:"\<forall> i.  \<not> sbHdElemWell (Y i) " 
      by (simp only: sbHdElemWell_def,simp add: epsholds)
    have h0:"\<forall>c i. ((Y i) \<^enum> c \<noteq> \<epsilon>) \<longrightarrow> ((\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>)"
      by (metis (full_types) chain is_ub_thelub minimal 
          monofun_cfun_arg po_eq_conv)
    then obtain set_not_eps where set_not_eps_def:
      "set_not_eps = {c::'a. \<exists>i. Y i \<^enum> c \<noteq> \<epsilon>}"
    by simp
    have h01:"finite set_not_eps"
      by simp
    have h1:"\<forall>c\<in>(UNIV - set_not_eps). (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      by (simp add: chain contlub_cfun_arg set_not_eps_def)
    have "set_not_eps \<noteq> UNIV"
    proof(auto)
      assume a1: "set_not_eps = UNIV"
      have "\<exists>c \<in> UNIV. (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>"
        using a1 h0 set_not_eps_def by blast
      have "\<exists> i. sbHdElemWell (Y i)"
      proof (rule ccontr, simp)
       assume a10: "\<forall>i::nat. \<not> sbHdElemWell (Y i)"
       have f110: "\<And> i::nat. \<not> sbHdElemWell (Y i)"
         by (simp add: a10)
       obtain i where i_def: "\<not> sbHdElemWell (Y i)"
         by (simp add: a10)
       obtain ch_not_eps where ch_not_eps_def:
         "ch_not_eps = {{i. Y i \<^enum> (ch) \<noteq> \<epsilon>}|ch::'a. True }"
         by blast
       obtain surj_f where surj_f_def:
         "surj_f = (\<lambda> ch. {i. Y i \<^enum> (ch::'a) \<noteq> \<epsilon>})"
         by simp
       have "ch_not_eps \<subseteq>  surj_f ` ({c::'a | c. True})"
         using ch_not_eps_def surj_f_def by auto
       then have ch_not_epsfinite: "finite ch_not_eps"
         by (metis finite_code finite_surj)
       have ch_not_eps_ele_not_emp: "\<forall> ele \<in> ch_not_eps. ele \<noteq> {}"
         using ch_not_eps_def a1 set_not_eps_def by blast
       have dom_emty_iff:"\<And>c. (ch_not_eps={}) \<longleftrightarrow> 
                          (Rep (c::'a) \<in> cEmpty)"
         by (metis (mono_tags, lifting) Collect_empty_eq
            Diff_eq_empty_iff IntI chDom_def ch_not_eps_def
            ch_not_eps_ele_not_emp chan_botsingle empty_iff
            mem_Collect_eq repinrange sbGetCh.rep_eq)
       have dom_not_emp_false: "ch_not_eps= {}"
       proof -
         have el_ch_not_eps_least: "\<forall> ele. ele \<in> ch_not_eps 
            \<longrightarrow> (\<exists> i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
         proof (rule ccontr, simp)
           assume a1111: "\<exists>ele::nat set. ele \<in> ch_not_eps \<and> 
                 (\<forall>i::nat. i \<in> ele \<longrightarrow> (\<exists>x::nat\<in>ele. \<not> i \<le> x))"
           obtain the_ch where the_ch_def: 
               "(surj_f the_ch) \<in> ch_not_eps \<and> 
               (\<forall>i::nat. i \<in> (surj_f the_ch) 
                \<longrightarrow> (\<exists>x::nat \<in> (surj_f the_ch). \<not> i \<le> x))"
                and the_ch_def2:
                "(surj_f the_ch) = {i. Y i \<^enum> the_ch \<noteq> \<epsilon>}"
             using a1111 ch_not_eps_def surj_f_def by blast
           obtain the_i where the_i_def: "the_i \<in> (surj_f the_ch)"
             using ch_not_eps_ele_not_emp the_ch_def by auto
           obtain the_subs where the_subst_def: 
             "the_subs = {i. i \<le> the_i \<and> Y i \<^enum> the_ch \<noteq> \<epsilon>}"
             by simp
           have the_subs_fin: "finite the_subs"
             by (simp add: the_subst_def)
           hence the_min_in_subs: "Min the_subs \<in> the_subs"
             using Min_in the_subs_fin the_i_def the_subst_def 
                   the_ch_def2 by blast
           hence the_min_min: "\<forall> i \<in> (surj_f the_ch). 
                                    Min the_subs \<le> i"
             using the_ch_def2 nat_le_linear the_subst_def 
             by fastforce
           show False
             using the_ch_def the_min_in_subs the_min_min surj_f_def
               the_ch_def the_subst_def by auto
         qed
          obtain bla::"nat set \<Rightarrow> nat set" where bla_def: 
      "bla = (\<lambda> da_set. {the_i. (\<forall> i \<in> da_set. the_i \<le> i) \<and>
      the_i \<in> da_set})"
            by simp
          obtain min_set_set::"nat set" where min_set_set_def:
      "min_set_set = {THE i. i \<in> bla da_set |
      da_set. da_set \<in> ch_not_eps}"
            by simp
          have i_max_is_max: "\<forall> ch::'a. \<exists> i .
      (i \<in> min_set_set) \<longrightarrow> Y i \<^enum> ch \<noteq> \<epsilon>"
            using a1 set_not_eps_def by blast
          have min_set_set_finite: "finite min_set_set"
            by (simp add: ch_not_epsfinite min_set_set_def)
          obtain the_max where the_max_def:
                "the_max = Max min_set_set"
            by simp
          have "the_max \<in> min_set_set"
            by (metis (mono_tags, lifting) Max_in min_set_set_finite
                ch_not_eps_def empty_Collect_eq equals0I 
                min_set_set_def the_max_def)
          have "sbHdElemWell (Y the_max)"
          proof (simp only: sbHdElemWell_def, rule allI)
            fix c::'a 
            obtain the_set where the_set_def: "the_set = surj_f c"
              by simp
            then obtain the_min where the_min_def:
              "the_min \<in> the_set \<and> (\<forall> j \<in> the_set. the_min \<le> j)"
              using el_ch_not_eps_least ch_not_eps_def surj_f_def 
                    the_set_def by blast
            have "bla the_set = {the_min}"
              using bla_def the_min_def by force
            hence "(THE i::nat. i \<in> bla the_set) = the_min"
              by auto
            hence the_min_min_set_set_in: "the_min \<in> min_set_set"
              using min_set_set_def ch_not_eps_def surj_f_def 
                    the_set_def by blast
            have "Y the_min \<^enum> c \<noteq> \<epsilon>"
              using surj_f_def the_min_def the_set_def by blast
            thus "Y the_max  \<^enum>  c \<noteq> \<epsilon>"
              by (metis min_set_set_finite the_max_def chain
                  po_class.chain_mono minimal monofun_cfun_arg
                  po_eq_conv Max_ge the_min_min_set_set_in)
          qed
          then show ?thesis
            by (simp add: a10)
        qed
        then show False
          using ch_not_eps_def by auto
      qed
      thus False
        by (metis well)
    qed
    then show "\<exists>c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      using h1 by blast
  qed

lift_definition sbHdElem_h_cont::"'cs::{finite,chan}\<^sup>\<Omega> \<rightarrow> ('cs\<^sup>\<surd>) u"
is "sbHdElem_h"
  unfolding sbHdElem_h_def
  apply(intro cont2cont)
  apply(rule Cpo.contI2)
  apply(rule monofunI)
  apply auto[1]
  apply (metis sbhdelem_mono_eq sbhdelem_some sbhdelemchain)
proof-
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
  assume ch1:"chain Y"
  assume ch2:"chain (\<lambda>i::nat. if sbIsLeast (Y i) then \<bottom> else 
              Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
  have "adm (\<lambda>sb::'c\<^sup>\<Omega>. \<exists>c. sb  \<^enum>  c = \<epsilon>)"
    apply(insert sbisleastadm) 
    by(simp only: sbHdElemWell_def,simp)
  hence "\<forall>i::nat. \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> 
          \<Longrightarrow> \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
    using admD ch1 by blast
  hence finiteIn:"\<forall>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon> 
          \<Longrightarrow> \<exists>i. \<forall>c::'c. (Y i) \<^enum> c \<noteq> \<epsilon>"
    by blast
  thus "(if sbIsLeast (\<Squnion>i::nat. Y i) then \<bottom> else 
Iup (Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq>
       (\<Squnion>i::nat. if sbIsLeast (Y i) then \<bottom> 
else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
  proof(cases "sbIsLeast (\<Squnion>i::nat. Y i)")
    case True
    then show ?thesis
      using sbnleast_mex by auto
  next
    case False
    obtain n where n_def:"\<not>sbIsLeast (Y n)"
      by (metis False finiteIn sbHdElemWell_def)
    have "sbHdElemWell (\<Squnion>x::nat. Y x) \<Longrightarrow>
    Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>x::nat. Y x)  \<^enum>  c))) =
    Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c)))"
      by (metis below_shd ch1 is_ub_thelub n_def sbHdElemWell_def 
          sbgetch_sbelow)
    hence "(if sbIsLeast (\<Squnion>i. Y i) then \<bottom> else Iup 
(Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq>
 Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      by auto
    then show ?thesis
      by (metis (mono_tags, lifting) below_lub ch2 n_def)
  qed
qed

lemma finite_lenset[simp]:"finite {f\<cdot>(x  \<^enum>  c) |c::'cs. True}"
  by(subst finite_image_set,simp,simp)

lemma least2min[simp]:
  assumes "finite A"
  and "A \<noteq> {}"
  shows"(LEAST n::'a::linorder. n \<in> A) = 
       (Min A)"
  apply(subst Least_Min,simp_all add: assms)
  using assms by auto

lemma sblenadm_below[simp]:
  assumes "((\<sqsubseteq>)::'lnat::{cpo,linorder} \<Rightarrow> 'lnat \<Rightarrow> bool) = (\<le>)"
  shows "adm (\<lambda>Y::'a\<^sup>\<Omega>. Min {(g:: M stream \<rightarrow> 'lnat)\<cdot>(Y  \<^enum>  c) |c::'a. True} \<sqsubseteq> k)"
    apply(rule admI)
    apply(subst contlub_cfun_arg,simp)+
  proof(rule ccontr)
    fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume chy:"chain Y"
    assume a1:"\<forall>i::nat. Min {g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<sqsubseteq> k"
    assume a2:"Min {\<Squnion>i::nat. g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<notsqsubseteq> k"
    have finites:"\<And>i. finite {g\<cdot>(Y i  \<^enum>  c) |c::'a. True}"
      using finite_lenset by blast
    have nemptys:"\<And>i. {g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<noteq> {}"
      by auto
    have "\<And>i::nat. Min {g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<in> {g\<cdot>(Y i  \<^enum>  c) |c::'a. True}"
      by (metis (no_types) Min_in finite_lenset nemptys)
    hence exc:"\<And>i. \<exists> c. g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k"
      using a1 apply auto[1] by metis
    then obtain f where f_def:"\<And>i. f i = {c. g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k}"
        by simp
      obtain revf where revf_def:"\<And>i. revf i = {c. \<not>(g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k)}"
        by simp
      have finitef:"\<And>i. finite (f i)"
        by simp
      have nemptyf:"\<And>i. f i\<noteq> {}"
        apply(simp add: f_def)
        using exc lnle_conv by blast
      have revchainf:"\<And>i. f (Suc i) \<subseteq> f i"
        apply(auto simp add: f_def)[1]
        by (meson chy monofun_cfun_arg po_class.chainE rev_below_trans)
      have finitef:"\<And>i. finite (revf i)"
        by simp
      have revchainf:"chain revf"
        apply(rule chainI)
        apply(auto simp add: revf_def less_set_def)[1]
        by (meson chy monofun_cfun_arg po_class.chainE rev_below_trans)
      hence revchainffinite:"finite_chain revf"
        apply(rule finite_range_imp_finch) by simp
      then obtain max where max_def:"max_in_chain max revf"
        using finite_chainE by auto
      have revfinvf:"\<And>i. revf i \<union> f i = UNIV"
        by(simp add: revf_def f_def,auto)
      have interempty:"\<And>i. revf i \<inter> f i = {}"
        by(simp add: revf_def f_def,auto)
    have "\<exists>c. \<forall>i. g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k"
    proof(rule ccontr)
      assume contr:"\<nexists>c::'a. \<forall>i::nat. g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k"
      have "\<exists>c. \<forall>i. c \<in> f i"
      proof(rule ccontr,simp)
        assume "\<forall>c::'a. \<exists>i::nat. c \<notin> f i"
        then have "\<forall>c. \<exists>i. c\<in> revf i"
          using revfinvf by fastforce
        then have "(\<Squnion>i. (revf i)) = UNIV"
          apply(simp add: lub_eq_Union)
          by auto
        hence "revf max = UNIV"
          using max_def maxinch_is_thelub revchainf by auto
        hence "f max = {}"
          using interempty by auto
        thus False
          using nemptyf by auto
      qed
      thus False
        by(insert contr,auto simp add: f_def)
    qed
    then obtain c where c_def:"\<And>i. g\<cdot>(Y i  \<^enum>  c) \<sqsubseteq> k"
      by blast
    then have "(\<Squnion>i::nat. g\<cdot>(Y i  \<^enum>  c)) \<sqsubseteq> k"
      apply(subst admD,simp_all)
      by (simp add: chy)
    moreover have "Min {\<Squnion>i::nat. g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<sqsubseteq> (\<Squnion>i::nat. g\<cdot>(Y i  \<^enum>  c))"
      apply(subst assms)
      apply(rule Min_le)
      by(subst finite_image_set,simp,simp,auto)
    ultimately have "Min {\<Squnion>i::nat. g\<cdot>(Y i  \<^enum>  c) |c::'a. True} \<sqsubseteq> k"
      using rev_below_trans by blast
    thus False
      using a2 by blast
  qed


lemma Min_cont:
  assumes "((\<sqsubseteq>)::'lnat::{cpo,linorder} \<Rightarrow> 'lnat \<Rightarrow> bool) = (\<le>)"
  shows"cont (\<lambda>x::'a\<^sup>\<Omega>. Min {(g:: M stream \<rightarrow> 'lnat)\<cdot>(x  \<^enum>  c) |c::'a. True})"
  apply(rule adm2cont)
proof(rule monofunI)
  fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
  assume sub:"x \<sqsubseteq> y"
  then have xsy:"\<And>c. g\<cdot>(x  \<^enum>  c) \<le> g\<cdot>(y  \<^enum>  c)"
    by (metis assms cont_pref_eq1I)
  have n_emptyy:"{g\<cdot>(y  \<^enum>  c) |c::'a. True} \<noteq> {}"
    by auto
  have n_emptyx:"{g\<cdot>(x  \<^enum>  c) |c::'a. True} \<noteq> {}"
    by auto
  have finitey:"finite {g\<cdot>(y  \<^enum>  c) |c::'a. True}"
    using finite_lenset by simp
  have finitex:"finite {g\<cdot>(x  \<^enum>  c) |c::'a. True}"
    using finite_lenset by simp
  thus "Min {g\<cdot>(x  \<^enum>  c) |c::'a. True} \<sqsubseteq> Min {g\<cdot>(y  \<^enum>  c) |c::'a. True}"
  proof-
    obtain c where c_def:"Min{g\<cdot>(y  \<^enum>  c) |c::'a. True} =  g\<cdot>(y  \<^enum>  c)"
      using Min_in finitey n_emptyy by auto
    moreover have "Min{g\<cdot>(x  \<^enum>  c) |c::'a. True} \<le> g\<cdot>(x \<^enum> c)"
      using Min_le finitex by blast
    ultimately show ?thesis
      by (metis (no_types, lifting) xsy assms dual_order.trans)
  qed
next
  fix k::'lnat
  show "adm (\<lambda>Y::'a\<^sup>\<Omega>. Min {g\<cdot>(Y  \<^enum>  c) |c::'a. True} \<sqsubseteq> k)"
    using assms sblenadm_below by blast
qed

lemma sblen_cont[simp]:"cont (sbLen::'cs\<^sup>\<Omega> \<Rightarrow> lnat)"
  unfolding sbLen_def
  apply(intro cont2cont)
  apply(subst least2min)
  apply(simp only: len_stream_def finite_lenset)
  using finite_lenset[of slen]
  apply blast
  apply(simp only: len_stream_def,rule Min_cont)
  apply(rule fun_eqI)
  using lnle_def by blast

lemma cont_sblen[simp]:"cont (len::'cs::{finite,chan}\<^sup>\<Omega> \<Rightarrow> lnat)"
  by(simp add: len_sb_def)

lemma sblen_leadm2[simp]:
   shows "adm (\<lambda>sb::'cs\<^sup>\<Omega>. #sb \<le> k)"
  apply(rule admI)
  apply(simp add: cont2contlubE)
  apply(rule admD,simp_all)
   apply(subst lnle_def)
   apply(rule adm_below,simp_all)
  apply(rule chainI)
  apply(rule mono_len2)
  using po_class.chainE by blast


lemma sblenneq_adm[simp]:"adm (\<lambda>xa::'cs\<^sup>\<Omega>. #xa \<noteq> Fin x)"
  apply(rule adm_neq_compact)
  apply(rule compactI,simp)
  apply(rule admI)
  apply auto[2]
  by (metis below_fin_imp_ninf l42 linear lnle_conv lub_below unique_inf_lub)


lemma sblenfneq_adm[simp]:
  "adm (\<lambda>xa::'cs\<^sup>\<Omega>. #((f\<cdot>xa)::'cs2\<^sup>\<Omega>) \<noteq> Fin x)"
  apply(rule adm_neq_compact)
  apply(rule compactI,simp)
  apply(rule admI)
  apply auto[2]
  apply (metis below_fin_imp_ninf l42 linear lnle_conv lub_below unique_inf_lub)
  apply(rule cont_compose_mix)
  by simp

lemma sblen_eqadm[simp]:
  shows "adm (\<lambda>sb::'cs\<^sup>\<Omega>. #sb = k)"
  by simp

lemma sblen_leadm[simp]:
  shows "adm (\<lambda>sb::'cs\<^sup>\<Omega>. k < #sb)"
  by (meson adm_upward dual_order.strict_trans1 mono_len)

hide_const %invisible sbLen

                                              text\<open>\label{subsub:sbsplit}\<close>


definition sb_step::"('cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'a::pcpo) \<rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'a" where
"sb_step \<equiv> \<Lambda> k sb. fup\<cdot>(\<Lambda> sbe. k sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb)"

text\<open>The @{const sb_step} function takes a function that describes
the mapping of a \gls{sb} depending on its first @{type sbElem} and 
returns a function, that only takes a \gls{sb} as an input. And maps
its first element accordingly.\<close>

lemma sb_step_insert:"sb_step\<cdot>k\<cdot>sb = (case sbHdElem_h_cont\<cdot>sb of 
up\<cdot>(sbe::'b\<^sup>\<surd>) \<Rightarrow> k sbe\<cdot>(sbRt\<cdot>sb))"
  apply(simp add: sb_step_def)
  done

text\<open>Interestingly, the output of @{const sb_step} is only strict,
if the domain of its input is not empty. For the
empty domain it behaves according to the function it gets as a
input. This is intended, because automatons with no input still can
produce output.\<close>

lemma sb_steps_bot[simp]:
"\<not>(chDomEmpty (TYPE ('cs))) \<Longrightarrow> sb_step\<cdot>f\<cdot>(\<bottom>::'cs\<^sup>\<Omega>) = \<bottom>"
  by(simp add: sb_step_insert sbHdElem_h_cont.rep_eq sbHdElem_h_def 
      chDom_def)

theorem sb_steps_leastbot[simp]:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty (TYPE ('cs))"
      and "sbIsLeast sb"
  shows   "sb_step\<cdot>f\<cdot>sb = \<bottom>"
  using assms
  by(simp add: sb_step_insert sbHdElem_h_cont.rep_eq sbHdElem_h_def 
      chDom_def)

lemma sb_steps_len0[simp]:
  fixes   sb::"'cs\<^sup>\<Omega>"
  assumes "#sb = 0"
  shows   "sb_step\<cdot>f\<cdot>sb = \<bottom>"
  apply(cases "chDomEmpty (TYPE ('cs))")
  using assms apply auto[1]
  using assms sb_steps_leastbot sbnleast_len by blast

text\<open>Hence, it is only a helper function construct mappings over 
\Gls{sb} from a step wise mapping over @{type sbElem}s.\<close>

theorem sb_steps_sbe[simp]:"sb_step\<cdot>f\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = f sbe\<cdot>sb"
  apply (subst sb_step_insert)
  apply (subst sbrt_sbecons)
  by(simp add: sbHdElem_h_cont.rep_eq sbhdelem_h_sbe)

lemma sbsplit_eqI: assumes "\<And>sbe sb. spf\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = f sbe\<cdot>sb"
      and "\<And>sb. #sb = 0 \<Longrightarrow> spf\<cdot>sb = \<bottom>"
    shows "spf = sb_step\<cdot>f"
  apply(rule cfun_eqI, rename_tac "sb")
  apply(case_tac "sb")
  apply (simp add: assms)+
  by (metis(full_types) assms(1) sb_steps_sbe sbtypeepmpty_sbbot)
  
lemma sb_steps_sbe_empty[simp]:
"chDomEmpty TYPE('cs) \<Longrightarrow> sb_step\<cdot>f\<cdot>(sb::'cs\<^sup>\<Omega>) = f sbe\<cdot>sb"
  by (metis (full_types) sb_steps_sbe sbtypeepmpty_sbbot)

lemma sb_steps_sbe_empty2:
"chDomEmpty TYPE('cs) \<Longrightarrow> sb_step\<cdot>f\<cdot>(sb::'cs\<^sup>\<Omega>) = 
                                            f (Abs_sbElem None)\<cdot>\<bottom>"
  by (metis (full_types) sb_steps_sbe sbtypeepmpty_sbbot)

lemma sb_step_cont[simp]: "cont (\<lambda> k sb. fup\<cdot>(\<Lambda> sbe. k sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb))"
  apply (intro cont2cont)
  by (simp add: discr_cont3)



definition sbMap::"('cs1\<^sup>\<surd> \<Rightarrow> 'cs2\<^sup>\<surd>) \<Rightarrow> 'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>" where
"sbMap f = (\<mu> h. sb_step\<cdot>(\<lambda>sbe. \<Lambda> sb. f sbe \<Zcat>\<^sup>\<surd> h\<cdot>sb))"

lemma sbmap_bottom:
  assumes "\<not> chDomEmpty TYPE('a)"
  and "sbIsLeast (x::'a\<^sup>\<Omega>)" 
  shows "sbMap f\<cdot>x = \<bottom>"
  apply(simp add: sbMap_def)
  apply(subst fix_eq)
  apply(simp add: sb_step_insert)
  by (metis (no_types, lifting) assms fup1 sbHdElem_h_cont.rep_eq 
      sbHdElem_h_def)


lemma sbmap_bottom_alt[simp]:
  assumes "#(x::'a\<^sup>\<Omega>) = 0" 
  shows "sbMap f\<cdot>x = \<bottom>"
  apply(rule sbmap_bottom)
  apply(rule ccontr)
  using assms by auto

lemma sbmap_bottom2[simp]: 
  assumes "\<not> chDomEmpty TYPE('a)"
  shows "sbMap f\<cdot>(\<bottom>::'a\<^sup>\<Omega>) = \<bottom>"
  using sbmap_bottom assms botsbleast by blast

lemma sbmap_cont[simp]: "cont (\<lambda> f. (\<mu> h. sb_step\<cdot>(\<lambda>sbe. \<Lambda> sb. f sbe \<Zcat>\<^sup>\<surd> h\<cdot>sb)))"
  by simp

lemma sbmap_step[simp]: "sbMap f\<cdot>(sbe \<Zcat>\<^sup>\<surd> sb) = (f sbe) \<Zcat>\<^sup>\<surd> sbMap f\<cdot>sb"
  apply(simp add: sbMap_def)
  apply(subst fix_eq)
  by simp

lemma sbmaps2sbmap[simp]:   
  fixes f::"'a\<^sup>\<surd> \<Rightarrow> 'b\<^sup>\<surd>"
  and g::"'b\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<surd>"
  assumes "\<not> chDomEmpty TYPE('a)"
  and "\<not> chDomEmpty TYPE('b)"
  shows "sbMap g\<cdot>(sbMap f\<cdot>x) = sbMap (g o f)\<cdot>x"
  apply(induction x, simp)
  using assms(1) apply blast
  by(simp_all add: assms)+

lemma sbe2sb_h:
  fixes sbe :: "'cs\<^sup>\<surd>"
  assumes "\<not>chDomEmpty TYPE ('cs)"
  shows "sbe2sb sbe = sbe \<Zcat>\<^sup>\<surd> \<bottom>"
  by (simp)

lemma sbmap_sbe2sb:
  fixes f :: "'a\<^sup>\<surd> \<Rightarrow> 'b\<^sup>\<surd>"
  assumes "\<not>chDomEmpty TYPE ('a)"
  and "\<not>chDomEmpty TYPE ('b)"
  shows "sbMap f\<cdot>(sbe2sb sbe) = sbe2sb (f sbe)"
  apply(subst sbe2sb_h)
  apply(simp add: assms)
  apply(subst sbmap_step)
  by(subst sbmap_bottom2, simp_all add: assms)



lemma sbtlen_cont[simp]:"cont (tlen::'cs::{finite,tchan}\<^sup>\<Omega> \<Rightarrow> lnat)"
  unfolding tlen_sb_def
  apply(intro cont2cont)
  apply(subst least2min)
  apply(simp only: tlen_stream_def finite_lenset)
  using finite_lenset[of slen]
  apply blast
  apply(simp only: tlen_stream_def,rule Min_cont)
  apply(rule fun_eqI)
  using lnle_def by blast

instance sb ::("{finite,tchan}") tlen_cont
  apply(intro_classes)
  by(simp add: tlen_sb_def)


end
