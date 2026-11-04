theory TSPFMethod
imports spf.SPF spf.TSPFfunction sps.SPSIO
begin

lemma cont_if3 [simp, cont2cont]: "(\<And>x y. \<lbrakk>\<not>b x; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> \<not>b y) \<Longrightarrow> (\<And>x. (b x \<Longrightarrow> cont f)) \<Longrightarrow> 
(\<And>x. (\<not>b x \<Longrightarrow> cont g)) \<Longrightarrow> (\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> g y) \<Longrightarrow> adm b\<Longrightarrow> cont (\<lambda>x. if b x then f x else g x)"
  apply(rule contI2)
  apply(rule monofunI)
  apply(case_tac "b x";case_tac "b y", simp_all)
  apply (simp add: cont2monofunE; fail)
   apply (meson cont2monofunE)
  oops

thm cont_if
lemma "adm P \<Longrightarrow> (\<And>x y. x \<sqsubseteq> y \<Longrightarrow> \<not>P x \<Longrightarrow> \<not>P y ) \<Longrightarrow> 
        (\<And>x. f\<cdot>x \<sqsubseteq>g\<cdot>x) \<Longrightarrow> cont (\<lambda>x. if P x then f\<cdot>x else g\<cdot>x)"
  apply(rule contI2)
   apply(rule monofunI)
  apply(auto)[1]
  using monofun_cfun apply blast
  using cfun_belowI monofun_cfun apply blast
  using cont_pref_eq1I apply blast
  apply(case_tac "P (\<Squnion>i::nat. Y i)")
  apply auto
  oops

definition tsbDelay::"nat \<Rightarrow> 'cs::tchan sb" where
"tsbDelay n = sbTake n\<cdot>sbInfTlen"

definition tsbDrop::"nat \<Rightarrow> 'cs::tchan sb \<rightarrow> 'cs::tchan sb" where
"tsbDrop = undefined"
definition tsbRt::"'cs::tchan sb \<rightarrow> 'cs::tchan sb" where
"tsbRt = undefined"


definition "liftedTSPF = Abs_tspfw (\<Lambda> sb. if(#\<^sub>\<surd>sb < 100) then tsbDelay 100
                            else tsbDelay 100 \<Zcat>\<Zcat> tsbDrop 100\<cdot>sb)"

lemma "cont (\<lambda>sb. if(#\<^sub>\<surd>sb < 100) then tsbDelay 100
                            else tsbDelay 100 \<Zcat>\<Zcat> tsbDrop 100\<cdot>sb)"
  apply(simp)
  oops



definition "liftedTSPF2 = Abs_tspfw (sbConc (tsbDelay 100) oo tsbDrop 100)"


definition "liftedTSPF3 = Abs_tspfw (fix\<cdot>(\<Lambda> tspf sb. tsbDelay 1 \<Zcat>\<Zcat> tspf\<cdot>(tsbRt\<cdot>sb)))"



definition "liftedTSPF4 = Abs_tspfw (SOME tspf. weak tspf
                                   \<and> (\<exists>sb. tspf\<cdot>sb = sb \<Zcat>\<Zcat> sb)
                                   \<and> (\<forall>sb. tspf\<cdot>sb \<noteq> sb))" 













definition "tsps = {ID, tspfDelayOutput 1 ID}"

definition "tsps1 = {tspfDelayOutput n ID | n::nat. n>100}"


definition tspfAdd::"nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"tspfAdd = undefined"

definition "tsps3 = {tspfAdd\<cdot>oracle | oracle::nat stream. #oracle = \<infinity>}"



definition "tsps2 = rel2sps (\<lambda>i out. #\<^sub>\<surd>i \<le> #\<^sub>\<surd>out 
                                    \<and> convUntimed\<cdot>i \<sqsubseteq> convUntimed\<cdot>out)"


lemma "TSPS = (\<lambda>tspf. tspfInputDrop 1\<cdot>(tspfOutputDrop 1\<cdot>tspf)) `TSPS"
  oops

definition "tsps_gfp = gfp(\<lambda>TSPS. (\<lambda>tspf. tspfInputDrop 1\<cdot>(tspfOutputDrop 1\<cdot>tspf)) `TSPS)"

lemma "mono (\<lambda>TSPS. f`TSPS)"
end