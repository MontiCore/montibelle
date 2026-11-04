theory Classes
imports LNat

begin


class conc =
  fixes conc :: "'a::pcpo \<Rightarrow> 'a \<rightarrow> 'a"
  assumes botconc1[simp]:"conc \<bottom>\<cdot>a = a"
      and botconc2[simp]:"conc a\<cdot>\<bottom> = a"
      and assoc: "conc (conc a\<cdot>b)\<cdot>c = conc a\<cdot>(conc b\<cdot>c)"
begin
abbreviation conc_abbr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<Zcat>\<Zcat>_" [200,200] 99) where
"s1 \<Zcat>\<Zcat> s2 \<equiv> conc s1\<cdot>s2"

lemma conc_bot1 [simp]: "f oo conc \<bottom> = f"
  by(rule cfun_eqI, simp)
lemma conc_bot2 [simp]: "conc \<bottom> oo f = f"
  by(rule cfun_eqI, simp)
lemma conc_belowI: "a=b \<Longrightarrow> as \<sqsubseteq> bs \<Longrightarrow> a \<Zcat>\<Zcat> as \<sqsubseteq> b \<Zcat>\<Zcat> bs"
  by (simp add: monofun_cfun_arg)
lemma conc_arg_cong: "x = y \<Longrightarrow> a\<Zcat>\<Zcat>x = a \<Zcat>\<Zcat>y"
  apply(rule cfun_arg_cong)
  .
lemma conc_arg_cong2: "a=b \<Longrightarrow> x = y \<Longrightarrow> a\<Zcat>\<Zcat>x = b \<Zcat>\<Zcat>y"
  by blast
lemma conc_conc_oo: "conc (sb\<Zcat>\<Zcat> rest) oo f = conc sb oo (conc rest oo f)"
  apply(rule cfun_eqI)
  by(simp add: oo_def assoc)
lemma concconc2conc: "(conc a) oo (conc b) = conc (a \<Zcat>\<Zcat> b)"
  by (metis conc_bot1 conc_conc_oo)

end

definition pconc::"('a::conc\<times>'b::conc) \<Rightarrow> ('a\<times>'b) \<rightarrow> ('a\<times>'b)" where
"pconc s1 = (\<Lambda> s2. (fst s1 \<Zcat>\<Zcat> fst s2, snd s1 \<Zcat>\<Zcat> snd s2))"

instantiation prod :: (conc, conc) conc
begin
definition "conc_prod=pconc"
instance
  apply(intro_classes)
    apply(simp_all add: conc_prod_def pconc_def)
  by (auto simp add: assoc)
end

lemma conc_prod_apply:
  shows "(s1,s2) \<Zcat>\<Zcat> (s3,s4) = (s1 \<Zcat>\<Zcat> s3, s2 \<Zcat>\<Zcat> s4)"
  by (simp add: pconc_def conc_prod_def)

lemma conc_prod_fst[simp]: "fst ((a, b) \<Zcat>\<Zcat> rest) = a \<Zcat>\<Zcat> (fst rest)"
  by (metis conc_prod_apply eq_fst_iff)

lemma conc_prod_snd[simp]: "snd ((a, b) \<Zcat>\<Zcat> rest) = b \<Zcat>\<Zcat> (snd rest)"
  by (metis conc_prod_apply eq_snd_iff)

declare pconc_def[simp]

instantiation unit :: conc
begin
definition unit_prod::"unit \<Rightarrow> unit \<Rightarrow> unit" where
"unit_prod _ _  = ()"

instance
  apply(intro_classes)
  apply(simp_all)
  done
end


instantiation lnat::conc
begin
definition conc_lnat::"lnat \<Rightarrow> lnat \<rightarrow> lnat" where
"conc_lnat ln1  = lAdd\<cdot>ln1"

instance
  apply(intro_classes)
  unfolding conc_lnat_def ladd_insert lnzero_def[symmetric]
    apply simp+
  by (simp add: add.assoc)
end
lemma lnat_conc [simp]: "ln1\<Zcat>\<Zcat>ln2 = ln1 + (ln2::lnat)"
  unfolding conc_lnat_def ladd_insert
  ..
lemma lnat_conc_1 [simp]: "lnsuc\<cdot>\<bottom> + xs = lnsuc\<cdot>xs"
  by (metis lnat_plus_lnsuc lnzero_def plus_lnat0_r)



class bot_nc = pcpo +
  fixes bot_nc
  assumes botnc_eq_bot:"bot_nc = \<bottom>"
begin

end

instantiation prod::(bot_nc,bot_nc)bot_nc
begin
definition"bot_nc_prod = (bot_nc,bot_nc)"
instance
  by(intro_classes,simp_all add: botnc_eq_bot bot_nc_prod_def)
end


class tlen = po +
  fixes tlen :: "'a::po \<Rightarrow> lnat"
  assumes len_mono: "monofun tlen"
  assumes tlen_notzero: "\<exists>a. tlen a \<noteq> 0"
begin
abbreviation tlen_abbr :: "'a \<Rightarrow> lnat" ("#\<^sub>\<surd> _" [1000] 999) where
"#\<^sub>\<surd> s \<equiv> (tlen s)"

lemma [nitpick_simp]: "tlen_abbr s = tlen s"
  by simp

lemma mono_tlen: "x \<sqsubseteq> y \<Longrightarrow> #\<^sub>\<surd>x \<le> #\<^sub>\<surd>y"
  using len_mono lnle_def monofun_def by blast

lemma mono_tlen2: "x \<sqsubseteq> y \<Longrightarrow> #\<^sub>\<surd> x \<sqsubseteq> #\<^sub>\<surd> y"
  using local.len_mono monofunE by blast

definition tlen_T::"'a" where
"tlen_T = (SOME x. #\<^sub>\<surd>x \<noteq> 0)"

lemma tlent[simp]: "#\<^sub>\<surd>tlen_T\<noteq> 0"
  apply(simp add: tlen_T_def)
  using someI tlen_notzero by force
end

class tlen_one = tlen +
  assumes tlen_one_def: "tlen a = 1"

class wellformed = tlen + len +
  fixes wellformed::"'a::{tlen,len} \<Rightarrow> bool" ("\<bbbW>" 999)
  assumes well_ex: "\<exists>a. wellformed a"
  assumes well_tlen: "\<And>a. wellformed a \<Longrightarrow> #a = \<infinity> \<Longrightarrow> #\<^sub>\<surd>a = \<infinity>"
  assumes well_infI: "\<And>a.  #\<^sub>\<surd>a = \<infinity> \<Longrightarrow> wellformed a"
  assumes well_belowI: "\<And>a super.  a\<sqsubseteq>super \<Longrightarrow> wellformed super \<Longrightarrow> wellformed a"
  assumes well_superEx: "\<And>a. wellformed a \<Longrightarrow> #\<^sub>\<surd>a < \<infinity> \<Longrightarrow>  \<exists> super. a\<sqsubseteq>super \<and> \<infinity>\<le>#\<^sub>\<surd>super"
begin

lemma well_superEx2: "wellformed a \<Longrightarrow>  \<exists> super. a\<sqsubseteq>super \<and> #\<^sub>\<surd>super=\<infinity>"
  apply(cases "#\<^sub>\<surd>a < \<infinity>")
  using well_superEx apply simp
  apply(rule_tac x=a in exI, simp)
  using inf_less_eq leI by blast

end

class tlen_len = wellformed +
  assumes tlen_len_eq[simp]: "(tlen::'a::{tlen,len} \<Rightarrow> lnat) = len"
      and well_all: "\<And>a. wellformed a"
begin

end

class tlen_cont = cpo + tlen +
  assumes tlen_cont[cont2cont, simp]: "cont (tlen::'a::{cpo, tlen} \<Rightarrow> lnat)"
begin

end

class tlen_inf = tlen +
  assumes tlen_inf[simp]: "\<exists>a :: 'a::po. #\<^sub>\<surd>a = \<infinity>"
begin
definition tlen_inf::"'a" where
"tlen_inf = (SOME a. #\<^sub>\<surd>a = \<infinity>)"

lemma tlen_inf_tlen [simp]: "#\<^sub>\<surd>tlen_inf = \<infinity>"
  apply(simp add: tlen_inf_def)
  using tlen_inf by (meson someI)
end



class tlenconc = wellformed + conc +
  assumes tlen_conc:"\<And>(a::'a::{wellformed,conc}) b. wellformed a \<Longrightarrow> #\<^sub>\<surd>a + #\<^sub>\<surd>b \<le> #\<^sub>\<surd>(a\<Zcat>\<Zcat>b)"
  and len_conc:"\<And>a b. #a=\<infinity> \<Longrightarrow> a \<Zcat>\<Zcat> b = a"
begin

end

instantiation unit::tlen
begin
definition tlen_unit::"unit \<Rightarrow> lnat" where
"tlen_unit un = \<infinity>"

instance
  apply(intro_classes)
  apply(rule monofunI)
  by(simp add: tlen_unit_def)+
end

instantiation prod::(tlen,tlen)tlen
begin
definition tlen_prod::"('a::tlen \<times> 'b::tlen) \<Rightarrow> lnat" where
"tlen_prod \<equiv> \<lambda>(a,b). min (tlen a) (tlen b)"

instance
  apply(intro_classes)
  apply(rule monofunI)
  apply (auto simp add: below_prod_def min_def tlen_prod_def)[2]
  apply (meson le_cases len_mono lnle_conv monofun_def trans_lnle)+
  by (meson tlen_notzero)
end

lemma tlen_flatten[simp]:"tlen((a,b),c) = tlen(a,b,c)"
  apply(simp add: tlen_prod_def)
  using min.assoc by blast

lemma tlen_prod_le_tlen_fst[simp]:"#\<^sub>\<surd>t \<le> #\<^sub>\<surd>(fst t)"
  by(cases t,simp add: tlen_prod_def)

lemma tlen_prod_le_tlen_snd[simp]:"#\<^sub>\<surd>t \<le> #\<^sub>\<surd>(snd t)"
  by(cases t,simp add: tlen_prod_def)

lemma tlen_prod_inf_fst[simp]:"#\<^sub>\<surd>s = \<infinity> \<Longrightarrow> #\<^sub>\<surd>(s,x) = #\<^sub>\<surd>x"
  by(simp add: tlen_prod_def)

lemma tlen_prod_inf_snd[simp]:"#\<^sub>\<surd>s = \<infinity> \<Longrightarrow> #\<^sub>\<surd>(x,s) = #\<^sub>\<surd>x"
  by(simp add: tlen_prod_def)

lemma tlen_prod_def2:"#\<^sub>\<surd>(a,b) = min (#\<^sub>\<surd>a) (#\<^sub>\<surd>b)"
  by(simp add: tlen_prod_def)

lemma tlen_prod_minl: "#\<^sub>\<surd>(a,b) \<le> #\<^sub>\<surd>a" and  tlen_prod_minr:"#\<^sub>\<surd>(a,b) \<le> #\<^sub>\<surd>b"
  by (auto simp add: tlen_prod_def)

lemma tlen_prod_rsmaller:
  assumes"(#\<^sub>\<surd>b \<le> x)"
  shows "#\<^sub>\<surd>(a,b)\<le>x"
  by (meson assms dual_order.trans tlen_prod_minr)

instantiation prod::(wellformed,wellformed)wellformed
begin
fun wellformed_prod::"('a \<times> 'b) \<Rightarrow> bool"where
"wellformed_prod (a,b) = (wellformed a \<and> wellformed b)"
instance
  apply(intro_classes)
  using well_ex[where 'a = 'a] well_ex[where 'a = 'b] apply simp
  apply(case_tac a,simp_all add: len_prod_def tlen_prod_def)
  using well_tlen apply (metis inf_less_eq min.cobounded1 min.cobounded2; fail)
  apply(case_tac a, simp, metis inf_ub min_def min_absorb2 well_infI; fail)
   apply (metis Classes.wellformed_prod.elims(3) Pair_below_iff well_belowI wellformed_prod.elims(2); fail)
  apply (metis (no_types, lifting) min.idem monofun_pair well_superEx2 wellformed_prod.elims(1))
  done
end

instance prod::(tlen_len,tlen_len) tlen_len
  apply(intro_classes)
  apply(subst fun_eq_iff,rule allI,case_tac x,simp)
  apply(simp add: tlen_prod_def len_prod_def; fail)
  by(case_tac a,simp add: well_all)

end
