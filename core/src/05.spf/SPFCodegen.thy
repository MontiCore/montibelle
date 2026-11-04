theory SPFCodegen

imports bundle.SBCodegen SPFComp
begin
default_sort "chan"


definition spfComp_h::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<Rightarrow> (('O1 \<union> 'O2)\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>))" where 
"spfComp_h = (\<lambda> spf1 spf2 sbIn. (\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spf2\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2)))"

lemma [code]:"Rep_cfun(spfComp_h spf1 spf2 sbIn) =
 (\<lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>1) \<uplus> spf2\<cdot> (sbIn \<uplus>\<^sub>- sbOut\<star>\<^sub>2))"
  by (simp add: spfComp_h_def)

lemma [code_abbrev]:"fix_nc(spfComp_h spf1 spf2 sbIn) 0 = spfComp\<cdot>spf1\<cdot>spf2\<cdot>sbIn"
  by (simp add: spfComp_def2 fix_def spfComp_h_def fix_nc_def botsb_eq)
  
definition spfComp_abbrh::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" 
(infixr "\<otimes>" 70) where "spfComp_abbrh spf1 spf2 \<equiv> (\<Lambda> sbIn . fix_nc(spfComp_h spf1 spf2 sbIn) 0) "

lemma[code]:"Rep_cfun(spfComp_abbrh spf1 spf2) = (\<lambda> sbIn . fix_nc(spfComp_h spf1 spf2 sbIn) 0) "
  by(simp add:spfComp_abbrh_def spfComp_h_def fix_nc_def botsb_eq)

lemma [code_abbrev]:"spfComp_abbrh spf1 spf2 = spfComp\<cdot>spf1\<cdot>spf2"
  by (simp add: spfComp_def2 fix_def spfComp_abbrh_def spfComp_h_def fix_nc_def botsb_eq)

end