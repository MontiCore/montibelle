theory SPF

imports bundle.SB inc.Causality

begin
                                                               text\<open>\label{sec:spf}\<close>

text \<open>A \gls{spf} is written as \<open>('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)\<close>. It is an continuous
  function from the input bundle \<open>('I\<^sup>\<Omega>)\<close> to an output bundle \<open>('O\<^sup>\<Omega>)\<close>. 
The signature of the component is directly visible from the 
  type-signatur of the \gls{spf}:\<close>

definition spfType ::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> 
  (channel set \<times> channel set)" where
"spfType _ = (chDom TYPE ('I), chDom TYPE ('O))"


definition spfDom ::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> channel set" where
"spfDom = fst o spfType"


definition spfRan ::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> channel set" where
"spfRan = snd o spfType"


definition spfIO::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set" where
"spfIO spf = {(sb, spf\<cdot>sb) | sb. True}"

paragraph\<open>SPF Equality \\\<close> text\<open>\label{par:spfeq}\<close>


definition spfEq::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> bool" where 
"spfEq f1 f2 \<equiv> chDom TYPE('I1) = chDom TYPE('I2) \<and> 
               chDom TYPE('O1) = chDom TYPE('O2) \<and>
                (\<forall>sb1 sb2. sb1 \<triangleq> sb2 \<longrightarrow> f1\<cdot>sb1 \<triangleq> f2\<cdot>sb2)"

text\<open>The operator checks the domain equality of input and output 
domains and then the bundle equality of its possible output bundles.
For easier use, a infix abbreviation \<open>\<triangleq>\<^sub>f\<close> is defined.\<close>

abbreviation spfeq_abbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> bool"
(infixr "\<triangleq>\<^sub>f" 101) where "f1 \<triangleq>\<^sub>f f2 \<equiv> spfEq f1 f2"

lemma spfeq_refl: "f \<triangleq>\<^sub>f f"
  apply (simp add: spfEq_def sbEQ_def)
  using sb_eqI by  blast

lemma spfeq_symmetric:
  assumes "f \<triangleq>\<^sub>f g"
  shows "g \<triangleq>\<^sub>f f"
  using assms
  by (simp add: spfEq_def sbeq_symmetric)

lemma spfeq_trans:
  fixes f::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)"
  and g::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)"
  and h::"('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>)"
  assumes "f \<triangleq>\<^sub>f g" and "g \<triangleq>\<^sub>f h"
  shows "f \<triangleq>\<^sub>f h"
  using assms apply(auto simp add: spfEq_def)[1]
proof -
  fix sb1::"'I1\<^sup>\<Omega>"
  fix sb3::"'I3\<^sup>\<Omega>"
  assume a1: "chDom TYPE('I1) = chDom TYPE('I3)"
  assume a2: "chDom TYPE('I2) = chDom TYPE('I3)"
  assume a3: "\<forall>(sb1::'I1\<^sup>\<Omega>) sb2::'I2\<^sup>\<Omega>. sb1 \<triangleq> sb2 \<longrightarrow> f\<cdot>sb1 \<triangleq> g\<cdot>sb2"
  assume a4: "\<forall>(sb2::'I2\<^sup>\<Omega>) sb3::'I3\<^sup>\<Omega>. sb2 \<triangleq> sb3 \<longrightarrow> g\<cdot>sb2 \<triangleq> h\<cdot>sb3"
  assume a5: "sb1 \<triangleq> sb3"
  obtain x::"'I2\<^sup>\<Omega>" where x_def: "x = (sb1\<star>)" by auto
  have h1: "x \<triangleq> sb1" by (subst x_def, auto simp add: sbEQ_def a1 a2)
  have s1: "f\<cdot>sb1 \<triangleq> g\<cdot>x" using h1 a3
    using sbeq_symmetric by blast
  obtain y::"'I2\<^sup>\<Omega>" where x_def: "y = (sb3\<star>)" by auto
  have h2: "y \<triangleq> sb3" by (subst x_def, auto simp add: sbEQ_def a1 a2)
  have s2: "g\<cdot>y \<triangleq> h\<cdot>sb3" using h2 a4
    using sbeq_symmetric by blast 
  show "f\<cdot>sb1 \<triangleq> h\<cdot>sb3"
    apply(subst sbeq_trans[of "f\<cdot>sb1" "g\<cdot>x"], auto simp add: s1 s2)
    using a4 a5 h1 sbeq_trans by blast
qed

lemma spfeq_smallest:
fixes f::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)"
and g::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)"
assumes "chDom TYPE('I1) \<noteq> chDom TYPE('I2) \<or>
         chDom TYPE('O1) \<noteq> chDom TYPE('O2) \<or>
         (\<exists>sb1 sb2. sb1 \<triangleq> sb2 \<and> \<not>(f\<cdot>sb1 \<triangleq> g\<cdot>sb2))"
shows "\<not>(f \<triangleq>\<^sub>f g)"
  using assms by (simp add: spfEq_def)

lemma spf_empty_eq: 
  fixes spfA spfB :: "'input::cpo \<rightarrow> ('cs::emptychan sb)" 
  shows "spfB = spfA"
  apply(intro cfun_eqI)
  by(rule sb_empty_eq[OF emptychanempty])

text\<open>However, we will introduce a function to convert the domain of 
a component. Similar to @{const sbTypeCast} \ref{subsub.sbconvert}
this makes it possible to evaluate the equality of two components
with the same domains but different types. It also allows us to
restrict input or output domains, hence it can be used for hiding 
channels.\<close>

lift_definition spfConvert::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>)" is
"\<lambda> f. (sbTypeCast oo f oo sbTypeCast)"
  by(intro cont2cont)

lemma spfconvert_input_id_eq: "spfConvert\<cdot>f = sbTypeCast oo f"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

lemma spfconvert_output_id_eq: "spfConvert\<cdot>f = f oo sbTypeCast"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

lemma spfconvert_eq [simp]: "spfConvert\<cdot>f = f"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

lemma spfconvert_id[simp]:
  assumes "chDom TYPE('Oe) \<subseteq> chDom TYPE('O)"
  and "chDom TYPE('Ie) \<subseteq> chDom TYPE('I)"
  shows "(spfConvert::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>))\<cdot>((spfConvert::('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>) \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))\<cdot>f) = f"
  apply(rule cfun_eqI)
  apply(simp add: spfConvert_def)
  apply(subst sbtypecast_id)
  using assms apply (simp; fail)
  apply(subst sbtypecast_id)
  using assms apply (simp; fail)
  ..

lemma spfconvert_merge:
  fixes spf::"('I1\<^sup>\<Omega> \<rightarrow>'O1\<^sup>\<Omega>)"
assumes "chDom TYPE('I3) \<inter> chDom TYPE('I1 - 'I2) = {}"
    and "chDom TYPE('O1) \<inter> chDom TYPE('O3 - 'O2) = {}" 
shows"spfConvert\<cdot>((spfConvert\<cdot>spf)::('I2\<^sup>\<Omega>\<rightarrow>'O2\<^sup>\<Omega>)) = ((spfConvert\<cdot>spf) ::('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>))"
  apply(rule cfun_eqI)
  apply(simp add: spfConvert.rep_eq)
  apply(subst sb_star21general[OF assms(2)])
  apply(subst sb_star21general[OF assms(1)])
  by simp

lemma spfconvert_closed[simp]:
assumes "chDom TYPE('I1) = chDom TYPE('I2)"
    and "chDom TYPE('O2) = chDom TYPE('O3)"
  shows
  "(spfConvert::('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> ('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>))\<cdot>((spfConvert::('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>))\<cdot>f) =
   (spfConvert::('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>))\<cdot>f"
  apply(rule spfconvert_merge)
  using assms by auto

lemma spfconvert_apply:"spfConvert\<cdot>F\<cdot>sb = (F\<cdot>(sb\<star>)\<star>)"
  by(simp add: spfConvert_def)

lemma spfconvert_symmetric:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "chDom TYPE ('fIn) = chDom TYPE('gIn)"
    and "chDom TYPE('fOut) = chDom TYPE('gOut)"
    and "f = spfConvert\<cdot>g"
  shows "spfConvert\<cdot>f = g"
  apply(rule cfun_eqI)
  apply(subst spfconvert_apply)
  apply(subst assms(3))
  apply(subst spfconvert_apply)
  apply(subst sbtypecast_id)
  apply(simp add: assms)
  apply(subst sbtypecast_id)
  by (auto simp add: assms)

lemma spfconvert2spfeq:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fIn) = chDom TYPE('gIn)"
  and "chDom TYPE('fOut) = chDom TYPE('gOut)"
  shows"f = spfConvert\<cdot>g \<Longrightarrow> f \<triangleq>\<^sub>f g"
  apply(auto simp add: spfEq_def assms sbEQ_def spfConvert_def)[1]
  apply(subgoal_tac "sb1\<star> = sb2", auto)
  by (metis (full_types) assms(1) sb_eqI sbconvert_eq2 
      sbtypecast_getch)

lemma spfconvert_red:
  fixes spf1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)"
  and spf2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)"
assumes "chDom TYPE ('I1) = chDom TYPE('I2)"
assumes "chDom TYPE ('O1) = chDom TYPE('O2)"
assumes "chDom TYPE ('I2) = chDom TYPE('I)"
assumes "chDom TYPE ('O2) = chDom TYPE('O)"
and "((spfConvert\<cdot>spf1)::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)) = spfConvert\<cdot>spf2"
shows "spfConvert\<cdot>spf1 = spf2"
  apply(rule cfun_eqI)
  apply(rule sb_eqI)
  apply(simp add: spfConvert_def assms)
proof-
  fix x::"'I2\<^sup>\<Omega>" and c::'O2
  assume a1:"Rep c \<in> chDom TYPE('O)"
  have h:"\<And>(x::'I\<^sup>\<Omega>) c::'O. Rep c \<in> chDom TYPE('O) \<Longrightarrow> spf1\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c = spf2\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c"
    apply(insert assms(5))
    apply(auto simp add: cfun_eq_iff spfConvert_def)[1]
    by (metis sbtypecast_getch)
  have nempty:"chDom TYPE ('O)\<noteq>{}"
    using a1 by blast
  obtain c2 where c2_def:" c = Abs (Rep(c2::'O))"
    using a1 abs_eqI(2) rep_reduction by metis
  have "\<exists>sb.((sb::'I\<^sup>\<Omega>)\<star>) = x "
    by(rule sbtypecast_surj,simp add: assms)
  then obtain sb where sb_def:" x = ((sb::'I\<^sup>\<Omega>)\<star>)"
    by blast
  show "spf1\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c = spf2\<cdot>x  \<^enum>  c"
    apply (auto simp add: sbgetch_insert assms c2_def sb_def)[1]
    apply(subst rep_reduction)
    apply (simp_all add: assms nempty)
    by(insert h[of c2 sb],simp add: nempty sbgetch_insert assms)
qed

lemma spfconvert2hiding:
  fixes spf1::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)"
  and spf2::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)"
assumes "chDom TYPE ('I1) = chDom TYPE('I2)"
assumes "chDom TYPE ('O1) = chDom TYPE('O2)"
assumes "chDom TYPE ('I2) = chDom TYPE('I)"
assumes "chDom TYPE ('O) \<subseteq> chDom TYPE('O2)"
  assumes"spfConvert\<cdot>spf1 = spf2"
  shows "(spfConvert\<cdot>spf1::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)) = spfConvert\<cdot>spf2"
  apply(rule cfun_eqI)
  apply(rule sb_eqI,simp add: spfConvert_def)
proof-
  fix x::"'I\<^sup>\<Omega>" and c::'O
  assume a1:"Rep c \<in> chDom TYPE('O)"
  have h:"\<And>(x::'I2\<^sup>\<Omega>) c::'O2. Rep c \<in> chDom TYPE('O2) \<Longrightarrow> spf1\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c = spf2\<cdot>x  \<^enum>  c"
    apply(insert assms(5))
    apply(auto simp add: cfun_eq_iff spfConvert_def)[1]
    by (metis sbtypecast_getch)
  have nempty:"chDom TYPE ('O)\<noteq>{}"
    using a1 by blast
  obtain c2 where c2_def:"c = Abs (Rep(c2::'O2)) \<and> Rep c2 \<in> chDom TYPE('O)"
    using a1 abs_eqI(2) rep_reduction
    by (metis assms(4) in_mono)
      have "\<exists>sb.((sb::'I2\<^sup>\<Omega>)\<star>) = x "
    by(rule sbtypecast_surj,simp add: assms)
  then obtain sb where sb_def:" x = ((sb::'I2\<^sup>\<Omega>)\<star>)"
    by blast
  show "spf1\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c = spf2\<cdot>(x\<star>)  \<^enum>\<^sub>\<star>  c"
    apply (auto simp add: sbgetch_insert assms sb_def c2_def)[1]
    by(insert h[of c2 sb],simp add: sbgetch_insert assms) 
qed

lemma spfconvert_predicate:
  fixes spf::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)"
  assumes "spf2 = (spfConvert\<cdot>spf::('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>))"
      and "\<And> sb::'I1\<^sup>\<Omega>. P (sb\<star>) (spf\<cdot>sb\<star>)"
      and "chDom TYPE('O2) \<subseteq> chDom TYPE('O1)"
      and "chDom TYPE('I2) = chDom TYPE('I1)"
    shows "P sb (spf2\<cdot>sb)"
  apply(simp add: assms spfConvert_def)
  apply(subgoal_tac "sb = (((sb\<star>)::'I1\<^sup>\<Omega>)\<star>)")
  apply(metis assms(2))
  by(simp add: assms)

lemma spf_arg_cong2:
  fixes f::"'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>"
assumes "Rep c1  = Rep c2"
    and "\<And>c. Rep c \<in> chDom TYPE('cs1) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum> c"
  shows "f\<cdot>sb1  \<^enum>\<^sub>\<star> c1 = f\<cdot>sb2  \<^enum>\<^sub>\<star> c2"
  apply(auto simp add: sbgetch_insert assms(1))
  using assms(2) sb_eqI by blast

lemma spf_arg_cong: 
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
assumes "\<And>c. Rep c \<in> chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum> c"
  shows "f\<cdot>sb1  \<^enum>\<^sub>\<star>  c = f\<cdot>sb2  \<^enum>\<^sub>\<star>  c"
  apply(rule spf_arg_cong2, simp)
  using assms by blast

lemma spfConvert_cfcomp_right: 
  fixes f::"'gOut\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "\<And>(c::'Out) sb. Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('gOut) \<longrightarrow> f\<cdot>sb  \<^enum>\<^sub>\<star>  c = sb  \<^enum>\<^sub>\<star>  c"
    and "\<And>(c::'Out) sb. Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep c \<notin> chDom TYPE('gOut) \<longrightarrow> f\<cdot>sb  \<^enum>\<^sub>\<star>  c = \<epsilon>"
  shows "spfConvert\<cdot>(f oo g) = (spfConvert\<cdot>g::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(rule cfun_eqI, rule sb_eqI, simp add: spfConvert_def)
  apply(case_tac "Rep c \<in> chDom TYPE('gOut)")
  using assms(1) apply simp
  using assms(2) by simp

lemma spfConvert_cfcomp_left: 
  fixes f::"'gOut\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
assumes "\<And>(sb::'In\<^sup>\<Omega>) c::'gOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('gOut)  \<longrightarrow>  Rep c \<in> chDom TYPE('In) \<longrightarrow> g\<cdot>(sb\<star>)  \<^enum>  c = sb  \<^enum>\<^sub>\<star>  c"
    and "\<And>(sb::'In\<^sup>\<Omega>) c::'gOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('gOut)  \<longrightarrow>  Rep c \<notin> chDom TYPE('In) \<longrightarrow> g\<cdot>(sb\<star>)  \<^enum>  c = \<epsilon>"
  shows "spfConvert\<cdot>(f oo g) = (spfConvert\<cdot>f::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)"
  apply(rule cfun_eqI, rule sb_eqI, simp add: spfConvert_def)
  apply(rule spf_arg_cong, simp)
  apply(case_tac "Rep ca \<in> chDom TYPE('In)")
  using assms(1) apply blast
  using assms(2) by (simp, blast)

lemma wrapped_spf_convert_eq: 
  fixes inputMapping::"'In \<Rightarrow> 'WrappedIn"
    and outputMapping::"'WrappedOut \<Rightarrow> 'Out"
assumes inputMapping_well: "\<And>c. ctype (Rep (inputMapping c)) \<subseteq> ctype (Rep c)"
    and inputMapping_req1: "\<And>c::'In. \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<in> chDom TYPE('In) \<longrightarrow> Rep c \<in> chDom TYPE('ConvIn) \<longrightarrow> Rep (inputMapping c) = Rep c"
    and inputMapping_req2: "\<And>c::'In. \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow> Rep c \<in> chDom TYPE('In) \<longrightarrow> Rep c \<notin> chDom TYPE('ConvIn) \<longrightarrow> Rep (inputMapping c) \<notin> chDom TYPE('ConvIn)"
    and outputMapping_well: "\<And>c. ctype (Rep (outputMapping c)) \<subseteq> ctype (Rep c)"
    and outputMapping_req1: "\<And>c::'WrappedOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('ConvOut) \<longrightarrow> Rep (outputMapping c) = Rep c"
    and outputMapping_req2: "\<And>c::'ConvOut. \<not>chDomEmpty TYPE('Out) \<longrightarrow> \<not>chDomEmpty TYPE('ConvOut) \<longrightarrow>  Rep c \<notin> chDom TYPE('WrappedOut) \<longrightarrow> Rep c \<notin> chDom TYPE('Out)"
  shows "(spfConvert\<cdot>(sbRenameCh outputMapping oo spf oo sbRenameCh inputMapping)) = (spfConvert\<cdot>spf::'ConvIn\<^sup>\<Omega> \<rightarrow> 'ConvOut\<^sup>\<Omega>)"
  apply(subst spfConvert_cfcomp_right)
  apply(rule impI, rule impI, rule sbrenamech_getch3[OF outputMapping_well])
  using outputMapping_req1 apply blast
  using outputMapping_req2 apply blast
  using outputMapping_req1 outputMapping_well apply (metis emptyE rep_reduction sbgetch_empty sbrenamech_getch2 sbtypecast_getch)
  apply(rule spfConvert_cfcomp_left)
  apply(subst sbrenamech_getch[OF inputMapping_well])
  using inputMapping_req1 apply(metis sbgetch_insert sbtypecast_getch)
  apply(subst sbrenamech_getch[OF inputMapping_well])
  using inputMapping_req2 by(metis sbgetch_insert sbtypecast_getch)

lemma sbrenamech_spfconv_swap:
  fixes f::"'In1\<^sup>\<Omega>\<rightarrow>'Out1\<^sup>\<Omega>"
    and inputMapping1::"'In2 \<Rightarrow> 'In3"
    and outputMapping1::"'Out3 \<Rightarrow> 'Out2"
    and inputMapping2::"'In1 \<Rightarrow> 'In4"
    and outputMapping2::"'Out4 \<Rightarrow> 'Out1"
assumes "\<And> c. ctype (Rep (outputMapping2 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (outputMapping1 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (inputMapping1 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (inputMapping2 c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. Rep c \<in> chDom TYPE('Out3) \<longrightarrow> Rep c \<in> chDom TYPE('Out4) \<longrightarrow> Rep (outputMapping2 (Abs (Rep c))) = Rep (outputMapping1 c)"
    and "\<And> c. Rep c \<in> chDom TYPE('Out3) \<longrightarrow> Rep c \<notin> chDom TYPE('Out4) \<longrightarrow> Rep (outputMapping1 c) \<notin> chDom TYPE('Out1)"
    and "\<And> c. Rep c \<in> chDom TYPE('In1) \<longrightarrow> Rep c \<in> chDom TYPE('In2) \<longrightarrow> Rep (inputMapping1 (Abs (Rep c))) = Rep (inputMapping2 c)"
    and "\<And> c. Rep c \<in> chDom TYPE('In1) \<longrightarrow> Rep c \<notin> chDom TYPE('In2) \<longrightarrow> Rep (inputMapping2 c) \<notin> chDom TYPE('In3)"
  shows "sbRenameCh outputMapping1 oo spfConvert\<cdot>f oo sbRenameCh inputMapping1 = spfConvert\<cdot>(sbRenameCh outputMapping2 oo f oo sbRenameCh inputMapping2)"
  apply(simp add: spfConvert_def)
  apply(subst assoc_oo)+
  apply(subst sbrenamech_typecast_swap[where g="outputMapping1", OF assms(1-2, 5-6)])
  apply(subst assoc_oo[symmetric])+
  apply(subst sbrenamech_typecast_swap[where g="inputMapping2", OF assms(3-4, 7-8)])
  by simp

lemma sbrenamech_convert_eq:
  fixes f::"'cs1 \<Rightarrow> 'cs2"
    and g::"'cs3 \<Rightarrow> 'cs4"
assumes "\<And> c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "\<And> c::'Out. Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('cs1) \<longrightarrow> Rep c \<in> chDom TYPE('cs3) \<longrightarrow> Rep (f (Abs (Rep c))) = Rep (g (Abs (Rep c)))"
    and "\<And> c::'Out. Rep c \<in> chDom TYPE('Out) \<longrightarrow> Rep c \<in> chDom TYPE('cs1) \<longleftrightarrow> Rep c \<in> chDom TYPE('cs3)"
  shows "(spfConvert\<cdot>(sbRenameCh f)::'In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) = spfConvert\<cdot>(sbRenameCh g)"
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI)
  apply(rule sb_eqI, simp)
  apply(case_tac "Rep c \<in> chDom TYPE('cs1)"; case_tac "Rep c \<in> chDom TYPE('cs3)")
  apply(subst sbrenamech_getch2[OF _ assms(1)], simp)
  apply(subst sbrenamech_getch2[OF _ assms(2)], simp)
  apply simp using assms(3) apply(simp add: sbgetch_insert)
  using assms(4) apply simp
  using assms(4) apply simp
  by simp

lemma sbrenamech_convert_eq2:
  fixes f::"'cs1 \<Rightarrow> 'cs2"
    and g::"'cs3 \<Rightarrow> 'cs4"
assumes "\<And> c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
    and "\<And> c. Rep c \<in> chDom TYPE('cs1) \<longrightarrow> Rep c \<in> chDom TYPE('cs3) \<longrightarrow> Rep (g (Abs (Rep c))) = Rep (f c)"
    and "\<And> c. Rep c \<in> chDom TYPE('cs1) \<longrightarrow> Rep c \<notin> chDom TYPE('cs3) \<longrightarrow> Rep (f c) \<notin> chDom TYPE('cs2)"
  shows "sbRenameCh f = spfConvert\<cdot>(sbRenameCh g)"
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI)
  apply(rule sb_eqI, simp)
  apply(subst sbrenamech_getch[OF assms(1)])
  apply(case_tac "Rep c \<in> chDom TYPE('cs3)")
  apply(subst sbrenamech_getch2[OF _ assms(2)], simp, simp)
  using assms(3) apply(simp add: sbgetch_insert)
  using assms(4) by(simp add: sbgetch_insert)

lemma spfconv_weak:
  fixes f::"'fIn::tchan\<^sup>\<Omega> \<rightarrow> 'fOut::tchan\<^sup>\<Omega>"
assumes "chDom TYPE('fIn) \<subseteq> chDom TYPE('fIn2)"
    and "chDom TYPE('fOut2) \<subseteq> chDom TYPE('fOut)"
    and "weak f"
  shows "weak (spfConvert\<cdot>f::'fIn2::tchan\<^sup>\<Omega> \<rightarrow> 'fOut2::tchan\<^sup>\<Omega>)"
  apply(rule weakI)
  apply(subst spfconvert_apply) 
  by (meson assms order_trans sbtypecast_tlen weak_def)

lemma sbrenamech_weak:
fixes f::"('cs1::tchan) \<Rightarrow> ('cs2::tchan)"
assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
    and "\<not>chDomEmpty TYPE('cs2)"
  shows "weak (sbRenameCh f)"
  apply(auto simp add: weak_def)[1]
  by(rule sbrenamech_tlen[OF assms])


definition excp :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c \<Rightarrow> bool" where
"excp b1 b2 c \<equiv> (b1\<^enum>c \<noteq> b2\<^enum>c) \<and> (\<forall>y. (y = c \<or> b1\<^enum>y = b2\<^enum>y))"

definition no_impact :: "('cs1::{chan}\<times>'cs2::{chan}) set \<Rightarrow> ('cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>) \<Rightarrow>  bool" where
"no_impact S f  \<equiv> \<forall>(cin,cout)\<in>S. (\<forall>b1 b2. ((excp b1 b2 cin) \<longrightarrow> (f\<cdot>b1)\<^enum>cout = (f\<cdot>b2)\<^enum>cout))"

definition allow_impact :: "('cs1::{chan} \<times> 'cs2::{chan}) set \<Rightarrow> ('cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>) \<Rightarrow>  bool" where
"allow_impact S  = no_impact (UNIV -S)"

                                      text\<open>\label{sub:cspf}\<close>


definition weak_causal_broy::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool"where
"weak_causal_broy spf \<equiv> \<forall>sb1 sb2 n. 
                      # sb1 = \<infinity> \<and> # sb2 = \<infinity> \<longrightarrow>
                      sbTake n\<cdot>sb1 = sbTake n\<cdot>sb2 \<longrightarrow>
                      (# (spf\<cdot>sb1)=\<infinity> \<and> # (spf\<cdot>sb2)=\<infinity>) \<and>
                      sbTake n\<cdot>(spf\<cdot>sb1) = sbTake n\<cdot>(spf\<cdot>sb2)"



text\<open>The causal \gls{spf} types of our framework are a direct
consequence from their predicates. Strong causal components are a 
subset of the weak causal components. A weak causal component is 
realizable, but we also introduce a type for strong causal 
components for their compositional properties. In general, both 
causal types do not contain a \<open>\<bottom>\<close> element, because this would be 
inconsistent with our time model. Hence, the fixed point operator 
@{const fix} can not be used for causal \gls{spf} types.\<close>









cpodef ('I::"{tlen,cpo}",'O::"{tlen_inf,cpo}") tspfw ("(_ \<rightarrow>\<^sub>w/ _)" [1, 0] 0) = "{f::('I \<rightarrow> 'O) . weak f}"
   apply simp
  using strong2weak strong_tleninf apply auto[1]
  by (simp add: weak_well_adm)

setup_lifting %invisible type_definition_tspfw

lemma reptspfw_cont [simp, cont2cont]:"cont Rep_tspfw"
  using cont_Rep_tspfw cont_id by blast

lift_definition %invisible Rep_tspfw_fun::
"('I::{tlen,cpo},'O::{tlen_inf,cpo})tspfw \<rightarrow> ('I \<rightarrow>'O)"is "\<lambda> spfs. Rep_tspfw( spfs)"
  by(intro cont2cont)





cpodef ('I::"{tlen,cpo}",'O::"{tlen_inf,cpo}") tspfs ("(_ \<rightarrow>\<^sub>s/ _)" [1, 0] 0) 
  = "{f::('I,'O)tspfw . strong (Rep_tspfw f)}"
  apply simp
   apply (metis Abs_tspfw_inverse mem_Collect_eq strong2weak strong_tleninf)
  apply simp
  by (metis (mono_tags, lifting) adm_upward below_tspfw_def cfun_below_iff dual_order.trans mono_tlen strong_def)

setup_lifting %invisible type_definition_tspfs

lemma reptspfs_cont [simp, cont2cont]:"cont Rep_tspfs"
  using cont_Rep_tspfs cont_id by blast

lift_definition %invisible Rep_tspfs_fun::
"('I::{tlen,cpo},'O::{tlen_inf,cpo})tspfs \<rightarrow> ('I \<rightarrow>'O)"is "\<lambda> spfs. Rep_tspfw_fun\<cdot>(Rep_tspfs spfs)"
  by(intro cont2cont)

lemma Rep_strong [simp]: "strong (Rep_tspfs_fun\<cdot>tspfs)"
  by (metis Rep_tspfs Rep_tspfs_fun.rep_eq Rep_tspfw_fun.rep_eq mem_Collect_eq)

definition Abs_tspfs_fun::"('I::{tlen,cpo} \<rightarrow> 'O::{tlen_inf,cpo}) 
  \<Rightarrow> 'I \<rightarrow>\<^sub>s 'O" where
"Abs_tspfs_fun = Abs_tspfs o Abs_tspfw"

lemma tspfw_abs_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. weak (h x)"
shows "cont (\<lambda>x. Abs_tspfw (h x))"
  by (simp add: assms(1) assms(2) cont_Abs_tspfw)

lemma tspfs_abs_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. strong (Rep_tspfw (h x))"
shows "cont (\<lambda>x. Abs_tspfs (h x))"
  by (simp add: assms(1) assms(2) cont_Abs_tspfs)


lemma tspfs_fun_abs_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. strong (h x)"
  shows "cont (\<lambda>x. Abs_tspfs_fun (h x))"
  apply (simp add: assms(1) assms(2) Abs_tspfs_fun_def cont_Abs_tspfs cont_Abs_tspfw)
  apply(intro cont2cont; (simp add: assms)?)
  by (simp add: Abs_tspfw_inverse assms(2))

lemma rep_abs_tspfs: "strong tspf \<Longrightarrow> Rep_tspfs_fun\<cdot>(Abs_tspfs_fun tspf) = tspf"
  by (metis (mono_tags, lifting) Abs_tspfs_fun_def Rep_tspfs_cases Rep_tspfs_fun.rep_eq Rep_tspfs_inverse Rep_tspfw_cases Rep_tspfw_fun.rep_eq Rep_tspfw_inverse comp_apply mem_Collect_eq strong2weak)

lemma spf_weak_len:
  fixes spf::"'in::{chan,finite}\<^sup>\<Omega>\<rightarrow>'out\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('in)"
    and "\<And>sb. #sb < \<infinity> \<Longrightarrow> #(spf\<cdot>sb) = #sb"
  shows "#(spf\<cdot>sb) = #sb"
proof-
  have "\<And>sb. #sb = \<infinity> \<Longrightarrow> #(spf\<cdot>sb) = #sb"
  proof (rule ccontr)
    fix sb::"'in\<^sup>\<Omega>"
    assume sb_len: "#sb = \<infinity>"
      and not_weak: "\<not> #(spf\<cdot>sb) = #sb"
    then have "#sb > #(spf\<cdot>sb)"
      using leI by fastforce
    then obtain k where out_len: "#(spf\<cdot>sb) = Fin k"
      using lnat_well_h2 sb_len by auto
    have sbtake_sb_len: "# (sbTake (Suc k)\<cdot>sb) = Fin (Suc k)"
      by (simp add: assms sbtake_len sb_len)
    have h1: "#(spf\<cdot>(sbTake (Suc k)\<cdot>sb)) > # (spf\<cdot>sb)"
      by (simp add: assms(2) out_len sbtake_sb_len)
    have "(spf\<cdot>(sbTake (Suc k)\<cdot>sb)) \<sqsubseteq> (spf\<cdot>sb)"
      by(simp add: cont_pref_eq1I)
    thus False
      using assms out_len sbtake_sb_len
      using h1 leD mono_len by blast
  qed
  thus ?thesis
    using assms(2) inf_less_eq leI by blast
qed

end
