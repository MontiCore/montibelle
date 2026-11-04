theory Timeconverter
imports ChannelConverterTypes SB

begin

default_sort type


fun convertStream:: "timeType \<Rightarrow> timeType \<Rightarrow> M stream \<rightarrow> M stream" where
"convertStream _ _  = undefined"


lemma "well input \<Longrightarrow> well (convertStream tt1 tt2\<cdot>input)"
  oops

lemma "sValues\<cdot>(convertStream tt1 tt2\<cdot>input) \<subseteq> sValues\<cdot>input"
  oops


fun convertStreamNonDet:: "timeType \<Rightarrow> timeType \<Rightarrow> (M stream \<rightarrow> M stream) set" where
"convertStreamNonDet TUntimed _  = undefined" |
"convertStreamNonDet _  _  = undefined"


lemma 
  ctype_tfinchan_def:
  assumes "cTime (Rep c) = TTFin"
  and "chDom TYPE('cs) \<noteq> {}"
  shows"ctype (Rep (c::'cs::{tschan})) = (Timed o TFin) ` {ls. set ls \<subseteq> (cMsg (Rep c))}"
  apply(simp add: ctype_def assms)
  apply (rule ccontr)
  using assms ctype_empty_iff dom2ctypenempty by blast

lemma 
  ctype_tfinchan:
  assumes "cTime c = TTFin"
  and "cMsg c \<noteq> {}"
  shows"ctype c = (Timed o TFin) ` {ls. set ls \<subseteq> (cMsg c)}"
  by(simp add: ctype_def assms)

datatype 'cs::one_chan tstimed = TSTIMED "'cs"

fun tstimedToOrigin::"'cs::one_chan tstimed \<Rightarrow> 'cs"where
"tstimedToOrigin (TSTIMED cs) = cs"

instance tstimed::("{countable,one_chan}")countable
  by(countable_datatype)

lemma tstimed_bij[simp]:"bij TSTIMED"
  by (metis bijI' tstimed.exhaust tstimed.inject)

lemma tstimed_inv[simp]:"TSTIMED (inv TSTIMED cs) = cs"
  by (meson bij_inv_eq_iff tstimed_bij)

lemma inv_tstimed[simp]:"inv TSTIMED (TSTIMED cs) = cs"
  by (metis bij_inv_eq_iff tstimed_bij)

lemma univ_tstimed:"(UNIV::'cs::one_chan tstimed set)= TSTIMED ` UNIV"
  using bij_betw_imp_surj_on tstimed_bij by blast


instance tstimed::("{finite,one_chan}")finite
  apply(standard)
  by(simp add: univ_tstimed)

instantiation tstimed::(one_chan) chan
begin

fun Rep_tstimed::"'a tstimed \<Rightarrow> channel"where
"Rep_tstimed (TSTIMED cs)= (if Rep cs \<in> chDom TYPE('a)then changeTimeType TTFin (Rep cs) else Rep cs)"

definition chanDom_tstimed::"'a tstimed myself \<Rightarrow> channel set"where
"chanDom_tstimed _ = changeTimeType TTFin ` chanDom (DUMMY::'a myself)"

definition Abs_tstimed::" channel \<Rightarrow> 'a tstimed"where"(Abs_tstimed::(channel \<Rightarrow> ('a::one_chan) tstimed)) (cs::channel) =
(if cs \<in> chanDom( (DUMMY::'a tstimed myself))  then  TSTIMED (THE a. (cName (Rep a)) = cName cs \<and> cMsg (Rep a) = cMsg cs) else
TSTIMED (Abs cs))" 

lemma chandom_tstimed_def2:"chanDom (c::'a tstimed myself) = changeTimeType TTFin ` chDom TYPE('a)"
  by(simp add: chanDom_tstimed_def chandomchdomeq)

lemma rep_tstimed_def2:assumes "chDom TYPE('a) \<noteq> {}"
  shows"Rep cs = changeTimeType TTFin (Rep (inv TSTIMED cs))"
  by(cases cs;simp add: assms)

lemma rep_tstimed_def_empty:assumes "chDom TYPE('a) = {}"
  shows"Rep cs = (Rep (inv TSTIMED cs))"
  by(cases cs;simp add: assms)

lemma rangerep:assumes "chDom TYPE('a)\<noteq> {}"
  shows"range (Rep::'a tstimed \<Rightarrow> channel) = changeTimeType TTFin ` (range (Rep::'a \<Rightarrow> channel))"
  apply(auto)[1]
  apply(case_tac xa;simp add: assms) 
proof -
  fix xb :: 'a
  have "Rep (TSTIMED xb) \<in> range (Rep::'a tstimed \<Rightarrow> channel)"
    by (meson rangeI)
  then show "changeTimeType TTFin (Rep xb) \<in> range (\<lambda>t. Rep (t::'a tstimed))"
    by (simp add: assms)
qed

lemma chdom_empty:"chDom TYPE('a) = {} \<longleftrightarrow> chanDom (x::'a tstimed myself) = {}"
  by(simp add: chanDom_tstimed_def chandomchdomeq)+

lemma ctype_nempty:"ctype ((c)) \<noteq> {} \<longleftrightarrow> ctype (changeTimeType T (c)) \<noteq> {}"
  by(simp add: ctype_empty_iff)

lemma nandmeq:
  assumes"changeTimeType T (CH name time p) = CH name2 time2 p2"
  shows "name = name2" 
  and "p=p2"
  using assms by(auto)

lemma tstimedtoorigin_cmsg[simp]:
  shows "cMsg (Rep (tstimedToOrigin c)) = cMsg (Rep c)"
  by (metis Rep_tstimed.elims cMsg.elims nandmeq(2) tstimedToOrigin.simps)

lemma cttype_inj_on:
  assumes "chDom TYPE('a) \<noteq> {}"
  shows"inj_on (changeTimeType T)  (range (Rep::'a \<Rightarrow> channel))"
  apply(rule inj_onI)
  apply(subgoal_tac "cTime x = cTime y")
   apply(case_tac x)
   apply(case_tac y,simp) 
proof-
  fix x y
  assume a1:" x \<in> range (Rep::'a \<Rightarrow> channel)"
  assume a2:" y \<in> range (Rep::'a \<Rightarrow> channel)"
  assume a3:"changeTimeType T x = changeTimeType T y"
  obtain a b where a_def:"(a ::'a) = Abs x" and b_def:"(b::'a) = Abs y"
    by simp
  have "cTime (Rep a) = cTime (Rep b)"
    apply(rule onechan_ctimesimp)
    apply (simp add: assms; fail)
    apply(simp add: a_def b_def a1 a2)
    apply(subst rep_reduction)
    using a1 assms chdom_in apply blast
    apply(subst rep_reduction)
    using a2 assms chdom_in apply blast
    using a3
    by (metis cName.simps changeTimeType.elims)
  thus "cTime x = cTime y"
    using a1 a2 a_def b_def
    by (metis assms chdomnotempty_rangeeq rep_reduction)
qed

lemma cname_change_eq: "cName (changeTimeType TTFin ( x)) = cName x"
  by (metis nandmeq(1) cName.elims)

lemma cmsg_change_eq: "cMsg (changeTimeType TTFin ( x)) = cMsg x"
  by (metis nandmeq(2) cMsg.elims)
  
lemma abs_rep_inv:"Abs((Rep::('a tstimed \<Rightarrow>channel)) (a::('a:: one_chan)tstimed)) = a "
  apply(cases a,simp)
  apply (rule conjI)
  apply(simp add: Abs_tstimed_def)
  apply (rule conjI)
  apply (simp add: cname_change_eq) 
  apply (metis (mono_tags, lifting)one_chan_neqI the_equality)
  using chandom_chdom_eq chandom_tstimed_def2 apply blast
  apply (simp add: Abs_tstimed_def)
  using chdom_empty chdomnotempty_rangeeq by blast
  
instance
  apply(standard)
  apply(simp add: abs_rep_inv; fail)
  apply(cases "chDom TYPE('a) = {}")
  apply(simp add: cEmpty_def)
  using chdom_empty rep_tstimed_def_empty apply auto[1]
  apply(simp add: chandom_tstimed_def2 chanDom univ_tstimed)
  apply (rule antisym)
  apply(auto)[1]
  apply(case_tac "xa";simp)
  apply (metis (mono_tags, opaque_lifting) all_not_in_conv changeTimeType.simps imageI rangeI rangerep rep_reduction univ_tstimed)
  apply(case_tac xa;simp add: cEmpty_def)
  apply (metis ctype_nempty changeTimeType.simps dom2ctypenempty emptyE rep_reduction)
  apply force
  apply(auto simp add: cEmpty_def)[1]
  apply(case_tac xc; case_tac xa;simp)
  by (metis (full_types) ctype_nempty dom2ctypeempty dom2ctypenempty empty_iff)
end

instance tstimed::(one_chan) tschan
  apply(standard)
  apply(cases "chDom TYPE ('a) = {}")
  using chandomchdomeq chdom_empty apply blast
  by(case_tac c;simp)
 
lemma tstimed_ctime[simp]:assumes "chDom TYPE('cs::one_chan) \<noteq>{}"
  shows"cTime (Rep (c::'cs tstimed)) = TTFin"
  by(cases c,simp add: assms)

lemma chdomempty_one_tstimed[simp]:"chDomEmpty TYPE('cs::{one_chan}) \<Longrightarrow> chDomEmpty TYPE('cs tstimed)"
  by (metis chandomchdomeq chdom_empty)
                                                     
lemma tstimed_cname[simp]:"cName (Rep (TSTIMED c)) = cName (Rep c)"
  apply(simp)
  by(cases "Rep c";simp)

instance tstimed::("{one_chan,emptychan}")emptychan
  apply(standard)
  apply (simp add: chanDom)
  by auto

instance tstimed::("{one_chan,somechan}")somechan
  apply(standard)
  apply (simp add: chanDom)
  apply auto[1]
  apply(simp add: rep_tstimed_def2)
  apply(case_tac xa;simp)
  apply(simp add: cEmpty_def)
  using ctype_nempty
  by (metis dom2ctypenempty somechannotempty)

lemma chdom_one_empty[simp]:assumes"chDom TYPE('cs::one_chan)\<noteq>{}"
  shows"chDom TYPE('cs tstimed) \<noteq>{}"
  by (metis assms chandomchdomeq chdom_empty)

lemma sbtlen_tstimed_eqI:
  assumes "\<And>c. Rep c \<in> chDom TYPE('a::echan) \<Longrightarrow> #\<^sub>\<surd>(sb1 \<^enum> (TSTIMED c)) = #\<^sub>\<surd>(sb2 \<^enum> c)"
  shows "#\<^sub>\<surd>(sb1) = #\<^sub>\<surd>(sb2::'a\<^sup>\<Omega>)"
proof (cases "chDomEmpty TYPE('a)")
  case True
  then show ?thesis
    by simp
next
  case False
  then obtain c1 where c1_def: "#\<^sub>\<surd>(sb1) = #\<^sub>\<surd>(sb1 \<^enum> c1)"
    by (metis chanDom_tstimed_def chandomchdomeq image_is_empty sbtlen2stlen)
  hence c1_all_leq: "\<And>c. #\<^sub>\<surd>(sb1 \<^enum> c1) \<le> #\<^sub>\<surd>(sb1 \<^enum> c)"
    by (metis False chandomchdomeq chdom_empty sbtlen_min_len)
  have sb1_sb2_tstimedtoorigin_eq: "\<And>c. #\<^sub>\<surd>(sb1 \<^enum> c) = #\<^sub>\<surd>(sb2 \<^enum> (tstimedToOrigin c))"
    by (metis False assms chdom_in tstimedToOrigin.elims)
  hence "\<And>c. #\<^sub>\<surd>(sb1 \<^enum> c1) \<le> #\<^sub>\<surd>(sb2 \<^enum> (tstimedToOrigin c))"
    by (metis c1_all_leq)
  hence "#\<^sub>\<surd>(sb2) = #\<^sub>\<surd>(sb2 \<^enum> (tstimedToOrigin c1))"
    by (metis False sb1_sb2_tstimedtoorigin_eq assms chdom_in sbtlen2stlen_h)
  then show ?thesis
    by (metis sb1_sb2_tstimedtoorigin_eq c1_def)
qed

instantiation tstimed::("{enum,one_chan}")enum
begin

definition "enum_tstimed = map TSTIMED Enum.enum"

definition "enum_all_tstimed P = Enum.enum_all (\<lambda>c. P (TSTIMED (c)))"

definition "enum_ex_tstimed P = Enum.enum_ex (\<lambda>c. P (TSTIMED (c)))"
instance
  apply(standard)
  apply(simp_all add: enum_tstimed_def)
  apply(subst UNIV_enum[symmetric])
  apply (simp add: univ_tstimed; fail)
  apply(subst distinct_map,auto)
  apply(simp add: enum_distinct; fail)
  apply (simp add: inj_on_def; fail)
  apply(auto simp add: enum_all_tstimed_def enum_ex_tstimed_def UNIV_enum)[4]
  by (metis tstimed.exhaust)+
end

end
