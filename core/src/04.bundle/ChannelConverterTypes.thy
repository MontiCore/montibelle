theory ChannelConverterTypes
imports Channel

begin

default_sort type

class one_chan = chan +
  assumes onechan_ctime:"\<And>(c1::'a) (c2::'a). 
  Rep c1 \<in>chDom TYPE('a::chan) \<Longrightarrow> Rep c2 \<in>chDom TYPE('a::chan) \<Longrightarrow> cName (Rep c1) = cName (Rep c2) \<Longrightarrow> cTime (Rep c1) = cTime (Rep c2)"
begin

lemma onechan_ctimesimp[simp]:
  assumes "chDom TYPE('a) \<noteq> {}"
  and "cName (Rep (c1::'a)) = cName (Rep (c2::'a))"
shows "cTime (Rep c1) = cTime (Rep c2)"
  using assms(1) assms(2) chdom_in local.onechan_ctime by blast

end

subclass (in echan) one_chan
  apply(standard)
  by (metis local.echan_ctime)

subclass (in uchan) one_chan
  apply(standard)
  by (metis local.uchan_ctime)

lemma ctype_tlivechan_def:
  assumes "cTime (Rep c) = TTLive"
  and "chDom TYPE('cs) \<noteq> {}"
  shows"ctype (Rep (c::'cs::{echan})) = {(Timed o TLive) Tick} \<union> (Timed o TLive o EventMsg) ` (cMsg (Rep c))"
  apply(simp add: ctype_def assms)
  apply (rule conjI)
  using assms ctype_empty_iff dom2ctypenempty apply blast
  by auto

lemma ctype_tlivechan:
  assumes "cTime c = TTLive"
  and "cMsg c \<noteq> {}"
  shows"ctype c = {(Timed o TLive) Tick} \<union> (Timed o TLive o EventMsg) ` (cMsg c)"
  apply (simp add: ctype_def assms)
  by auto

fun changeTimeType::"timeType \<Rightarrow> channel \<Rightarrow> channel" where
"changeTimeType tt (CH name _ P) = CH name tt P"

lemma changett_msg[simp]:"cMsg (changeTimeType T c) = cMsg c"
  by(cases c,simp)

lemma changett_time[simp]:"cTime (changeTimeType T c) = T"
  by(cases c;simp)

lemma ctype_nempty:"ctype ((c)) \<noteq> {} \<longleftrightarrow> ctype (changeTimeType T (c)) \<noteq> {}"
  by(simp add: ctype_empty_iff)

lemma nandmeq:
  assumes"changeTimeType T (CH name time p) = CH name2 time2 p2"
  shows "name = name2" 
  and "p=p2"
  using assms by(auto)

datatype 'cs::one_chan tlived = TLIVED "'cs"

fun tlivedToOrigin::"'cs::one_chan tlived \<Rightarrow> 'cs"where
"tlivedToOrigin (TLIVED cs) = cs"

instance tlived::("{countable,one_chan}")countable
  by(countable_datatype)

lemma tlived_bij[simp]:"bij TLIVED"
  by (metis bijI' tlived.exhaust tlived.inject)

lemma tlived_inv[simp]:"TLIVED (inv TLIVED cs) = cs"
  by (meson bij_inv_eq_iff tlived_bij)

lemma inv_tlived[simp]:"inv TLIVED (TLIVED cs) = cs"
  by (metis bij_inv_eq_iff tlived_bij)

lemma univ_tlived:"(UNIV::'cs::one_chan tlived set)= TLIVED ` UNIV"
  using bij_betw_imp_surj_on tlived_bij by blast

instance tlived::("{finite,one_chan}")finite
  apply(standard)
  by(simp add: univ_tlived)

instantiation tlived::(one_chan) chan
begin

fun Rep_tlived::"'a tlived \<Rightarrow> channel"where
"Rep_tlived (TLIVED cs)= (if Rep cs \<in> chDom TYPE('a) then changeTimeType TTLive (Rep cs)
                                                     else Rep cs)"

definition chanDom_tlived::"'a tlived myself \<Rightarrow> channel set"where
"chanDom_tlived _ = changeTimeType TTLive ` chanDom (DUMMY::'a myself)"

definition Abs_tlived::" channel \<Rightarrow> 'a tlived" where
"Abs_tlived cs = (if cs \<in> chanDom( (DUMMY::'a tlived myself))
                  then TLIVED (THE a. (cName (Rep a)) = cName cs \<and> cMsg (Rep a) = cMsg cs)
                  else TLIVED (Abs cs))" 

lemma chandom_tlived_def2:"chanDom (c::'a tlived myself) = changeTimeType TTLive ` chDom TYPE('a)"
  by(simp add: chanDom_tlived_def chandomchdomeq)

lemma rep_tlived_def2:
  assumes "chDom TYPE('a) \<noteq> {}"
  shows"Rep cs = changeTimeType TTLive (Rep (inv TLIVED cs))"
  by (cases cs; simp add: assms)

lemma rep_tlived_def_empty:
  assumes "chDom TYPE('a) = {}"
  shows"Rep cs = (Rep (inv TLIVED cs))"
  by (cases cs ;simp add: assms)

lemma rangerep:
  assumes "chDom TYPE('a)\<noteq> {}"
  shows"range (Rep::'a tlived \<Rightarrow> channel) = changeTimeType TTLive ` (range (Rep::'a \<Rightarrow> channel))"
  apply(auto)[1]
  apply(case_tac xa;simp add: assms) 
proof -
  fix xb :: 'a
  have "Rep (TLIVED xb) \<in> range (Rep::'a tlived \<Rightarrow> channel)"
    by (meson rangeI)
  then show "changeTimeType TTLive (Rep xb) \<in> range (\<lambda>t. Rep (t::'a tlived))"
    by (simp add: assms)
qed

lemma chdom_empty:"chDom TYPE('a) = {} \<longleftrightarrow> chanDom (x::'a tlived myself) = {}"
  by(simp add: chanDom_tlived_def chandomchdomeq)+

lemma tlivedToOrigin_cmsg[simp]:
  shows "cMsg (Rep (tlivedToOrigin c)) = cMsg (Rep c)"
  by (metis Rep_tlived.elims cMsg.elims nandmeq(2) tlivedToOrigin.simps)

lemma cname_change_eq: "cName (changeTimeType TTLive ( x)) = cName x"
  by (metis nandmeq(1) cName.elims)

lemma cmsg_change_eq: "cMsg (changeTimeType TTLive ( x)) = cMsg x"
  by (metis nandmeq(2) cMsg.elims)

lemma one_chan_eqI:
  assumes"Rep (x::'a) = CH x1 x2 x3"
  and "CH x1 x2 x3 \<in> chDom TYPE('a::one_chan)"
  and "Rep y = CH x1 y2 x3"
  shows "x = y"
  using onechan_ctimesimp[of x y] assms
  by (metis abs_rep_id cName.simps cTime.simps equals0D)

lemma one_chan_neqI:
  assumes "(x::'a::one_chan) \<noteq> y"
and "Rep x\<in> chDom TYPE('a)"
shows "cName (Rep x) \<noteq> cName (Rep y) \<or> cMsg (Rep x) \<noteq> cMsg (Rep y)"
  apply (auto simp add: assms)[1]
  using onechan_ctimesimp[of x y] assms
  by(cases "Rep x";cases "Rep y";simp add: one_chan_eqI)

lemma abs_rep_inv: "Abs((Rep::('a tlived \<Rightarrow> channel)) (a::('a:: one_chan)tlived)) = a "
  apply(cases a,simp)
  apply (rule conjI)
  apply(simp add: Abs_tlived_def)
  apply (rule conjI)
  apply (simp add: cname_change_eq) 
  apply (metis (mono_tags, lifting)one_chan_neqI the_equality)
  using chandom_chdom_eq chandom_tlived_def2 apply blast
  apply (simp add: Abs_tlived_def)
  using chdom_empty chdomnotempty_rangeeq by blast

instance
  apply(standard)
  apply(simp add: abs_rep_inv; fail)
  apply(cases "chDom TYPE('a) = {}")
  apply(simp add: cEmpty_def)
  using chdom_empty rep_tlived_def_empty apply auto[1]
  apply(simp add: chandom_tlived_def2 chanDom univ_tlived)
  apply (rule antisym)
  apply(auto)[1]
  apply(case_tac "xa";simp)
  apply (metis (mono_tags, opaque_lifting) all_not_in_conv changeTimeType.simps imageI rangeI rangerep rep_reduction univ_tlived)
  apply(case_tac xa;simp add: cEmpty_def)
  apply (metis ctype_nempty changeTimeType.simps dom2ctypenempty emptyE rep_reduction)
  apply (force; fail)
  apply(auto simp add: cEmpty_def)[1]
  apply(case_tac xc; case_tac xa;simp)
  by (metis (full_types) ctype_nempty dom2ctypeempty dom2ctypenempty empty_iff)
end

instance tlived ::(one_chan) echan
  apply (standard)
  apply (cases "chDom TYPE ('a) = {}")
  using chandomchdomeq chdom_empty apply blast
  by (case_tac c; simp)

lemma tlived_ctime[simp]:assumes "chDom TYPE('cs::one_chan) \<noteq>{}"
  shows"cTime (Rep (c::'cs tlived)) = TTLive"
  by(cases c,simp add: assms)

lemma cdomempty_onetlive[simp]:"chDomEmpty TYPE('cs::{one_chan}) \<Longrightarrow> chDomEmpty TYPE('cs tlived)"
  by (metis chandomchdomeq chdom_empty)


datatype 'cs::one_chan untimed = UNTIMED "'cs"

fun untimedToOrigin::"'cs::one_chan untimed \<Rightarrow> 'cs"where
"untimedToOrigin (UNTIMED cs) = cs"

instance untimed::("{countable,one_chan}")countable
  by(countable_datatype)

lemma untimed_bij[simp]:"bij UNTIMED"
  by (metis bijI' untimed.exhaust untimed.inject)

lemma untimed_inv[simp]:"UNTIMED (inv UNTIMED cs) = cs"
  by (meson bij_inv_eq_iff untimed_bij)

lemma inv_untimed[simp]:"inv UNTIMED (UNTIMED cs) = cs"
  by (metis bij_inv_eq_iff untimed_bij)

lemma univ_untimed:"(UNIV::'cs::one_chan untimed set)= UNTIMED ` UNIV"
  using bij_betw_imp_surj_on untimed_bij by blast

instance untimed::("{finite,one_chan}")finite
  apply(standard)
  by(simp add: univ_untimed)

instantiation untimed::(one_chan) chan
begin

fun Rep_untimed::"'a untimed \<Rightarrow> channel"where
"Rep_untimed (UNTIMED cs)= (if Rep cs \<in> chDom TYPE('a) then changeTimeType TUntimed (Rep cs)
                                                     else Rep cs)"

definition chanDom_untimed::"'a untimed myself \<Rightarrow> channel set"where
"chanDom_untimed _ = changeTimeType TUntimed ` chanDom (DUMMY::'a myself)"

definition Abs_untimed::" channel \<Rightarrow> 'a untimed" where
"Abs_untimed cs = (if cs \<in> chanDom( (DUMMY::'a untimed myself))
                  then UNTIMED (THE a. (cName (Rep a)) = cName cs \<and> cMsg (Rep a) = cMsg cs)
                  else UNTIMED (Abs cs))"

lemma chandom_untimed_def2:"chanDom (c::'a untimed myself) = changeTimeType TUntimed ` chDom TYPE('a)"
  by(simp add: chanDom_untimed_def chandomchdomeq)

lemma rep_untimed_def2:
  assumes "chDom TYPE('a) \<noteq> {}"
  shows"Rep cs = changeTimeType TUntimed (Rep (inv UNTIMED cs))"
  by (cases cs; simp add: assms)

lemma rep_untimed_def_empty:
  assumes "chDom TYPE('a) = {}"
  shows"Rep cs = (Rep (inv UNTIMED cs))"
  by (cases cs ;simp add: assms)

lemma rangerep_2:
  assumes "chDom TYPE('a)\<noteq> {}"
  shows"range (Rep::'a untimed \<Rightarrow> channel) = changeTimeType TUntimed ` (range (Rep::'a \<Rightarrow> channel))"
  apply(auto)[1]
  apply(case_tac xa;simp add: assms) 
proof -
  fix xb :: 'a
  have "Rep (UNTIMED xb) \<in> range (Rep::'a untimed \<Rightarrow> channel)"
    by (meson rangeI)
  then show "changeTimeType TUntimed (Rep xb) \<in> range (\<lambda>t. Rep (t::'a untimed))"
    by (simp add: assms)
qed

lemma chdom_empty_2:"chDom TYPE('a) = {} \<longleftrightarrow> chanDom (x::'a untimed myself) = {}"
  by(simp add: chanDom_untimed_def chandomchdomeq)+

lemma untimedToOrigin_cmsg[simp]:
  shows "cMsg (Rep (untimedToOrigin c)) = cMsg (Rep c)"
  by (metis Rep_untimed.simps cMsg.simps changeTimeType.elims untimedToOrigin.elims)

lemma cname_change_eq_2: "cName (changeTimeType TUntimed ( x)) = cName x"
  by (metis nandmeq(1) cName.elims)

lemma cmsg_change_eq_2: "cMsg (changeTimeType TUntimed ( x)) = cMsg x"
  by (metis nandmeq(2) cMsg.elims)

lemma abs_rep_inv_2: "Abs((Rep::('a untimed \<Rightarrow> channel)) (a::('a:: one_chan)untimed)) = a "
  apply(cases a,simp)
  apply (rule conjI)
  apply(simp add: Abs_untimed_def)
  apply (rule conjI)
  apply (simp add: cname_change_eq_2) 
  apply (metis (mono_tags, lifting)one_chan_neqI the_equality)
  using chandom_chdom_eq chandom_untimed_def2 apply blast
  apply (simp add: Abs_untimed_def)
  using chdom_empty_2 chdomnotempty_rangeeq by blast

instance
  apply(standard)
  apply(simp add: abs_rep_inv_2; fail)
  apply(cases "chDom TYPE('a) = {}")
  apply(simp add: cEmpty_def)
  using chdom_empty_2 rep_untimed_def_empty apply auto[1]
  apply(simp add: chandom_untimed_def2 chanDom univ_untimed)
  apply (rule antisym)
  apply(auto)[1]
  apply(case_tac "xa";simp)
  apply (metis (mono_tags, opaque_lifting) all_not_in_conv changeTimeType.simps imageI rangeI rangerep_2 rep_reduction univ_untimed)
  apply(case_tac xa;simp add: cEmpty_def)
  apply (metis ctype_nempty changeTimeType.simps dom2ctypenempty emptyE rep_reduction)
  apply force
  apply(auto simp add: cEmpty_def)[1]
  apply(case_tac xc; case_tac xa;simp)
  by (metis (full_types) ctype_nempty dom2ctypeempty dom2ctypenempty empty_iff)
end

instance untimed ::(one_chan) uchan
  apply (standard)
  apply (cases "chDom TYPE ('a) = {}")
  using chandom_chdom_eq chdom_empty_2 apply blast
  by (case_tac c; simp)

lemma untimed_ctime[simp]:assumes "chDom TYPE('cs::one_chan) \<noteq>{}"
  shows"cTime (Rep (c::'cs untimed)) = TUntimed"
  by(cases c,simp add: assms)

lemma chdomempty_oneuntimed[simp]:"chDomEmpty TYPE('cs::{one_chan}) \<Longrightarrow> chDomEmpty TYPE('cs untimed)"
  using chandom_chdom_eq chdom_empty_2 by blast

end