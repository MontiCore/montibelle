theory MsgWithChan

imports inc.Classes Channel stream.EventStream

begin
default_sort type

definition well::"('chan::chan \<times> msg) \<Rightarrow> bool" where
"well \<equiv> \<lambda>(c,m). (m \<in> cMsg (Rep c))"

lemma wellI: "snd a \<in> cMsg (Rep (fst a)) \<Longrightarrow> well a"
  by (simp add: case_prod_unfold well_def)

typedef ('chan::chan) msgWithChan = "{(chan, msg) | (chan::'chan) msg::msg.
    well (chan,msg)
  } \<union> (if (chDom TYPE('chan) = {}) then {undefined} else {})"
proof(cases "chDom TYPE('chan) = {}";simp add: well_def)
  obtain a b where undefined_def:"(a::'chan,b::msg) = undefined"
    using prod.collapse by blast
  thus "\<exists>(a::'chan) b::msg. (a, b) = undefined \<or> b \<in> cMsg (Rep a)"
    by(auto) 
next
  assume cdom:"chDom TYPE('chan) \<noteq> {}"
  then have "\<And>c::'chan. cMsg (Rep c)\<noteq> {}"
    using ctype_empty_iff dom2ctypenempty by blast
  then obtain m c where well:"m \<in> cMsg (Rep (c::'chan))"
    by (meson all_not_in_conv)
  thus "\<exists>(a::'chan) b::msg. b \<in> cMsg (Rep a)"
    by auto
qed
instantiation msgWithChan::(chan)equal
begin
definition "equal_msgWithChan ec1 ec2 = ((ec1::'a msgWithChan) = ec2)"
instance
  by(intro_classes,simp add: equal_msgWithChan_def)
end

lemma Abs_msgWithChan_inverse2:"well t \<Longrightarrow> Rep_msgWithChan (Abs_msgWithChan t) = t"
  apply(rule Abs_msgWithChan_inverse)
  by simp

lemma wellineventwithchan:"well t \<Longrightarrow> t \<in> Rep_msgWithChan ` UNIV"
  by (metis Abs_msgWithChan_inverse2 range_eqI)


setup_lifting type_definition_msgWithChan

lemma repincMsg:assumes "chDom TYPE ('cs::chan) \<noteq> {}"
  shows"Rep_msgWithChan x \<in> {(chan, msg) | (chan::'cs) msg::msg.
    msg \<in> (cMsg (Rep chan))}"
    apply(insert Rep_msgWithChan[of x])
    using assms by(simp_all add: assms well_def chDom_def)

lemma reprangeincmsg:
  assumes "chDom TYPE ('cs::chan) \<noteq> {}"
  shows "range Rep_msgWithChan = {(chan, msg) | (chan::'cs) msg::msg.
    msg \<in> (cMsg (Rep chan))}"
proof(auto)
  fix a::'cs and b::msg and x::"'cs msgWithChan"
  assume a1:"(a, b) = Rep_msgWithChan x"
  have "(a::'cs, b::msg)
    \<in> {(chan, msg) |(chan::'cs) msg::msg. msg \<in> cMsg (Rep chan)}"
    apply(insert Rep_msgWithChan[of x])
    using assms by(simp_all add: a1 well_def chDom_def)
  then show "b \<in> cMsg (Rep a)"
    by auto
next
  fix a::'cs and b::msg
  assume a1:"b \<in> cMsg (Rep a)"
  then show "(a, b) \<in> range Rep_msgWithChan"
    apply(subst range_eqI[of _ _ "Abs_msgWithChan (a,b)"],auto)
    apply(subst Abs_msgWithChan_inverse,simp add: well_def)..
qed

lemma repincMsg2[simp]:assumes "chDom TYPE ('cs::chan) \<noteq> {}"
  and "Rep_msgWithChan x = (cs::'cs,m)"
shows"m \<in> cMsg (Rep cs)"
  using repincMsg[of x] assms by auto

lemma repeventwithchan_well[simp]:
  assumes "chDom TYPE ('cs::chan) \<noteq> {}"
  shows"well (Rep_msgWithChan x::'cs\<times>msg)"
  by(simp add: well_def,cases "Rep_msgWithChan x",simp add: assms)

lemma repeventwithsomechan_well[simp]:
  shows"well (Rep_msgWithChan x::'cs::somechan\<times>msg)"
  by (simp)

lemma repeventwithchan_notwell[simp]:
  assumes "chDom TYPE ('cs::chan) = {}"
  shows"\<not>(well (Rep_msgWithChan x::'cs\<times>msg))"
  apply(simp add: well_def,cases "Rep_msgWithChan x",simp add: assms) 
  using assms ctype_empty_iff dom2ctypeempty by blast

lemma map_absrep_id:assumes "\<And>t. t\<in> set ls \<Longrightarrow> well t"
  shows"map Rep_msgWithChan (map Abs_msgWithChan ls) = ls"
  using assms
  apply(induction ls;simp)
  by (simp add: Abs_msgWithChan_inverse2)
instance msgWithChan::("{chan,countable}")countable
proof(intro_classes)    
  obtain prod2nat where prod2nat_def:"inj (prod2nat::('a\<times>msg) \<Rightarrow> nat)"
    by auto
  show "\<exists>to_nat::'a msgWithChan \<Rightarrow> nat. inj to_nat"
    apply (rule_tac x="\<lambda>a. prod2nat ((fst (Rep_msgWithChan a)), (snd (Rep_msgWithChan a)))" in exI)
    apply (auto)[1]
    by (meson Rep_msgWithChan_inject inj_def prod2nat_def)
qed



definition ewcTypeCast:: "'cs1::chan msgWithChan \<Rightarrow> 'cs2::chan msgWithChan" where
"ewcTypeCast msg = (if Rep (fst (Rep_msgWithChan msg)) \<in> chDom (TYPE ('cs2))
                    \<and> chDom TYPE('cs1) \<noteq> {}
          then (Abs_msgWithChan o (apfst (Abs o Rep)) o Rep_msgWithChan) msg
          else undefined)"


lemma ewctypecast_well: assumes "Rep (fst (Rep_msgWithChan m)) \<in> chDom (TYPE ('csGreat::chan))"
  shows "well ((apfst ((Abs o Rep)::'csSmall::chan\<Rightarrow>'csGreat)) (Rep_msgWithChan m))"
  apply(rule wellI; simp add: assms)
  by (metis assms cdom_notempty cempty_rule prod.collapse repincMsg2)

lemma ewctypecast_rep: assumes "Rep (fst (Rep_msgWithChan m)) \<in> chDom (TYPE ('csGreat::chan))"
  shows "(Rep_msgWithChan ((ewcTypeCast::'csSmall::chan msgWithChan \<Rightarrow> 'csGreat msgWithChan) m)) 
       = (apfst (Abs o Rep)) (Rep_msgWithChan m)"
  apply(auto simp add: ewcTypeCast_def assms)[1]
  using ewctypecast_well[OF assms] apply (simp add: Abs_msgWithChan_inverse2; fail)
  using assms cdom_notempty cempty_rule by blast



definition getChannel::"'cs::chan msgWithChan \<Rightarrow> 'cs" where
"getChannel msgCs = fst (Rep_msgWithChan msgCs)"

definition getMsg::"'cs::chan msgWithChan \<Rightarrow> msg" where
"getMsg msgCs = snd (Rep_msgWithChan msgCs)"



definition ewcFiltercast::"'csPrev::{chan,countable} msgWithChan event stream \<rightarrow> 'cs::{chan,countable} msgWithChan event stream" where
"ewcFiltercast = emap ewcTypeCast oo efilter (\<lambda>msg. Rep (getChannel msg) \<in> chDom TYPE('cs))"

lemma ewcfiltercast_bot[simp]:"ewcFiltercast\<cdot>\<epsilon> = \<epsilon>"
  and ewcfiltercast_tick[simp]:"ewcFiltercast\<cdot>(\<up>Tick \<Zcat> rst) = \<up>Tick \<Zcat> ewcFiltercast\<cdot>rst"
  and ewcfiltercast_msg_in[simp]: "Rep (getChannel msg) \<in> chDom TYPE('cs::{chan,countable}) 
        \<Longrightarrow> ewcFiltercast\<cdot>(\<up>(EventMsg msg) \<Zcat> rst) = \<up>(EventMsg ((ewcTypeCast msg)::'cs msgWithChan)) \<Zcat> ewcFiltercast\<cdot>rst"
  and ewcfiltercast_msg_notin[simp]: "Rep (getChannel msg) \<notin> chDom TYPE('cs::{chan,countable}) 
        \<Longrightarrow> ewcFiltercast\<cdot>(\<up>(EventMsg msg) \<Zcat> rst) = ((ewcFiltercast\<cdot>rst) :: 'cs msgWithChan event stream)"
   apply(simp add: ewcFiltercast_def)+
  done


lemma ewcfilter_tlen[simp]: "#\<^sub>\<surd>((ewcFiltercast\<cdot>s)::'cs::{chan,countable} msgWithChan event stream) = #\<^sub>\<surd> s"
  apply(induction s rule:eind)
    apply (simp add: tlen_stream_def)
    apply simp
   apply simp
   apply(case_tac "Rep (getChannel msg) \<in> chDom TYPE('cs)"; simp; fail)
  by simp


lemma mwc_eqI: "getMsg x = getMsg y \<Longrightarrow> getChannel x = getChannel y \<Longrightarrow> x=y"
  apply(cases x;cases y; auto)
       apply (auto simp add: Abs_msgWithChan_inject getMsg_def getChannel_def Abs_msgWithChan_inverse2)
  by ((metis(full_types) repeventwithchan_notwell split_pairs2)+)?



end
