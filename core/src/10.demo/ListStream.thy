theory ListStream

imports stream.StreamAutomaton

begin
default_sort countable

definition lCons::"'a \<Rightarrow> 'a list stream \<rightarrow> 'a list stream" where
"lCons msg = stream_step\<cdot>(\<lambda> x. \<Lambda> xs. \<up>(msg # x) \<Zcat> xs)"

lemma lcons_eps [simp]:"lCons msg\<cdot>\<epsilon> = \<epsilon>"
  and lcons_empty [simp]:"lCons msg\<cdot>(\<up>[] \<Zcat> xs) = \<up>[msg] \<Zcat> xs"
  and lcons_cons [simp]:"lCons msg\<cdot>(\<up>ls \<Zcat> xs) = \<up>(msg#ls) \<Zcat> xs"
by(auto simp add: lCons_def)




lift_definition lDelay::"'a list stream \<rightarrow> 'a list stream" is
"\<lambda>s. \<up>[] \<Zcat> s"
  by(intro cont2cont)
declare lDelay.rep_eq [simp]




fun lEventCons::"'a event \<Rightarrow> 'a list stream \<rightarrow> 'a list stream" where
"lEventCons Tick    = lDelay" |
"lEventCons (Event m) = lCons m"

abbreviation lEventCons_abbr :: "'a event \<Rightarrow> 'a list stream \<Rightarrow> 'a list stream" 
  ("(_ \<Zcat>\<^sub>e _)" [66,65] 65)
where "msg \<Zcat>\<^sub>e s \<equiv> lEventCons msg\<cdot>s"

fun lEventCons_mult::"'a event list \<Rightarrow> 'a list stream \<rightarrow> 'a list stream" where
"lEventCons_mult []     = ID" |
"lEventCons_mult (l#ls) = (\<Lambda> s.  l \<Zcat>\<^sub>e lEventCons_mult ls\<cdot>s) "



definition lEventHd::"'a list stream \<Rightarrow> 'a event" where
"lEventHd s = (case (shd s) of [] \<Rightarrow> Tick | (l#ls) \<Rightarrow> Event l)"

definition lEventHd_cont::"'a list stream \<rightarrow> 'a event discr u" where
"lEventHd_cont = (\<Lambda> s. if s=\<epsilon> then \<bottom> else updis (lEventHd s))"

lemma "s\<noteq>\<epsilon> \<Longrightarrow> lEventHd (lEventCons m\<cdot>s) = m"
  apply(cases m; cases s)
  by(auto simp add: lEventHd_def)



definition lRt::"'a list stream \<rightarrow> 'a list stream" where
"lRt = stream_step\<cdot>(\<lambda> x. \<Lambda> xs. case x of [] \<Rightarrow> xs | _ \<Rightarrow> \<up>(tl x) \<Zcat> xs)"

lemma [simp]:"lRt\<cdot>\<epsilon> = \<epsilon>"
  and [simp]:"lRt\<cdot>(\<up>[] \<Zcat> xs) = xs"
  and [simp]:"lRt\<cdot>(\<up>[]) = \<epsilon>"
  and [simp]:"lRt\<cdot>(\<up>(l#ls) \<Zcat> xs) = \<up>ls \<Zcat> xs"
  by(auto simp add: lRt_def)



lemma [simp]: "lRt\<cdot>(lEventCons m\<cdot>s) = s"
  apply(cases m; cases s)
  by auto

lemma "lRt\<cdot>(lDelay\<cdot>xs) = xs"
  and "lRt\<cdot>(lCons msg\<cdot>xs) = xs"
   apply(simp)
  apply(cases xs; simp)
  done


lemma assumes "adm P"
          and "P \<epsilon>"
          and "\<And>s.     P s \<Longrightarrow> P (\<up>Tick \<Zcat> s)"
          and "\<And>msg s. P s \<Longrightarrow> P (\<up>(Event msg) \<Zcat> s)"
        shows "P (s::'a event stream)"
  by (metis assms(1) assms(2) assms(3) assms(4) streamind tlen_event.cases)
 
lemma assumes "adm P"
          and "P \<epsilon>"
          and "\<And>s.     P s \<Longrightarrow> P (Tick    \<Zcat>\<^sub>e s)"
          and "\<And>msg s. P s \<Longrightarrow> P (Event msg \<Zcat>\<^sub>e s)"
        shows "P (s::'a list stream)"
  apply(induction s)
    apply(auto simp add: assms)
  apply(induct_tac a)
   apply(auto simp add: assms)
   apply (metis assms(3) lDelay.rep_eq lEventCons.simps(1))
  using assms(4) by fastforce

















lemma assumes"wellformed input"
  shows "wellformed (spf\<cdot>input)"
  oops

lemma assumes"wellformed input"
  shows "P input (spf\<cdot>input)"
  oops


lemma "P input (spf\<cdot>input)"
 oops













fun mergeh::"'a::type list list \<Rightarrow> 'a list set"where
"mergeh [] = {[]}" |
"mergeh [xs] = {xs}" |
"mergeh (xs#ys#rest) = \<Union>((\<lambda>merged. mergeh (merged#rest)) ` (shuffles xs ys))"

value "mergeh [[1,2,4::nat],[2,5,19]]"

definition mergenth::"nat \<Rightarrow> 'a list stream list \<Rightarrow> 'a list set" where
"mergenth n ls = mergeh (map (snth n) ls)"

definition mergels::"('a::countable list stream list \<Rightarrow> 'a list stream) set" where
"mergels = {f | f. \<forall>i n. snth n (f i) \<in> mergeh (((map (snth n)  i)))}"



thm smap_def


fun listZip::"'a stream list \<Rightarrow> 'a list stream" where
"listZip [] = \<epsilon>" |
"listZip (l#ls) = smap (\<lambda>(a,b). (a#b))\<cdot>(szip\<cdot>l\<cdot>(listZip ls))"

definition merge::"('a list stream list \<Rightarrow> 'a list stream) set" where
"merge = (\<lambda> f s. f\<cdot>(listZip s)) ` ndetsmap mergeh"





fun toListHelper::"'m list \<Rightarrow> 'm event \<Rightarrow> ('m list \<times> 'm list stream)" where
"toListHelper s Tick    = (   []    , \<up>s)" |
"toListHelper s (Event m) = ( s @ [m] , \<epsilon> )"

definition sTimedToList :: "'m event stream \<rightarrow> 'm list stream" where
"sTimedToList = sscanlAut toListHelper []"



definition list_stream_step::"('m event \<Rightarrow> 'm list stream \<rightarrow> 'a::pcpo) 
  \<rightarrow> 'm list stream \<rightarrow> 'a" where
"list_stream_step \<equiv> \<Lambda> k s. fup\<cdot>(\<Lambda> a. k (undiscr a)\<cdot>(lRt\<cdot>s))\<cdot>((lEventHd_cont\<cdot>s))"
                                                                   
definition listAutSem::"('state, 'msg::countable event, 'out event stream) automaton 
      \<Rightarrow> ('msg list stream \<rightarrow> 'out list stream) set" where
"listAutSem aut = (\<lambda>f. sTimedToList oo f) ` (sem list_stream_step aut)"

definition sumAutList::"(nat list stream \<rightarrow> nat list stream) set" where
"sumAutList = (listAutSem sumAut)"


lemma assumes "spf \<in> sumAutList" 
  shows "\<exists>spf2. spf\<in>UNIV \<and> spf\<cdot>(msg \<Zcat>\<^sub>e s) = undefined"
  oops




definition listAutSem2::"('state, 'msg::countable event, 'out event stream) automaton
      \<Rightarrow> ('msg list stream \<rightarrow> 'out event stream) set" where
"listAutSem2 aut = (sem list_stream_step aut)"

definition sumAutList2::"(nat list stream \<rightarrow> nat event stream) set" where
"sumAutList2 = (listAutSem2 sumAut)"


end