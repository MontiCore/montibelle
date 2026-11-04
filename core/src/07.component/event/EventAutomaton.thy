theory EventAutomaton 

imports stream.EventStream automaton.Automaton automaton.AutomatonCausality
begin

default_sort countable

primrec l2es::"'a list \<Rightarrow> 'a event stream" where
"l2es [] = \<up> Tick" |
"l2es (x#xs) = \<up>(EventMsg x) \<Zcat> l2es xs"

definition l2estream::"'a list stream \<rightarrow> 'a event stream" where
"l2estream = fix\<cdot>(\<Lambda> h. stream_step\<cdot>(\<lambda>l . \<Lambda> ls. l2es l \<Zcat> h\<cdot>ls))"

lemma l2estream_unfold[simp]:"l2estream\<cdot>(\<up>a \<Zcat> s) = l2es a \<Zcat> l2estream\<cdot>s"
  apply(simp add: l2estream_def)
  apply(subst fix_eq)
  by(subst beta_cfun,simp_all)

lemma l2estream_bot[simp]:"l2estream\<cdot>\<epsilon> = \<epsilon>"
  apply(simp add: l2estream_def)
  apply(subst fix_eq)
  by(subst beta_cfun,simp_all)

lemma l2estream_bot2[simp]:"l2estream\<cdot>(\<up>[]) = \<up>Tick"
  using l2estream_unfold[of "[]" \<epsilon>]
  by auto

lemma l2estream_unfold2[simp]:"l2estream\<cdot>(\<up>(x#xs) \<Zcat> s) = \<up>(EventMsg x) \<Zcat> l2estream\<cdot>(\<up>xs \<Zcat> s)"
  by simp

lemma l2estream_unfold3[simp]:"l2estream\<cdot>(\<up>(x#xs)) = \<up>(EventMsg x) \<Zcat> l2estream\<cdot>(\<up>xs)"
  using l2estream_unfold2[of x xs \<epsilon>] by simp
 (*
section\<open>event to list stream\<close>


definition e2ls_h::"'a event stream \<Rightarrow> 'a list" where
"e2ls_h = (map (\<lambda>e. case e of EventMsg a \<Rightarrow> a)) o s2list"


pcpodef 'a estream = "{s::'a::countable event stream | s ls. s = l2estream\<cdot>ls}"
  apply auto
  apply(rule exI[where x=\<epsilon>],simp)
  apply(rule admI)
  sorry

definition e2lstream::"'a estream \<rightarrow> 'a list stream" where
"e2lstream = (\<Lambda> s. fix\<cdot>(\<Lambda> h. (\<Lambda> s. \<up>(e2ls_h (stakewhile (\<lambda>e. e\<noteq> Tick)\<cdot>s)) \<Zcat> 
              h\<cdot>(sdropwhile (\<lambda>e. e\<noteq>Tick)\<cdot>s)))\<cdot>(Rep_estream s))"
*)

default_sort "{countable,tlen}"

lemma fixes f::"'m \<Rightarrow> 'm stream \<rightarrow> 'n stream"
  assumes "\<And>input msg.  #\<^sub>\<surd>msg + #\<^sub>\<surd> input \<le> #\<^sub>\<surd>((f msg)\<cdot>input)"
  shows " #\<^sub>\<surd>input \<le> #\<^sub>\<surd>(stream_step\<cdot>f\<cdot>input)"
  by(cases input; simp add: assms)

theorem statesem_weak_stream:
  fixes aut :: "('state::type, 'a::{tlen,countable}, 'out::{tlen_cont, tlenconc, pcpo}) automaton"
  assumes "spf \<in> stateSem stream_step aut s"
        and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> #\<^sub>\<surd>msg \<le> #\<^sub>\<surd>out \<and> wellformed out"  
  shows "(#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(spf\<cdot>(input)))"
  apply(rule statesem_weak_ind [where aut="aut" and step="stream_step" and conv="sup'" and s=s])
      apply(auto simp add: assms)[5]
  using stream_tlen_eps streamind by blast

theorem sem_weak_stream:
  fixes aut ::"('state::type, 'a::{tlen,countable}, 'out::{tlen_cont, tlenconc, pcpo}) automaton"
  assumes "spf \<in> sem stream_step aut"
      and "\<And> state msg state' out. (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> #\<^sub>\<surd>msg \<le> #\<^sub>\<surd>out \<and> wellformed out"  
    and "\<And>initState initOut. (initState, initOut) \<in> autInitConfig\<cdot>aut \<Longrightarrow> wellformed initOut "
  shows "weak spf"
  apply(rule sem_weak [where step=stream_step and aut=aut])
    apply(simp add: assms; fail)
   apply (simp add: assms(2) statesem_weak_stream weak_def)
  by (simp add: assms(3))

theorem sem_strong_stream:
  fixes aut :: "('state::type, 'a::{tlen,countable}, 'out::{tlen_cont, tlenconc, pcpo}) automaton"
  assumes "spf \<in> sem stream_step aut"
    and "\<And>state spf. state\<in> fst ` autInitConfig\<cdot>aut \<Longrightarrow> spf \<in> (stateSem stream_step aut state) \<Longrightarrow> weak spf"
    and "\<forall>(initState, initOut) \<in> autInitConfig\<cdot>aut. 1 \<le> #\<^sub>\<surd>initOut \<and> wellformed initOut "
  shows "strong spf"
  apply(rule sem_strong_ind[where step=stream_step and aut=aut])
  by(simp_all add: assms)

default_sort type

text\<open>Event automatons in Isabelle are just an instance of the general
automaton where their semantic uses the stream splitting function 
@{const stream_step}. In the following, the event automatons 
message type describes possible events. Since it might include
timing information, not every input is allowed. 
For example, processing infinitely many inputs in a time unit is not
possible. Hence, lemma might include assumptions forcing 
@{const wellformed} in or output. If it does not include any 
timed events it automatically describes an untimed event automaton.\<close>

definition eStateSem::"('state, 'msg::countable, 'out::{pcpo,conc}) automaton 
  \<Rightarrow> 'state \<Rightarrow> ('msg stream \<rightarrow> 'out) set" where
"eStateSem = stateSem stream_step"
definition eSem::"('state, 'msg::countable, 'out::{pcpo,conc}) automaton 
  \<Rightarrow> ('msg stream \<rightarrow> 'out) set" where
"eSem = sem stream_step"
lemma assumes "aut' \<sqsubseteq> aut"
  shows "eSem aut' \<subseteq> eSem aut"
  by(simp add: eSem_def assms) 

lemma eStateSem_unfold: 
  assumes "spf \<in> eStateSem aut state"
  and "\<And> msg nextState out nextSPF f .(nextState, out) \<in> (autTransition\<cdot>aut) state msg \<Longrightarrow>
       nextSPF \<in> stateSem stream_step aut nextState \<Longrightarrow>
       f msg\<cdot>sb = out\<Zcat>\<Zcat>nextSPF\<cdot>sb \<Longrightarrow> P (stream_step\<cdot>f\<cdot>sb)"
  shows "P (spf\<cdot>sb)"
  using assms apply (simp add: eStateSem_def)
  by (metis stateSemf_def)


lemma eSem_unfold_pred: 
  assumes "spf \<in> (eSem p)"
and "\<And>spf state out. (state,out)\<in>autInitConfig\<cdot>p \<Longrightarrow>
        spf \<in> (eStateSem p) state \<Longrightarrow>
        P  (out \<Zcat>\<Zcat> spf\<cdot>sb)"
shows "P (spf\<cdot>sb)"
proof -
  obtain spf2 initState initOut where 
    initstate_initout_def: "(initState, initOut) \<in> (autInitConfig\<cdot>p)"
    and sem2_statesem: "spf2\<in>(eStateSem p) initState"
    and sem_apply: "spf\<cdot>sb = initOut \<Zcat>\<Zcat> spf2\<cdot>sb"
    apply(insert ndasem_pred[of spf stream_step p sb])
    by (metis assms(1) eSem_def eStateSem_def)
  show " P (spf\<cdot>sb)"
    apply(simp add: sem_apply)
    apply(rule assms(2)[of initState])
    apply (simp add: initstate_initout_def)
    by (simp add: sem2_statesem)
qed 


default_sort "{countable,tlen}"


theorem estatesem_weak:
  fixes aut :: "('state::type, 'a::{tlen,countable}, 
                'out::{tlen_cont, tlenconc, pcpo}) automaton"
  assumes "spf \<in> eStateSem aut s"
        and "\<And> state msg state' out. 
           (state',out) \<in> ((autTransition\<cdot>aut) state msg)
            \<Longrightarrow> #\<^sub>\<surd>msg \<le> #\<^sub>\<surd>out \<and> wellformed out"  
      shows "(#\<^sub>\<surd>input \<le> #\<^sub>\<surd>(spf\<cdot>(input)))"
  using assms by(simp add: eStateSem_def statesem_weak_stream)


theorem esem_strong:
  fixes aut :: "('state::type, 'a::{tlen,countable}, 
                 'out::{tlen_cont, tlenconc, pcpo}) automaton"
  assumes "spf \<in> eSem aut"
    and "\<And>state spf. state\<in> fst ` autInitConfig\<cdot>aut 
          \<Longrightarrow> spf \<in> (eStateSem aut state) \<Longrightarrow> weak spf"
    and "\<forall>(initState, initOut) \<in> autInitConfig\<cdot>aut. 
              1 \<le> #\<^sub>\<surd>initOut \<and> wellformed initOut "
  shows "strong spf"
  using assms by(simp add: eSem_def eStateSem_def sem_strong_stream)
        
lemma estatesem2dastatesem:
  assumes "is_singleton (autInitConfig\<cdot>aut)"
  and "\<And>state msg. is_singleton ((autTransition\<cdot>aut) state msg)"
  shows "eStateSem aut s= {daStateSem stream_step (aut2da aut) s}"
  apply(simp add: eStateSem_def)
  apply(rule stateSem2daStateSem_aut[where conv = "sup'"],simp_all add: assms)
  using streamind by auto

lemma esem2dasem:
  assumes "is_singleton (autInitConfig\<cdot>aut)"
  and "\<And>state msg. is_singleton ((autTransition\<cdot>aut) state msg)"
  shows "eSem aut = {daSem stream_step (aut2da aut)}"
  apply(simp add: eSem_def)
  apply(rule sem2daSem_aut,simp_all add: assms)
  apply(rule stateSem2daStateSem_aut[where conv = "sup'"],simp_all add: assms)
  using streamind by auto

end
