theory railway_min
  imports stream.StreamAutomaton
begin

datatype sections = s1 | s2

instance sections::countable
  by countable_datatype

datatype access = a11 | a12 | a13 | a21 | a22 | a23

instance access::countable
  by countable_datatype

fun sect::"access \<Rightarrow> sections"where
"sect (a11) = s1"|
"sect (a12) = s1"|
"sect (a13) = s1"|
"sect (a21) = s2"|
"sect (a22) = s2"|
"sect (a23) = s2"

fun co::"access \<Rightarrow> access"where
"co (a11) = a21"|
"co (a12) = a22"|
"co (a13) = a23"|
"co (a21) = a11"|
"co (a22) = a12"|
"co (a23) = a13"

lemma co_inv:"co (co a) = a"
  by(cases a;simp)

definition close::"access \<Rightarrow> access \<Rightarrow> bool"where
"close a b = (sect a = sect b)"

fun possible_switch:: "access \<Rightarrow> access \<Rightarrow> bool"where
"possible_switch a1 a2 = (sect a1 = sect a2 \<and>  (a1,a2) \<noteq> (a12,a13) \<and> (a1,a2) \<noteq> (a13,a12) \<and> (a1,a2) \<noteq> (a22,a23) \<and> (a1,a2) \<noteq> (a23,a22))"

lemma ps_refl:"reflp possible_switch"
  apply(rule reflpI)
  by(case_tac x;simp)

lemma ps_sym:"symp possible_switch"
  apply(rule sympI)
  by(case_tac x;simp)

lemma "possible_switch a1 a2 \<Longrightarrow> sect a1 = sect a2"
  by simp

datatype train = T1 | T2

instance train::countable
  by countable_datatype

class railwaystate =
  fixes position::"'a \<Rightarrow> train \<Rightarrow> access"
  fixes isgreen::"'a \<Rightarrow> access \<Rightarrow> bool"
  fixes isopen::"'a \<Rightarrow> access \<Rightarrow> bool"


type_synonym state =  "(access\<Rightarrow>bool) \<times> (train \<Rightarrow> access) \<times> (access \<Rightarrow> bool)"

datatype State = S state

instantiation State::railwaystate
begin

fun isgreen_State::"State \<Rightarrow> access \<Rightarrow> bool"where
"isgreen_State (S (green, _, _)) = green"

fun position_State::"State \<Rightarrow> train \<Rightarrow> access"where
"position_State (S (_ ,tposition, _)) = tposition"

fun isopen_State::"State \<Rightarrow> access \<Rightarrow> bool"where
"isopen_State (S (_, _, opn)) = opn"
instance
  by standard
end





datatype controlaction = setswitch access access | setgreen access | setred access | setenter train access

instance controlaction::countable
  by countable_datatype

datatype reaction = C controlaction | reject

instance reaction ::countable
  by countable_datatype


datatype action = enter train access | opens access access | getgreen access | getred access

fun physical_transition::"State \<Rightarrow> action \<Rightarrow> (State)"where
"physical_transition s (enter t0 a) = (if (sect(co a) = sect(position s t0)) then ((S (isgreen s,(\<lambda>t. if t = t0 then a else position s t),isopen s))) else s)"|
"physical_transition s (opens c b) = (if possible_switch c b then (S (isgreen s, position s, (\<lambda>a. (sect c \<noteq> sect a \<and> isopen s a) \<or> (sect c = sect a \<and> (a = b \<or> a = c))))) else s)"|
"physical_transition s (getgreen c) =  S ((\<lambda>a. isgreen s a \<or> a = c), position s, isopen s)"|
"physical_transition s (getred c) = S ((\<lambda>a. isgreen s a \<and> a \<noteq> c), position s, isopen s)"

fun init_isgreen::"access \<Rightarrow> bool"where
"init_isgreen a = False"

fun init_position::"train \<Rightarrow> access"where
"init_position T1 = a11"|
"init_position T2 = a22"

fun init_open::"access \<Rightarrow> bool"where
"init_open a23 = False"|
"init_open a13 = False"|
"init_open _ = True"


definition initstate::"(State \<times> reaction stream) set"where
"initstate = {((S (init_isgreen, init_position, init_open)),\<epsilon>)}"

fun securetransition ::"State \<Rightarrow> controlaction \<Rightarrow> (State\<times> reaction stream)"where
"securetransition s (setswitch c b) =  (physical_transition s (opens c b), \<up>(C (setswitch c b)))"|
"securetransition s (setgreen c) =  (physical_transition s (getgreen c), \<up>(C (setgreen c)))"|
"securetransition s (setred c) = (physical_transition s (getred c), \<up>(C (setred c)))"|
"securetransition s (setenter t0 a) = (physical_transition s (enter t0 a), \<up>(C (setenter t0 a)))"

definition securestate::"State \<Rightarrow> bool"where
"securestate s \<equiv> \<forall>t1 t2. close (position s t1) (position s t2) \<longrightarrow> t1 = t2 "

definition securestates::"State set"where
"securestates = Collect securestate"

definition safelight::"State \<Rightarrow> access \<Rightarrow> bool"where
"safelight s a = (isopen s a \<and> isopen s (co a) \<and> (\<forall>b. (close a b \<and> isgreen s b) \<longrightarrow> (((sect a = sect (co b)\<and> sect(co a) = sect b) \<or> a = b))))"

lemma "safelight s a \<Longrightarrow> close a b \<Longrightarrow> a\<noteq> b \<Longrightarrow>  isgreen s b \<Longrightarrow> sect a = sect (co b)"
  apply(simp add: safelight_def)
  by auto

lemma safelight_trainindependent[simp]:"safelight (S (f,g,h)) a \<Longrightarrow> safelight (S (f,g',h)) a"
  by(simp add: safelight_def)

lemma close_sym[simp]:"close a b \<Longrightarrow> close b a"
  by(simp add: close_def)

lemma close_symp[simp]:"symp close"
  apply(rule sympI)
  by(simp)


lift_definition sec_controller::"(State,controlaction,reaction stream)automaton"is
"((\<lambda>s a. {securetransition s a}),initstate)"
  apply(auto)
  by (simp add: initstate_def)


definition controllerinv::"State \<Rightarrow> bool"where
"controllerinv s \<equiv> securestate s"

lemma controllerinv_controller:"\<not> (reachableStates sec_controller \<subseteq> {s. controllerinv s})"
  apply(simp add: reachableStates_def)
  apply(subst reachable_unfold)
  apply(subst reachable_unfold)
  apply auto
  apply(subgoal_tac "\<not>(\<Union>x\<in>autInitConfig\<cdot>sec_controller. fst ` \<Union> (range ((autTransition\<cdot>sec_controller) (fst x)))) \<subseteq> Collect controllerinv")
  apply auto
  apply(simp add: autTransition.rep_eq autInitConfig.rep_eq sec_controller.rep_eq)
  apply(simp_all add: controllerinv_def securestate_def initstate_def)
  apply(subgoal_tac "\<not>fst ` ({securetransition (S (init_isgreen, init_position, init_open)) (setenter T1 a21)}) \<subseteq> Collect controllerinv")
  apply blast
  apply auto
  apply(subgoal_tac "close (position (S (init_isgreen, \<lambda>t. if t = T1 then a21 else position (S (init_isgreen, init_position, init_open)) t, init_open)) T1) (position (S (init_isgreen, \<lambda>t. if t = T1 then a21 else position (S (init_isgreen, init_position, init_open)) t, init_open)) T2)")
  using controllerinv_def securestate_def 
  apply (meson train.distinct(1))
  by(simp add: close_def)
 
lemma contr_secure:"\<not>reachableStates sec_controller \<subseteq> securestates"
  using controllerinv_controller by(auto simp add: controllerinv_def securestates_def)

end