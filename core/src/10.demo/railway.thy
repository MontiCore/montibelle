theory railway
  imports stream.StreamAutomaton
begin


datatype sections = s1 | s2 | s3 | s4 | s5 | s6 |s7

instance sections::countable
  by countable_datatype

datatype access = a11 | a12 | a21 | a22 | a31 | a32 | a41 | a42 | a43 | a51 | a52 | a61 | a62 | a71 | a72 | a73

instance access::countable
  by countable_datatype

fun sect::"access \<Rightarrow> sections"where
"sect (a11) = s1"|
"sect (a12) = s1"|
"sect (a21) = s2"|
"sect (a22) = s2"|
"sect (a31) = s3"|
"sect (a32) = s3"|
"sect (a41) = s4"|
"sect (a42) = s4"|
"sect (a43) = s4"|
"sect (a51) = s5"|
"sect (a52) = s5"|
"sect (a61) = s6"|
"sect (a62) = s6"|
"sect (a71) = s7"|
"sect (a72) = s7"|
"sect (a73) = s7"

fun co::"access \<Rightarrow> access"where
"co (a11) = a73"|
"co (a12) = a21"|
"co (a21) = a12"|
"co (a22) = a31"|
"co (a31) = a22"|
"co (a32) = a41"|
"co (a41) = a32"|
"co (a42) = a51"|
"co (a43) = a61"|
"co (a51) = a42"|
"co (a52) = a72"|
"co (a61) = a43"|
"co (a62) = a71"|
"co (a71) = a62"|
"co (a72) = a52"|
"co (a73) = a11"

lemma co_inv:"co (co a) = a"
  by(cases a;simp)

definition close::"access \<Rightarrow> access \<Rightarrow> bool"where
"close a b = (sect a = sect b \<or> (\<exists>c. sect a = sect (co c) \<and> sect c = sect b))"

fun possible_switch:: "access \<Rightarrow> access \<Rightarrow> bool"where
"possible_switch a1 a2 = (sect a1 = sect a2 \<and>  (a1,a2) \<noteq> (a42,a43) \<and> (a1,a2) \<noteq> (a43,a42) \<and> (a1,a2) \<noteq> (a72,a71) \<and> (a1,a2) \<noteq> (a71,a72))"

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



type_synonym state =  "(access\<Rightarrow>bool) \<times> (train \<Rightarrow> access) \<times> (access \<Rightarrow> bool)"

datatype State = S state

fun isgreen::"State \<Rightarrow> access \<Rightarrow> bool"where
"isgreen (S (green, _, _)) = green"

fun position::"State \<Rightarrow> train \<Rightarrow> access"where
"position (S (_ ,tposition, _)) = tposition"

fun isopen::"State \<Rightarrow> access \<Rightarrow> bool"where
"isopen (S (_, _, opn)) = opn"


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
  apply(simp add: close_def)
  by (metis co_inv)

lemma close_symp[simp]:"symp close"
  apply(rule sympI)
  by(simp)




datatype action = enters train access | openUp access access | setColor access bool

fun physical_transition::"State \<Rightarrow> action \<Rightarrow> (State)"where
"physical_transition s (enters t0 a) = (if (sect(co a) = sect(position s t0)) then ((S (isgreen s,(\<lambda>t. if t = t0 then a else position s t),isopen s))) else s)"|
"physical_transition s (openUp c b) = (if possible_switch c b then (S (isgreen s, position s, (\<lambda>a. (sect c \<noteq> sect a \<and> isopen s a) \<or> (sect c = sect a \<and> (a = b \<or> a = c))))) else s)"|
"physical_transition s (setColor c True) =  S ((\<lambda>a. isgreen s a \<or> a = c), position s, isopen s)"|
"physical_transition s (setColor c False) = S ((\<lambda>a. isgreen s a \<and> a \<noteq> c), position s, isopen s)"

datatype reaction = reject

instance reaction ::countable
  by countable_datatype

fun init_isgreen::"access \<Rightarrow> bool"where
"init_isgreen a = False"

fun init_position::"train \<Rightarrow> access"where
"init_position T1 = a21"|
"init_position T2 = a73"

fun init_open::"access \<Rightarrow> bool"where
"init_open a43 = False"|
"init_open a71 = False"|
"init_open _ = True"


definition initstate::"(State \<times> reaction stream) set"where
"initstate = {((S (init_isgreen, init_position, init_open)),\<epsilon>)}"


fun isfree::"State \<Rightarrow> access \<Rightarrow> bool"where
"isfree s a = (\<forall>t. sect (position s t) \<noteq> sect a)"

fun protected::"State \<Rightarrow> sections \<Rightarrow> bool"where
"protected s sec = (\<forall>a. sect (a) = sec \<longrightarrow> \<not> isgreen s a \<and> \<not> isgreen s (co a))"

fun safegreen::"State \<Rightarrow> access \<Rightarrow> bool"where
"safegreen s a = (safelight s a \<and> (\<forall>b. close a b \<and> sect(co a) \<noteq> sect b \<longrightarrow> isfree s b))"

fun securetransition ::"State \<Rightarrow> action \<Rightarrow> (State\<times> reaction stream)"where
"securetransition s (openUp c b) = (if isfree s c \<and> protected s (sect c) then (physical_transition s (openUp c b),\<epsilon>) else (s,\<up>reject))"|
"securetransition s (setColor c True) = (if safegreen s c then (physical_transition s (setColor c True),\<epsilon>) else (s,\<up>reject))"|
"securetransition s (setColor c False) = (physical_transition s (setColor c False), \<epsilon>)"|
"securetransition s (enters t0 a) = (if isgreen s a then (physical_transition s (enters t0 a),\<epsilon>)  else (s,\<up>reject))"

lift_definition sec_controller::"(State,action,reaction stream)automaton"is
"((\<lambda>s a. {securetransition s a}),initstate)"
  apply(auto)
  by (simp add: initstate_def)




definition lightinv::"State \<Rightarrow> bool"where
"lightinv s \<equiv> \<forall>a. isgreen s a \<longrightarrow> safelight s a"

definition trainfreeinv::"State \<Rightarrow> bool"where
"trainfreeinv s \<equiv> \<forall>a. isgreen s a \<longrightarrow> (\<forall>b t. (close a b \<and> position s t = b) \<longrightarrow> (sect b = sect a \<or> sect b = sect (co a)))"

definition controllerinv::"State \<Rightarrow> bool"where
"controllerinv s \<equiv> securestate s \<and> lightinv s \<and> trainfreeinv s"

lemma init_secureinv:assumes "s \<in> fst` initstate"
  shows"securestate s"
  using assms apply (auto simp add: initstate_def securestate_def close_def)
   apply(case_tac t1;case_tac t2;simp)
  apply(case_tac t1;case_tac t2;simp)
  apply (smt co.simps(14,15,16) sect.elims
      sect.simps(1,11,13)
      sections.distinct(1,11,17,19,21,29,35,39,41))
  by (smt co.simps(3,4) sect.elims sect.simps(2,5)
      sections.distinct(13,15,17,19,2,21,29)
      sections.simps(12))

lemma init_lightinv:assumes "s \<in> fst` initstate"
  shows"isgreen s a \<Longrightarrow> safelight s a"
  using assms by(simp add: initstate_def)

lemma init_trainfreeinv:assumes "s \<in> fst` initstate"
  shows"trainfreeinv s"
  using assms by(simp add: initstate_def trainfreeinv_def)

lemma controllerinv_init:"s \<in> fst` initstate \<Longrightarrow> controllerinv s"
  apply(auto simp add: controllerinv_def)
  using init_secureinv securestates_def apply fastforce
  using init_lightinv lightinv_def apply fastforce
  using init_trainfreeinv by fastforce

lemma controllerinv_controller:"reachableStates sec_controller \<subseteq> {s. controllerinv s}"
  apply(rule reach_statinv_substet)
  defer
  using controllerinv_init
  apply(simp add: autTransition.rep_eq autInitConfig.rep_eq sec_controller.rep_eq)
  apply(auto simp add: autTransition.rep_eq autInitConfig.rep_eq sec_controller.rep_eq)
  apply(case_tac msg;simp)
  apply(simp_all add: controllerinv_def securestate_def lightinv_def trainfreeinv_def)
  apply (simp add: safelight_def) 
  apply (smt close_def close_sym)
  apply (simp add: safelight_def) 
  apply (metis co_inv)
  apply(case_tac x32;simp)
  apply (simp add: safelight_def) 
  apply (smt close_sym)
  using safelight_def by fastforce

lemma contr_secure:"reachableStates sec_controller \<subseteq> securestates"
  using controllerinv_controller by(auto simp add: controllerinv_def securestates_def)


end