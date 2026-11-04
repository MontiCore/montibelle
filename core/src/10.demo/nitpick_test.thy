theory nitpick_test

imports HOLCF

begin
default_sort "domain"

domain message = A | B | C
domain 'a stream = conc (hd:: 'a) (lazy rt::"'a stream")
print_theorems


fun nth::"nat \<Rightarrow> 'a stream \<rightarrow> 'a" where
"nth 0       = hd"  |
"nth (Suc n) = (nth n) oo rt"


fixrec onlyA::"message stream" where
"onlyA = conc\<cdot>A\<cdot>onlyA"

declare onlyA.simps [simp del]


lemma "nth n\<cdot>onlyA = A"
  apply(induction n; subst onlyA.simps)
  by simp+



definition bot_msg::"message" where
"bot_msg = \<bottom>"

setup\<open>
Nitpick_HOL.register_codatatype_global @{typ "message"}
  "" 
  (map dest_Const [@{term A},@{term B},@{term C}, @{term bot_msg}])\<close>

lemma "a = A"
  nitpick[debug]
  oops


definition bot_u::"'a stream" where
"bot_u = \<bottom>"
definition conc_u::"'a \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
"conc_u a as = conc\<cdot>a\<cdot>as"



definition stream_cases:: "'a \<Rightarrow> ('m \<Rightarrow> 'm stream \<Rightarrow> 'a) \<Rightarrow> 'm stream \<Rightarrow> 'a" where
"stream_cases Bot Conc s = (if(s=\<bottom>) then Bot else Conc (hd\<cdot>s) (rt\<cdot>s))"

setup\<open>
Nitpick_HOL.register_codatatype_global @{typ "'a stream"}
  @{const_name stream_cases}
  (map dest_Const [@{term bot_u},@{term conc_u}])\<close>

lemma "(a::nat) = b"  
  nunchaku
  oops

lemma "a = (b::message stream)"
  nitpick[expect=genuine]
  oops

lemma "z \<noteq> conc_u (t::message) a"
  nitpick[expect=genuine]
  oops


lemma "as \<noteq> conc_u A (conc_u A bot_u)"
  nitpick[expect=none, debug, show_all]
  oops

lemma "as \<noteq> conc_u A (conc_u A bs)"
  nitpick[expect=genuine]
  oops

lemma "conc_u FF (conc_u TT bot_u) \<noteq> as"
  nitpick[expect=genuine]
  oops

lemma "conc_u (Def (1::nat)) (conc_u (Def 2) (conc_u (Def (t*12+10)) (conc_u (Def 10) bot_u))) \<noteq> as"
  nitpick[expect=genuine]
  oops





lemma "hd\<cdot>(conc_u a b) = A"
  oops


definition hd_u::"'a stream \<Rightarrow> 'a" where
"hd_u s = hd\<cdot>s"

lemma [nitpick_simp]: "hd_u (conc_u a b) = a"
  by(simp add: hd_u_def conc_u_def)
lemma [nitpick_simp]: "hd_u (bot_u) = bot_msg"
  by(simp add: hd_u_def conc_u_def bot_msg_def bot_u_def)

lemma "hd_u(conc_u a b) = A"
  nitpick[expect=genuine]
  oops

lemma "hd_u(bot_u) = (a::message)"
  nitpick[expect=genuine]
  oops



definition rt_u::"'a stream \<Rightarrow> 'a stream" where
"rt_u = Rep_cfun rt"

lemma [nitpick_psimp]: "a\<noteq>bot_msg \<Longrightarrow> rt_u (conc_u a b) = b"
  by(simp add: conc_u_def rt_u_def bot_msg_def)
lemma [nitpick_psimp]: "a=bot_msg \<Longrightarrow> rt_u (conc_u a b) = bot_u"
  by(simp add: conc_u_def rt_u_def bot_msg_def bot_u_def)
lemma [nitpick_psimp]: "rt_u (bot_u) = bot_u"
  by(simp add: rt_u_def bot_u_def)

lemma []: "rt_u s = stream_cases bot_u (\<lambda>a as. as) s"
  by(simp add: rt_u_def stream_cases_def bot_u_def)

lemma "rt_u (conc_u A b) = b"
  nitpick[expect=none] 
  oops

lemma "rt_u (conc_u A b) \<noteq> b"
  nitpick[expect=genuine] 
  oops

lemma "conc_u a (conc_u b as) = (as::message stream)"
  nitpick[expect=genuine]
  oops

lemma "rt_u ( rt_u (rt_u as)) = (as::message stream)"
  nitpick[expect=genuine]
  oops





definition nth_u::"nat \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"nth_u a s = nth a\<cdot>s"


lemma [nitpick_unfold]:"nth_u 0 s =  stream_cases \<bottom> (\<lambda>a as. a) s"
  by(simp add: nth_u_def conc_u_def stream_cases_def)
lemma [nitpick_psimp]:"a\<noteq>(\<bottom>::nat lift) \<Longrightarrow> nth_u (Suc n) (conc_u a as) = nth_u n as"
  by(simp add: nth_u_def conc_u_def bot_msg_def)

lemma [nitpick_unfold]: "nth_u n s = 
  stream_cases (hd_u s) (\<lambda> a as. case n of (Suc m) \<Rightarrow> nth_u m as | 0 \<Rightarrow> a) s"
  oops

lemma "nth_u 5 s \<noteq> Def (5::nat)"
  nitpick[expect=genuine]

  oops





default_sort type

codatatype (lset:'a)llist
  =lnull:LNil | LCons(lhd:'a) (ltl:"'a llist")


lemma "LCons (a::nat) (LCons b (LCons c (LCons d LNil))) \<noteq> z"
  nitpick[expect=genuine]
  oops

lemma "LCons (10::nat) (LCons 11 (LCons 12 (LNil))) \<noteq> z"
  nitpick[expect=none]
  oops

lemma "LCons (True) (LCons True (LNil)) \<noteq> z"
  nitpick[expect=none]
  oops

datatype 'a myList = CCons 'a "'a myList" | NNil

lemma "(CCons (1022::nat) (CCons 2 (CCons 1 (CCons (1::nat) (CCons 2 (CCons 1 (CCons (1::nat) (CCons 2 (CCons 1 NNil)))))))))  \<noteq> z"
  nitpick
  oops

lemma "(1::nat)#2#2#3#600#8#2#1023#[] \<noteq> z"
  nitpick[expect=genuine]
  oops

lemma "(5001::nat) \<noteq> z"
  nitpick[expect=none]
  oops





end