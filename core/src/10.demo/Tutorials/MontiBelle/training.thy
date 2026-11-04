theory training
  imports spf.SPFComp sps.SPSComp bundle.SB stream.EventStream 
          bundlelocale.SBEGen
          
begin



text\<open>You can use Slack if you have questions. You should already have
access to @{url montibelle.slack.com}, there the channel \<open>#isabelle\<close>
can be used.\<close>


text\<open>Read through the @{theory user.Datatypes} theory.\<close>



definition nonmono::"'a \<Rightarrow> 'b" where
"nonmono = undefined"


lemma [simp]:"\<not>monofun nonmono"
  sorry

lemma "\<not>monofun (\<lambda>a. nonmono a)"
  by simp



lemma intro: assumes"(n::natural)>0"
      and "m>0"
    shows "n+m>0"
  apply(rule pos_add_strict)
  by(simp add: assms)+


lemma shows "(\<Lambda> x. x)\<cdot>x = id x"
  apply(subst beta_cfun)
  apply(simp)
  unfolding id_def
  ..






lemma induex: 
  assumes "Fin n < #s"
  and "True"
  shows " snth n (sscanlAOne (\<lambda> s n::nat. ((s+1),(n+s))) m\<cdot>s) =
          snth n s + n + m"
text\<open>The lemma is separated into an assumption and show part. The 
assumptions are often useful in a induction proof. To use them, they
can be added to the goal 
using \<open>using assms\<close> before starting the induction proof. If there 
are more than one assumptions, the relevant ones can be obtained by 
adding a number like shown below. Here, only the first assumption is 
relevant. For some induction proofs, the admissibility @{const adm}
of a predicate has to be shown. Additional assumptions might 
contradict or help the admissibility of a predicate, check them with 
care.\<close>
using assms(1)
proof(induction n arbitrary: s m)
  case 0
  then show ?case
    by(cases s;simp add: sscanlAOne_def)
next
  case (Suc n)
  then show ?case
    by(cases s;simp add: sscanlAOne_def)
qed

text\<open>Note that the following lemma is not provable by induction, 
even though it directly follows from the last lemma @{thm induex}, 
because it is only an instance were the variable \<open>m\<close> is set to \<open>0\<close>.
But this leads to the problem, that \<open>0\<close> cannot be set to be 
arbitrary. This shows, that it is useful, easier and often necessary
to proof a generalized version of a property. Here, the induction 
proof problem is hinted and then the same lemma is proven by using 
@{thm induex}.\<close>

lemma 
  assumes "Fin n < #s"
  shows " snth n (sscanlAOne (\<lambda> s n::nat. ((s+1),(n+s))) 0\<cdot>s) =
          snth n s + n"
  using assms
proof(induction n arbitrary: s)
case 0
  then show ?case 
    by(cases s;simp add: sscanlAOne_def)
next
  case (Suc n)
  then show ?case 
    apply(cases s;simp)
oops

lemma
  assumes "Fin n < #s"
  shows " snth n (sscanlAOne (\<lambda> s n::nat. ((s+1),(n+s))) 0\<cdot>s) =
          snth n s + n"
  using induex assms(1) by auto


lemma
  assumes "Fin n < #s"
  shows " snth n (sscanlAOne (\<lambda> s n::nat. ((s+1),(n+s))) 0\<cdot>s) =
          snth n s + n"
  apply(insert induex[of n s 0] assms(1)) 
  by simp

lemma "\<exists>n. n = 0"
  apply(rule exI [where x="0"])
  ..



definition noncont::"'a \<Rightarrow> 'b" where
"noncont = undefined"

lemma "monofun noncont"
  oops

lemma "\<not>cont noncont"
  oops


definition contfun::"'a \<Rightarrow> 'b"where
"contfun = undefined"

lemma "cont contfun"
  oops


definition pred1::"'a \<Rightarrow> bool" where
"pred1 = undefined"

lemma "\<not>adm pred1"
  oops


pcpodef XY = "{something}"
  oops



definition add2::"nat stream \<rightarrow> nat stream" where
"add2 = undefined"


fixrec add2fix::"nat stream \<rightarrow> nat stream" where
"add2fix = undefined"

lemma "add2 = add2fix"
  oops




text\<open>Proof that the values of natstream are equivalent to 
the universe @{const UNIV} of @{type nat}. You may define and proof 
additional lemmas, but each proof should be less than 10 Lines long!\<close>
lemma "ValuesOfnatstream = universe"
  oops

text\<open>Use the @{const smap} function to define a function over 
streams that inverts the input bool tone stream (tip: @{const TOneMsg})\<close>

definition inverter::"bool tone stream \<rightarrow> bool tone stream" where
"inverter = undefined"


lemma "weak inverter"
  oops


lemma "inverter oo inverter = ID"
  oops


definition inverterLift::"M stream \<rightarrow> M stream" where
"inverterLift = undefined"


text\<open>Define three domain types (In,Intern,Out), each with one 
channel (not cempty). First, define a subset of the channel type as 
a new type. Then instantiate the new type as a @{class chan} and 
@{class finite} without using sledgehammer. Afterwards instantiate
it as a @{class tschan}. The instantiation proof should work for all
three instantiations without any variations.\<close>

typedef In = "{undefined::channel}" 
  sorry 

instantiation In::"{finite,chan}"
begin
instance
  sorry
end

instance In::tschan
  sorry

typedef Intern = "{undefined::channel}"
  by simp

instantiation Intern::"{finite,chan}"
begin
instance
  sorry
end

instance Intern::tschan
  sorry

typedef Out = "{undefined::channel}"
  by simp

instantiation Out::"{finite,chan}"
begin
instance
  sorry
end

instance Out::tschan
  sorry


definition almostSB::"In \<Rightarrow> M stream" where
"almostSB = undefined"

lemma "\<not>lsb_well almostSB"
  oops

text\<open>Define a In SB with the stream \<open>(\<up>True)\<^sup>\<infinity>\<close> and the 
\<open>lift_definition\<close> keyword.\<close>

lift_definition inSB::"In\<^sup>\<Omega>" is
"undefined"
  sorry




lift_definition notweak::"'In\<^sup>\<Omega> \<rightarrow> Out\<^sup>\<Omega>" is
"undefined"
  sorry

lemma "\<not>weak notweak"
  oops


lift_definition invert1::"In\<^sup>\<Omega> \<rightarrow> Intern\<^sup>\<Omega>"is
"undefined"
  sorry


lift_definition invert2::"Intern\<^sup>\<Omega> \<rightarrow> Out\<^sup>\<Omega>"is
"undefined"
  sorry


lemma "\<not>strong invert1"
  oops

text\<open>Proof that the output stream is equal to the input stream on 
inSB. Lemmata like @{thm spfcomp_unfold} might help. Furthermore, 
\<open>rep_eq\<close> lemmata that remove  @{const Abs_cfun} and  @{const Abs_lsb}
 automatically (put them in simp) is helpful for @{const invert1} and 
@{const invert2}. Edit the lemma to restrict the output of the composition
to the output of the second inverter.\<close>


thm Abs_lsb_inverse

lemma "(invert1 \<otimes> invert2)\<cdot>(inSB\<star>) \<^enum> (Abs cout) = inSB \<^enum> (Abs cin)"
  oops



definition sps1::"(In\<^sup>\<Omega> \<rightarrow> Out\<^sup>\<Omega>) set" where
"sps1 = undefined"

definition sps2::"(In\<^sup>\<Omega> \<rightarrow> Out\<^sup>\<Omega>) set" where
"sps2= undefined"

lemma "sps1 \<subseteq> sps2"
  oops



definition constrIn::"bool tone \<Rightarrow> In \<Rightarrow> M" where
"constrIn = undefined"

interpretation inSBE: sbeGen constrIn
  sorry

definition constrIntern::"bool tone \<Rightarrow> Intern \<Rightarrow> M" where
"constrIntern = undefined"

interpretation internSBE: sbeGen constrIntern
  sorry


end
