theory sinftimes_test 
                                                            
imports stream.Stream inc.Prelude inc.HOLCFcodegen  "HOL-Library.Code_Lazy" "HOL-Library.Extended_Nat"
                                                             
begin 

default_sort "countable"



definition lscons_lazy::"'a \<Rightarrow> ('a stream lazy) \<Rightarrow> 'a stream" where
"lscons_lazy \<equiv> \<lambda>a0 a1. lscons\<cdot>(Iup (Discr a0))\<cdot>(force a1)"


(*
lemma lslazy_code_abbrev[code_abbrev]:" lscons_lazy a0 a1 = lscons\<cdot>(Iup (Discr a0))\<cdot>(force a1)"
  by(simp add: lscons_lazy_def)
*)

lemma up_code_abbrev [code_abbrev]:"Iup a = up\<cdot>a"
  apply (simp add: up_def)
  apply(subst beta_cfun, simp add: cont_Iup)
  ..

(*
lemma [code_abbrev]: "updis x && xs = \<up>x \<Zcat> xs"
  using lscons_conv by blast
*)





definition equal_stream2::"'a stream \<Rightarrow> 'a stream \<Rightarrow> bool" where                   
"equal_stream2 a b \<equiv> (a = b)"

code_printing
code_module test  \<rightharpoonup> (SML)
\<open>fun streamequal a b = a=b \<close> for constant equal_stream2
|constant equal_stream2 \<rightharpoonup> (SML) "streamequal"

instantiation stream::("{equal,countable}") equal
begin
definition equal_stream::"'a stream \<Rightarrow> 'a stream \<Rightarrow> bool" where                   
"equal_stream a b \<equiv> equal_stream2 a b "
instance
  apply(intro_classes)
  by(simp add: equal_stream2_def equal_stream_def)
end

setup_domain "lnat" "lnsuc" 

definition equal_lnat2::"lnat \<Rightarrow> lnat \<Rightarrow> bool" where                   
"equal_lnat2 a b \<equiv> (a = b)"

code_printing
code_module test2  \<rightharpoonup> (SML)
\<open>fun lnatequal a b = a=b \<close> for constant equal_lnat2
|constant equal_lnat2 \<rightharpoonup> (SML) "lnatequal"

instantiation lnat:: equal
begin
definition equal_lnat::"lnat \<Rightarrow> lnat \<Rightarrow> bool" where                   
"equal_lnat a b \<equiv> equal_lnat2 a b "
instance
  apply(intro_classes)
  by(simp add: equal_lnat2_def equal_lnat_def)
end



setup_domain "'a stream" "lscons_lazy" 

setup \<open>Sign.mandatory_path "LNat"\<close>

old_rep_datatype Fin Inf'
  apply (metis ninf2Fin)
  by simp+
setup \<open>Sign.parent_path\<close>


primrec the_lnat :: "lnat \<Rightarrow> nat" where
"the_lnat (Fin n) = n"

primrec lnat2enat :: "lnat \<Rightarrow> enat" where
"lnat2enat (Fin n) = n" |
"lnat2enat (Inf') = (\<infinity>::enat)"

lemma "lnat2enat n = (if (n\<noteq>Inf') then (inv Fin n) else (\<infinity>::enat))"
  by (metis Fin_0 add.right_neutral add_eq_0_iff_both_eq_0 plus_lnat_def lnat2enat.simps(1) lnat2enat.simps(2))


lemma shd_c[code]:"shd (lscons_lazy a a0) = a"
  apply(simp add: shd_def lscons_lazy_def)
  by (simp add: up_code_abbrev)
  

definition sinf ::" 'a \<Rightarrow> 'a stream" where
"sinf \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda>s. (updis s && (h s))))" 

definition stake1::"nat \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"stake1 \<equiv> stake"

lemma [code_abbrev]:"stake1 = stake"
  by (simp add: stake1_def)

lemma[ccode]:"stake1 0\<cdot>sa = \<bottom>" and
[ccode]:"stake1 n\<cdot>\<bottom> = \<bottom>" and
[ccode]:"stake1 (Suc n)\<cdot> ((lscons_lazy a as)) = lscons_lazy  a (delay (\<lambda>_. stake1 (n)\<cdot> (force as)))"
   apply(simp add:stake1_def lscons_lazy_def)+
  by(simp add: force_delay)

definition sdrop1::"nat \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"sdrop1 \<equiv> sdrop"

lemma [code_abbrev]:"sdrop1 = sdrop"
  by (simp add: sdrop1_def)

lemma[ccode]:"sdrop1 0\<cdot>sa = sa" and
[ccode]:"sdrop1 n\<cdot>\<bottom> = \<bottom>" and
[ccode]:"sdrop1 (Suc n)\<cdot> ((lscons_lazy a as)) = force(delay (\<lambda>_. sdrop1 (n)\<cdot> (force as)))"
   apply(simp add:sdrop1_def lscons_lazy_def)+
  apply(simp add: force_delay)
  by (simp add: lscons_conv up_code_abbrev)

function toList::"nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
"toList 0 s = []" |
"toList n \<bottom> = []" |
"toList (Suc n) (lscons_lazy a as) = [a] @ (toList n (force as))"
  apply(auto)
  defer
  apply (simp add: inst_up_pcpo lscons_lazy_def)
  apply (metis shd_c)
  apply (simp add: inst_up_pcpo lscons_lazy_def)
proof -
  fix P :: bool and a :: nat and b :: "'a stream"
  assume a1: "\<And>s. a = 0 \<and> b = s \<Longrightarrow> P"
  assume a2: "\<And>n aa as. a = Suc n \<and> b = lscons_lazy aa as \<Longrightarrow> P"
  assume a3: "\<And>n. a = n \<and> b = \<epsilon> \<Longrightarrow> P"
  obtain aa :: "'a stream \<Rightarrow> 'a" and ss :: "'a stream \<Rightarrow> 'a stream" where
    f4: "\<forall>s. s = \<epsilon> \<or> s = \<up>(aa s) \<Zcat> ss s"
    by (metis scases)
  { assume "\<exists>s. s \<noteq> \<epsilon> \<and> s = b"
    then have "\<exists>f a. \<up>a \<Zcat> f () = b"
    proof -
      obtain aaa :: "'a stream \<Rightarrow> 'a" and ssa :: "'a stream \<Rightarrow> 'a stream" where
        "\<forall>s. \<up>(aaa s) \<Zcat> ssa s = s \<or> stream_bottom_nc = s"
        by (metis \<open>\<And>thesis. (\<And>aa ss. \<forall>s. s = \<epsilon> \<or> s = \<up>(aa s) \<Zcat> ss s \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> stream_bottom_code_abbrev)
      then show ?thesis
        using \<open>\<exists>s. s \<noteq> \<epsilon> \<and> s = b\<close> stream_bottom_code_abbrev by force
    qed
    then have P
      using a2 a1 by (metis force_delay lscons_conv lscons_lazy_def not0_implies_Suc up_code_abbrev) }
  then show P
    using a3 by blast
qed
termination
  by (metis "termination" in_measure lessI prod.sel(1) wf_measure)

lemma[code]:"toList (Suc n) (lscons_lazy a as) = [a] @ (toList n (force as))"
  by(simp)

lemma[code]:"toList 0 s = []"
  by simp

lemma[code]: "toList n \<bottom> = []"
  by simp



lemma [ccode]:"sconc s1\<cdot> \<epsilon> = s1" and
      [ccode]:"sconc \<epsilon>\<cdot>s2 = s2" and
      [ccode]:"sconc (lscons_lazy a as)\<cdot>s2 = 
                        lscons_lazy  a (delay (\<lambda>_. sconc (force as)\<cdot>s2))"
  apply (simp)+
  using sconc_scons'
  by (simp add: sconc_scons' force_delay lscons_lazy_def up_code_abbrev)


lemma [code]:"list2s ([]) = \<epsilon>" and
      [code]:"list2s (a#as) = lscons_lazy a (delay (\<lambda>_. (list2s as)))"
   apply auto
  by (simp add: force_delay lscons_conv lscons_lazy_def up_code_abbrev)

lemma[code]:"sinf (a) =  lscons_lazy a (delay (\<lambda>_.(sinf (a))))"
  apply (subst sinf_def [THEN fix_eq2], auto)
  apply (simp add: lscons_lazy_def)
  apply (simp add: up_code_abbrev)
  by (simp add: force_delay)


lemma [code_abbrev]:"slen\<cdot>lnx = len lnx"
  by (simp add: len_stream_def)


lemma [ccode]: "slen\<cdot>(\<epsilon>) = (0)" and 
      [ccode]: "slen\<cdot>((lscons_lazy a as)) = lnsuc\<cdot>(#(force as))"
  apply(subst slen_def [THEN fix_eq2], simp add: lnzero_def)
  apply (simp add: len_stream_def  lscons_lazy_def)
  apply (subst slen_def [THEN fix_eq2], simp add: lnle_def strictify_conv_if)
  by (simp add: inst_up_pcpo)

(*
lemma [code]:"Fin (Suc n) = lnsuc\<cdot>(Fin n)" and
      [code]:"Fin 0 = \<bottom>"
  apply simp
  by(simp add: lnzero_def)
*)

lemma [code]:"lnsuc_nc (Fin n) = Fin (Suc n)" and
      [code]:"lnat_bottom_nc = Fin 0" and
      [code]:"lnsuc_nc (Inf') = Inf'"
  apply (simp_all add: lnsuc_nc_def lnat_bottom_nc_def)
  by(simp add: lnzero_def)


lemma [code]:"plus (Fin 0) (Fin b) = (Fin b)" and
      [code]:"plus (Fin (Suc a)) (Fin b) = plus (Fin a) (Fin (Suc b))"
using lnzero_def plus_lnat0_r apply auto[1]
  by (simp add: lnat_plus_lnsuc)

lemma [code]:"(Fin 0) \<le> (Fin 0) = True" and
      [code]:"((Fin (Suc 0))) \<le> (Fin 0) = False" and
      [code]:"(Fin 0) \<le> ((Fin (Suc x))) = ((Fin 0) \<le> (Fin x))" and
      [code]:"(Fin (Suc (Suc x))) \<le> (Fin 0) = (((Fin (Suc x))) \<le> (Fin 0))" and
      [code]:"((Fin (Suc x))) \<le> ((Fin (Suc y))) = ((Fin x) \<le> (Fin y))"
  by(auto)

lemma [code_abbrev]:"(if (x=y) then False else (Fin x \<le> Fin y)) = (Fin x < Fin y)"
  by (simp add: less_le)



lemma [ccode]:"(lscons_lazy x0 (xs)) \<Zcat> y = 
                   (lscons_lazy x0 (delay (\<lambda>_.  (force xs) \<Zcat> y)))" and
      [ccode]:"(\<epsilon>) \<Zcat> z = z"
   apply(auto)
  by (simp add: force_delay lscons_conv lscons_lazy_def up_code_abbrev)

value "(lscons_lazy True (delay (\<lambda>_. \<epsilon>)))"

value "toList 99 ((lscons_lazy False (delay (\<lambda>_. (lscons_lazy True (delay (\<lambda>_. \<epsilon>)))))) \<Zcat>
           (lscons_lazy False (delay (\<lambda>_. (lscons_lazy True (delay (\<lambda>_. \<epsilon>)))))))"

value "(\<epsilon>) \<Zcat> (lscons_lazy False (delay (\<lambda>_. \<epsilon>)))"

value "(\<epsilon>) \<Zcat> (\<epsilon>::nat stream)"


value "toList 99 (sdrop 2\<cdot>(stake 7\<cdot>(sinf (True))))"

value [nbe] "slen\<cdot>(stake 16\<cdot>(sinf (True)))"

value  "(\<bottom>::lnat) \<le> (\<bottom>)"

value "(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>\<bottom>))))))) \<le>
           (lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>(lnsuc\<cdot>\<bottom>)))))))"

value "Fin 7 \<le> Fin 13"

value "stake 16\<cdot>(sinftimes ((\<epsilon>::nat stream)))"

value "(Fin 3 + Fin 5)"

definition id :: "'a \<Rightarrow> 'a" where
"id = (\<lambda> a. a)"

lemma identity :"id a = a"
  by (simp add: sinftimes_test.id_def)

value "Fin 4 < Fin 2"


end
