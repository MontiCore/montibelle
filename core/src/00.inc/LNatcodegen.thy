theory LNatcodegen

imports LNat Codegen Classes

begin

setup_domain "lnat" "lnsuc" 

setup \<open>Sign.mandatory_path "LNat"\<close>

old_rep_datatype Fin Inf'
  apply (metis ninf2Fin)
  by simp+
setup \<open>Sign.parent_path\<close>

instantiation lnat::bot_nc
begin
definition bot_nc_lnat :: "lnat" where "bot_nc_lnat \<equiv> 0 :: lnat"
instance
  apply(intro_classes)
  by(simp add: bot_nc_lnat_def lnzero_def)
end



primrec the_lnat :: "lnat \<Rightarrow> nat" where
"the_lnat (Fin n) = n" | 
"the_lnat Inf' = undefined"


definition equal_lnat2::"lnat \<Rightarrow> lnat \<Rightarrow> bool" where                   
"equal_lnat2 a b \<equiv> (a = b)"

code_printing
code_module test2  \<rightharpoonup> (SML)
\<open>fun lnatequal a b = a=b \<close> for constant equal_lnat2
|constant equal_lnat2 \<rightharpoonup> (SML) "lnatequal"



lemma [code]:"lnsuc_nc (Fin n) = Fin (Suc n)" and
      [code]:"lnat_bottom_nc = Fin 0" and
      [code]:"lnsuc_nc (Inf') = Inf'"
  apply (simp_all add: lnsuc_nc_def lnat_bottom_nc_def)
  by(simp add: lnzero_def)


(*
lemma [code]:"plus (Fin 0) (Fin b) = Fin b" and
      [code]:"plus (Fin (Suc a)) (Fin b) = plus (Fin a) ((Fin (Suc b)))"
  using lnzero_def plus_lnat0_r apply auto[1]
  by (simp_all add: lnat_plus_lnsuc)
 *)

lemma [code]:"(Fin 0) \<le> (Fin 0) = True" and
      [code]:"((Fin (Suc 0))) \<le> (Fin 0) = False" and
      [code]:"(Fin 0) \<le> ((Fin (Suc x))) = ((Fin 0) \<le> (Fin x))" and
      [code]:"(Fin (Suc (Suc x))) \<le> (Fin 0) = (((Fin (Suc x))) \<le> (Fin 0))" and
      [code]:"((Fin (Suc x))) \<le> ((Fin (Suc y))) = ((Fin x) \<le> (Fin y))"
  by(auto)



lemma min_lnat_exec [code_unfold]: "(min (n::lnat) (m::lnat)) = (if (m=Inf') then n else (if 
                              (n=Inf') then m else (min (the_lnat(n)) (the_lnat(m)))))"
  apply auto[1]
  by (metis less2nat_lemma lncases min.commute min_def the_lnat.simps(1))

lemma imply_lnat_len_less [code_abbrev]:"(if (x=Inf') then (\<forall>n\<in>UNIV. P n) 
                          else (((\<forall>n\<in>{0..((the_lnat((x))))}. 
            if n = the_lnat(x) then True else P n)))) = (\<forall>n::nat. n < (x::lnat) \<longrightarrow> P n)"
  apply(auto)[1]
  using ninf2Fin apply fastforce
  by (metis lnat_well_h1 neq_iff not_le the_lnat.simps(1))


lemma imply_lnat_len_less_add_one [code_abbrev]:"(if (x=Inf')
         then (\<forall>n\<in>UNIV. P n) else
        ((\<forall>n\<in>{0..((the_lnat((x))))}. 
            if ((n = the_lnat(x)) \<or> ((Suc n) = (the_lnat(x)))) then True else P n))) = (\<forall>n::nat. (n+1) < ((x::lnat)) \<longrightarrow> P n)"
  apply(auto)[1]
  apply (metis atMost_atLeast0 atMost_iff inf_ub less2nat less_le lnat_well_h2 not_le not_less_eq the_lnat.simps(1))
  by (metis le_less_Suc_eq less_linear lnat_well_h1 the_lnat.simps(1))


lemma le_eq [code]: "(Fin n < (x::lnat)) \<equiv> (if (x=Inf') then
             Code.abort STR ''infinite'' (\<lambda>_. Fin n < (x::lnat)) 
                      else (n < the_lnat(x)))" 
proof (induction x)
  case (Fin lnat)
  then show ?case
    by simp
next
  case Inf'
  then show ?case
    by simp
qed

lemma nat_all_enum [simp]: "(\<forall>m::nat. (m \<le> (n::nat)) \<longrightarrow> P m) \<equiv> (\<forall>m\<in>{0..n}.  P m)"
  using all_nat_less by presburger

lemma nat_all_enum_less: "(\<forall>m::nat. (m < (n::nat)) \<longrightarrow> P m) \<equiv> (if (n=0) then True else
                                                                   (\<forall>m\<in>{0..(minus n 1)}.  P m))"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: less_Suc_eq_le)
qed

lemma nat_reduce [simp]: "(\<forall>m::nat. (m < (n::nat)) \<and> (m < (q::nat)) \<longrightarrow> P m) \<equiv> (\<forall>m::nat. (m < (min n q)) \<longrightarrow> P m)"
  by simp

lemma nat_exist_enum: "(\<exists>m::nat > y. (m < (x::nat)) \<and> P m) \<equiv> (if (x=0) then False else 
                                                                        \<exists>m\<in>{(Suc y)..(minus x 1)}.  P m)"
proof (induction x)
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  then show ?case
    by (metis Suc_le_eq atLeastAtMost_iff diff_Suc_1 less_Suc_eq_le nat.simps(3)) 
qed

lemma smaller_exec : "(\<forall>m::nat<n. P m) = (if (n=0) then True else 
                                                    (\<forall>m\<in>{0..(minus n 1)}. P m))"
  by(auto)


lemma red_4_exec: "(\<forall>n::nat. Fin n < i \<and> Fin n < j \<and> Fin n < k \<and> Fin n < l \<longrightarrow> Q n) = 
    (if (i\<noteq>Inf' \<and> j\<noteq>Inf' \<and> k\<noteq>Inf' \<and> l\<noteq>Inf') then (let minimum = Min{the_lnat i, the_lnat j, the_lnat k, the_lnat l}
                          in (if minimum = 0 then True else (\<forall>n\<in>{0..(minus (minimum) 1)}. Q n)))
            else (\<forall>n::nat. Fin n < i \<and> Fin n < j \<and> Fin n < k \<and> Fin n < l \<longrightarrow> Q n))"
  apply(auto)[1]
  apply (metis Suc_pred le_eq le_imp_less_Suc min_less_iff_conj)
  by (simp add: le_eq)+

lemma red_3_exec: "(\<forall>n::nat. Fin n < i \<and> Fin n < j \<and> Fin n < k \<longrightarrow> Q n) =
    (if (i\<noteq>Inf' \<and> j\<noteq>Inf' \<and> k\<noteq>Inf') then (let minimum = Min{the_lnat i, the_lnat j, the_lnat k}
                          in (if minimum = 0 then True else (\<forall>n\<in>{0..(minus (minimum) 1)}. Q n)))
            else (\<forall>n::nat. Fin n < i \<and> Fin n < j \<and> Fin n < k \<longrightarrow> Q n))"
  apply(auto)[1]
  apply (metis Suc_pred le_eq le_imp_less_Suc min_less_iff_conj)
  by (simp add: le_eq)+

lemma red_2_exec: "(\<forall>n::nat. Fin n < i \<and> Fin n < j \<longrightarrow> Q n) = 
    (if (i\<noteq>Inf' \<and> j\<noteq>Inf') then (let minimum = Min{the_lnat i, the_lnat j}
                          in (if minimum = 0 then True else (\<forall>n\<in>{0..(minus (minimum) 1)}. Q n)))
            else (\<forall>n::nat. Fin n < i \<and> Fin n < j \<longrightarrow> Q n))"
  apply(auto)[1]
  apply (metis Suc_pred le_eq le_imp_less_Suc min_less_iff_conj)
  by (simp add: le_eq)+

lemma red_1_exec: "(\<forall>n::nat. Fin n < i \<longrightarrow> Q n) = 
    (if (i\<noteq>Inf') then (let minimum = the_lnat i
                          in (if minimum = 0 then True else (\<forall>n\<in>{0..(minus (minimum) 1)}. Q n)))
            else (\<forall>n::nat. Fin n < i \<longrightarrow> Q n))"
  apply(auto)[1]
  apply (simp add: atMost_atLeast0 le_eq)
  by (simp add: le_eq)+


definition lAdd_nc :: "lnat \<Rightarrow> lnat \<Rightarrow> lnat" where
  "lAdd_nc a \<equiv> (Rep_cfun ((Rep_cfun lAdd) a))"
lemma [code_abbrev]: "lAdd_nc a b = a+b"
  by(simp add: lAdd_nc_def plus_lnat_def ladd_insert)

lemma [code_abbrev]: "lAdd_nc a b = lAdd\<cdot>a\<cdot>b"
  by (simp add: lAdd_nc_def)

lemma [code]: "lAdd_nc =
  (\<lambda> ln1 ln2.
    case ln1
      of Fin n \<Rightarrow> (case ln2 of Fin m \<Rightarrow> n+m | \<infinity> \<Rightarrow> \<infinity>)
      | \<infinity> \<Rightarrow> \<infinity>
  )"
  using lAdd_nc_def ladd_def_h2 ladd_insert by presburger


lemma [nitpick_simp]:
  "lnsuc_nc x = (if (x = \<infinity>) then \<infinity> else Fin ((inv Fin) x) + 1)"
  by (metis lnsuc_nc_def UNIV_I fin_inj inv_into_f_f lnat_plus_fin lnat_plus_suc plus_lnat_def)

lemma "a \<noteq> lnsuc_nc (Fin 5)"
  oops


lemma [nitpick_simp]: "less_eq \<infinity> a = (a = \<infinity>)"
  and [nitpick_simp]: "less_eq a \<infinity> = True"
  and [nitpick_psimp]: "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> less_eq a b = less_eq ((inv Fin) a) ((inv Fin) b)"
  using inf_less_eq apply blast
  apply simp
  by (metis fin_inj infI inv_f_f less2nat)

lemma [nitpick_simp]: "less (a :: lnat) b = (a \<noteq> b \<and> less_eq a b)"
  using nless_le by blast


lemma [nitpick_unfold]: "(0::lnat) = Fin 0"
and [nitpick_unfold]: "(\<bottom>::lnat) = Fin 0"
  apply (simp add: Fin_02bot)
  using Fin_02bot by fastforce

end
