theory StreamLtl

imports StreamCodegen
begin

declare nat_all_enum [simp del]








datatype 'a ltl  = 
FalseLtl ("false\<^sub>l") |
ExPropLtl "'a \<Rightarrow> bool" ("exprop\<^sub>l") |
AllPropLtl "'a \<Rightarrow> bool" ("allprop\<^sub>l") |
NotLtl "'a ltl" ("not\<^sub>l" 85)|
OrLtl "'a ltl" "'a ltl" (infixl "or\<^sub>l"  80) |
NextLtl "'a ltl" ("X\<^sub>l" 87) |
UntilLtl "'a ltl" "'a ltl" (infixl "U\<^sub>l" 83)



primrec ltl_semantics::"'a stream \<Rightarrow> 'a ltl \<Rightarrow> bool" where
false_def: "ltl_semantics s FalseLtl = False" |
exprop_def: "ltl_semantics s (ExPropLtl P) = ((\<not> s=\<epsilon>) \<and> (P (shd s)))" |
allprop_def: "ltl_semantics s (AllPropLtl P) = ((s=\<epsilon>) \<or> (P (shd s)))" |
not_def: "ltl_semantics s (NotLtl \<Phi>) = (\<not> (ltl_semantics s \<Phi>))" |
or_def: "ltl_semantics s (OrLtl \<Phi> \<Psi>) = ((ltl_semantics s \<Phi>) \<or> (ltl_semantics s \<Psi>))" |
next_def: "ltl_semantics s (NextLtl \<Phi>) = (ltl_semantics (sdrop 1\<cdot>s) \<Phi>)" |
until_def: "ltl_semantics s (UntilLtl \<Phi> \<Psi>) 
               = (\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Psi>)
                   \<and> (\<forall>j . j < i \<longrightarrow> (ltl_semantics (sdrop j\<cdot>s) \<Phi>))))"

definition TrueLtl::"'a ltl"  ("true\<^sub>l")                      
  where "TrueLtl = (NotLtl FalseLtl)"
definition AndLtl:: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl"  (infixl "and\<^sub>l"  80)   
  where "AndLtl \<Phi> \<Psi> = (NotLtl (OrLtl (NotLtl \<Phi>) (NotLtl \<Psi>)))"
definition ImpliesLtl:: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" (infixr "imp\<^sub>l"  78)
  where "ImpliesLtl \<Phi> \<Psi> = (OrLtl (NotLtl \<Phi>) \<Psi>)"
definition EqualityLtl:: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" (infix "eq\<^sub>l"  78)
  where "EqualityLtl \<Phi> \<Psi> = (OrLtl (AndLtl \<Phi> \<Psi>) (AndLtl (NotLtl \<Phi>) (NotLtl \<Psi>)))"

definition ReleaseLtl:: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" (infixr "R\<^sub>l" 83)
  where "ReleaseLtl \<Phi> \<Psi> = (NotLtl (UntilLtl (NotLtl \<Phi>) (NotLtl \<Psi>)))"
definition FinallyLtl:: "'a ltl \<Rightarrow> 'a ltl" ("F\<^sub>l" 86)
  where "FinallyLtl \<Psi> = (UntilLtl TrueLtl \<Psi>)"
definition GloballyLtl:: "'a ltl \<Rightarrow> 'a ltl" ("G\<^sub>l" 86)
  where "GloballyLtl \<Psi> = (ReleaseLtl FalseLtl \<Psi>)"
definition WeakUntilLtl:: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" (infixl "W\<^sub>l" 83)
  where "WeakUntilLtl \<Phi> \<Psi> = (ReleaseLtl \<Psi> (OrLtl \<Phi> \<Psi>))"

abbreviation HasNextLtl :: "'a ltl \<Rightarrow> 'a ltl" 
  where "HasNextLtl \<Phi> \<equiv> ImpliesLtl (NextLtl (ExPropLtl (\<lambda>x. True))) \<Phi>"

abbreviation PropLtl :: "('a \<Rightarrow> bool) \<Rightarrow> 'a ltl" 
  where "PropLtl P \<equiv> ExPropLtl P"

theorem FinallyLtl_def2: "ltl_semantics s (FinallyLtl \<Phi>) = (\<exists>i :: nat.(((Fin i) < #s)) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Phi>))"
  by (simp add: FinallyLtl_def, simp add: TrueLtl_def)
theorem GloballyLtl_def2: "ltl_semantics s (GloballyLtl \<Phi>) = (\<forall>i :: nat.(((Fin i) < #s)) \<longrightarrow> (ltl_semantics (sdrop i\<cdot>s) \<Phi>))"
  by (simp add: GloballyLtl_def, simp add: ReleaseLtl_def)

lemma minArg:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<exists>xs. P xs"
  shows   "\<exists>xs. is_arg_min (\<lambda>x. x) P xs"
  using assms is_arg_min_arg_min_nat by metis  

lemma RD2H1: "\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<or> (\<exists>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>) \<Longrightarrow>
         \<forall>i. ltl_semantics (sdrop i\<cdot>s) \<Phi> \<longrightarrow> Fin i < #s \<longrightarrow> (\<exists>j\<le>i. \<not> ltl_semantics (sdrop j\<cdot>s) \<Psi>) \<Longrightarrow>
        (Fin w < #s \<and> (\<not> ltl_semantics (sdrop w\<cdot>s) \<Psi>) \<and> (\<forall>u. ltl_semantics (sdrop u\<cdot>s) \<Psi> \<or> u \<ge> w)) \<Longrightarrow>
        (\<exists>v<w. (\<not> ltl_semantics (sdrop v\<cdot>s) \<Psi>))"
  by (metis dual_order.strict_trans1 less2nat less_le_not_le)

lemma RD2H2: "\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<or> (\<exists>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>) \<Longrightarrow>
         \<forall>i. ltl_semantics (sdrop i\<cdot>s) \<Phi> \<longrightarrow> Fin i < #s \<longrightarrow> (\<exists>j\<le>i. \<not> ltl_semantics (sdrop j\<cdot>s) \<Psi>) \<Longrightarrow>
         \<exists>k. Fin k < #s \<and> (\<not> ltl_semantics (sdrop k\<cdot>s) \<Psi>) 
    \<Longrightarrow> (\<exists>w. Fin w < #s \<and> (\<not> ltl_semantics (sdrop w\<cdot>s) \<Psi>) \<and> (\<forall>u. ltl_semantics (sdrop u\<cdot>s) \<Psi> \<or> u \<ge> w))"
      using minArg [of "(\<lambda>k. Fin k < #s \<and> (\<not> ltl_semantics (sdrop k\<cdot>s) \<Psi>))"]
      apply auto[1]
      apply (simp add: is_arg_min_def)
      apply (rule_tac x="x" in exI)
      by (meson dual_order.strict_trans less2nat not_le_imp_less)

lemma RD2H3: "\<not> ltl_semantics s (UntilLtl (NotLtl \<Phi>) (NotLtl \<Psi>)) 
             \<Longrightarrow> ((\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Phi>)
                   \<and> (\<forall>j . j \<le> i \<longrightarrow> (ltl_semantics (sdrop j\<cdot>s) \<Psi>))))
                 \<or> (\<forall>k :: nat.(((Fin k) < #s)) \<longrightarrow> (ltl_semantics (sdrop k\<cdot>s) \<Psi>)))"
    apply auto[1]
    apply (rule ccontr)
  using RD2H1 [of s \<Psi> \<Phi>]
  using RD2H2 [of s \<Psi> \<Phi>]
  apply auto[1]
  using leD by blast


theorem ReleaseLtl_def2:
"ltl_semantics s (ReleaseLtl \<Phi> \<Psi>) 
               = ((\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Phi>)
                   \<and> (\<forall>j . j \<le> i \<longrightarrow> (ltl_semantics (sdrop j\<cdot>s) \<Psi>))))
                 \<or> (\<forall>k :: nat.(((Fin k) < #s)) \<longrightarrow> (ltl_semantics (sdrop k\<cdot>s) \<Psi>)))"
  apply (simp add: ReleaseLtl_def)
proof -
  have a: "ltl_semantics s (UntilLtl (NotLtl \<Phi>) (NotLtl \<Psi>)) 
             \<Longrightarrow> (\<not> ((\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Phi>)
                   \<and> (\<forall>j . j \<le> i \<longrightarrow> (ltl_semantics (sdrop j\<cdot>s) \<Psi>))))
                 \<or> (\<forall>k :: nat.(((Fin k) < #s)) \<longrightarrow> (ltl_semantics (sdrop k\<cdot>s) \<Psi>))))"
    apply auto[1]
    apply (subgoal_tac "ia \<ge> i")
      apply auto[1]
    using leI by auto[1]
  from a
  show "(\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<or> (\<exists>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>)) =
    ((\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Phi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Psi>)) \<or>
     (\<forall>k. Fin k < #s \<longrightarrow> ltl_semantics (sdrop k\<cdot>s) \<Psi>))"
    using RD2H3 [of s \<Phi> \<Psi>]
    by auto
qed

lemma WD2H1: "(\<exists>k. Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi>)
\<Longrightarrow> (\<exists>w. Fin w < #s \<and> ltl_semantics (sdrop w\<cdot>s) \<Psi> \<and> (\<forall>k. (Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi>) \<longrightarrow> (k \<ge> w)))"
  using minArg [of "(\<lambda>k. Fin k < #s \<and> (ltl_semantics (sdrop k\<cdot>s) \<Psi>))"]
  by (simp add: is_arg_min_linorder)

lemma WD2H2: "(Fin w < #s \<and> ltl_semantics (sdrop w\<cdot>s) \<Psi> \<and> (\<forall>k. (Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi>) \<longrightarrow> (k \<ge> w)))
\<Longrightarrow> (\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop j\<cdot>s) \<Psi>)) =
    (\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>))"
  apply auto[1]
   apply (rule exI [where x=w])
   apply (meson dual_order.strict_trans leD less2nat_lemma linorder_le_less_linear)
  apply (rule exI [where x=w])
  by (metis le_eq_less_or_eq order_less_trans)

lemma WD2H3: "(\<exists>k. Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi> \<Longrightarrow>
     (\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop j\<cdot>s) \<Psi>)) =
     (\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>)))"
  using WD2H1[of s \<Psi>] WD2H2[of _ s \<Psi> \<Phi>] by auto

lemma WD2H4: "(\<nexists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop j\<cdot>s) \<Psi>) \<Longrightarrow>
     (\<forall>k. Fin k < #s \<longrightarrow> ltl_semantics (sdrop k\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop k\<cdot>s) \<Psi>) = (\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Phi>))"
  by (metis less2nat order_le_less_subst2)

lemma WD2H5: "(\<nexists>k. Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi> \<Longrightarrow>
     ((\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop j\<cdot>s) \<Psi>)) \<or>
      (\<forall>k. Fin k < #s \<longrightarrow> ltl_semantics (sdrop k\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop k\<cdot>s) \<Psi>)) =
     ((\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>)) \<or>
      (\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Phi>)))"
  by auto

lemma WD2H6:"((\<not> A \<Longrightarrow> B = D)) \<Longrightarrow> (E \<Longrightarrow> A=C) \<Longrightarrow> (\<not>E \<Longrightarrow> ((A \<or> B) = (C \<or> D))) \<Longrightarrow> ((A \<or> B) = (C \<or> D))"
  by auto


theorem WeakUntilLtl_def2: "ltl_semantics s (WeakUntilLtl \<Phi> \<Psi>) 
               = ((\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_semantics (sdrop i\<cdot>s) \<Psi>)
                   \<and> (\<forall>j . j < i \<longrightarrow> (ltl_semantics (sdrop j\<cdot>s) \<Phi>))))
                 \<or> (\<forall>i :: nat.(((Fin i) < #s)) \<longrightarrow> (ltl_semantics (sdrop i\<cdot>s) \<Phi>)))"
  apply(simp add: WeakUntilLtl_def)
  apply (simp add: ReleaseLtl_def2)
  using WD2H3[of s \<Psi> \<Phi>] WD2H4[of s \<Psi> \<Phi>] WD2H5[of s \<Psi> \<Phi>] apply auto[1]
  using WD2H6[of "(\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j\<le>i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop j\<cdot>s) \<Psi>))"
    "(\<forall>k. Fin k < #s \<longrightarrow> ltl_semantics (sdrop k\<cdot>s) \<Phi> \<or> ltl_semantics (sdrop k\<cdot>s) \<Psi>)"
    "(\<forall>i. Fin i < #s \<longrightarrow> ltl_semantics (sdrop i\<cdot>s) \<Phi>)"
    "(\<exists>k. Fin k < #s \<and> ltl_semantics (sdrop k\<cdot>s) \<Psi>)"
    "(\<exists>i. Fin i < #s \<and> ltl_semantics (sdrop i\<cdot>s) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi>))"]
  by auto



lemma next_empty [simp]: "ltl_semantics \<epsilon> (NextLtl \<Phi>) = ltl_semantics \<epsilon> \<Phi>"
  by auto

lemma until_empty [simp]: "ltl_semantics \<epsilon> (UntilLtl \<Phi> \<Psi>) = False"
  apply auto[1]
  by (metis Fin_0 lnat_well_h1 not_less_zero)+

lemma finally_empty [simp]: "ltl_semantics \<epsilon> (FinallyLtl \<Phi>) = False"
  by (metis FinallyLtl_def until_empty)

lemma globally_empty [simp]: "ltl_semantics \<epsilon> (GloballyLtl \<Phi>) = True"
by (metis GloballyLtl_def ReleaseLtl_def ltl_semantics.not_def until_empty)

lemma release_empty [simp]: "ltl_semantics \<epsilon> (ReleaseLtl \<Phi> \<Psi>) = True"
  by (metis ReleaseLtl_def ltl_semantics.not_def until_empty)

lemma weakuntil_empty [simp]: "ltl_semantics \<epsilon> (WeakUntilLtl \<Phi> \<Psi>) = True"
  by (simp add: WeakUntilLtl_def)


lemma and_dual_or [simp]:
  "ltl_semantics s (NotLtl (AndLtl (NotLtl \<Phi>) (NotLtl \<Psi>))) = ltl_semantics s (OrLtl \<Phi> \<Psi>)"
  by (simp add: AndLtl_def)

lemma finally_dual_globally [simp]: 
  "ltl_semantics s (NotLtl (FinallyLtl (NotLtl \<Phi>))) = ltl_semantics s (GloballyLtl \<Phi>)"
  by (simp add: GloballyLtl_def, simp add: FinallyLtl_def, simp add: ReleaseLtl_def, simp add: TrueLtl_def)

lemma globally_dual_finally [simp]: 
  "ltl_semantics s (NotLtl (GloballyLtl (NotLtl \<Phi>))) = ltl_semantics s (FinallyLtl \<Phi>)"
  by (simp add: FinallyLtl_def, simp add: GloballyLtl_def, simp add: ReleaseLtl_def, simp add: TrueLtl_def)

lemma next_dual_next: 
  assumes "#s \<ge> Fin (Suc (Suc 0))"
  shows
  "ltl_semantics s (NotLtl (NextLtl \<Phi>)) = ltl_semantics s (NextLtl (NotLtl \<Phi>))"
  using assms
  by auto

lemma release_dual_until [simp]:
  "ltl_semantics s (NotLtl (ReleaseLtl (NotLtl \<Phi>) (NotLtl \<Psi>))) = ltl_semantics s (UntilLtl \<Phi> \<Psi>)"
  by (simp add: ReleaseLtl_def, auto)

lemma ltlsemantics_and[simp]:
  "ltl_semantics s (ReleaseLtl (AndLtl \<Phi> \<Psi>) (\<Psi> or\<^sub>l AndLtl \<Phi> \<Psi>)) = ltl_semantics s (ReleaseLtl \<Phi> \<Psi>)"
  apply (simp add: ReleaseLtl_def2, simp add: AndLtl_def)
  by auto

lemma ltlsemantics_weakand[simp]:  
  "ltl_semantics s (WeakUntilLtl \<Psi> (AndLtl \<Phi> \<Psi>)) = ltl_semantics s (ReleaseLtl \<Phi> \<Psi>)"
  by (simp add: WeakUntilLtl_def)

lemma ltlsemantics_andimplies[simp]:
  "ltl_semantics s (AndLtl (ImpliesLtl \<Phi> \<Psi>) (ImpliesLtl \<Psi> \<Phi>)) = ltl_semantics s (EqualityLtl \<Phi> \<Psi>)"
  by (simp add: ImpliesLtl_def, simp add: EqualityLtl_def, simp add: AndLtl_def, auto)


lemma and_dist:
  "ltl_semantics s (AndLtl \<Phi> (OrLtl \<Psi> X)) = ltl_semantics s (OrLtl (AndLtl \<Phi> \<Psi>) (AndLtl \<Phi> X))"
  by (simp add: AndLtl_def, auto)

lemma or_dist:
  "ltl_semantics s (OrLtl \<Phi> (AndLtl \<Psi> X)) = ltl_semantics s (AndLtl (OrLtl \<Phi> \<Psi>) (OrLtl \<Phi> X))"
  by (simp add: AndLtl_def, auto)

lemma finally_dist:
  "ltl_semantics s (FinallyLtl (OrLtl \<Phi> \<Psi>)) = ltl_semantics s (OrLtl (FinallyLtl \<Phi>) (FinallyLtl \<Psi>))"
  by (simp add: FinallyLtl_def, auto)

lemma globally_dist:
  "ltl_semantics s (GloballyLtl (AndLtl \<Phi> \<Psi>)) = ltl_semantics s (AndLtl (GloballyLtl \<Phi>) (GloballyLtl \<Psi>))"
  by (metis AndLtl_def finally_dist finally_dual_globally globally_dual_finally ltl_semantics.not_def ltl_semantics.or_def)

lemma allprop_setup: "\<forall>s k. Fin k < #s \<longrightarrow> sdrop k\<cdot>s \<noteq> \<epsilon>"
    by (simp add: drop_not_all)
  
lemma beweisIdee: "Fin (Suc k) < #(updis a && as) \<Longrightarrow>
         ltl_semantics (sdrop (Suc k)\<cdot>(updis a && as)) \<Psi> \<Longrightarrow>
         \<forall>j<(Suc k). ltl_semantics (sdrop j\<cdot>(updis a && as)) \<Phi> \<Longrightarrow>
         \<exists>i. Fin i < #as \<and> ltl_semantics (sdrop i\<cdot>as) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>as) \<Phi>)"
  apply (rule exI [where x="k"])
  apply auto[1]
    apply (simp_all add: lscons_conv)
  apply (erule_tac x="Suc j" in allE)
  by (simp add: lscons_conv)

lemma testCU3: "Fin i < #s \<Longrightarrow>
         ltl_semantics (sdrop i\<cdot>s) \<Psi> \<Longrightarrow>
         \<not> ltl_semantics s \<Psi> \<Longrightarrow> i = Suc (i - 1)"
 by (metis Suc_diff_1 not_gr_zero sdrop_0)

lemma testCU4: "Fin i < #s \<Longrightarrow>
         ltl_semantics (sdrop i\<cdot>s) \<Psi> \<Longrightarrow>
         \<forall>j<i. ltl_semantics (sdrop j\<cdot>s) \<Phi> \<Longrightarrow>
         \<not> ltl_semantics s \<Psi> \<Longrightarrow>
       \<exists>k. (Fin (Suc k) < #s \<and>
         ltl_semantics (sdrop (Suc k)\<cdot>s) \<Psi> \<and>
         (\<forall>j<(Suc k). ltl_semantics (sdrop j\<cdot>s) \<Phi>))"
  apply (rule exI [where x="i-1"])
  using testCU3 [of "i" "s" "\<Psi>"]
  by auto

lemma testCU5: "Fin i < #(updis a && as) \<Longrightarrow>
         ltl_semantics (sdrop i\<cdot>(updis a && as)) \<Psi> \<Longrightarrow>
         \<forall>j<i. ltl_semantics (sdrop j\<cdot>(updis a && as)) \<Phi> \<Longrightarrow>
         \<not> ltl_semantics (updis a && as) \<Psi> \<Longrightarrow>
       \<exists>i. Fin i < #as \<and> ltl_semantics (sdrop i\<cdot>as) \<Psi> \<and> (\<forall>j<i. ltl_semantics (sdrop j\<cdot>as) \<Phi>)"
  using testCU4 [of "i" "(updis a && as)" "\<Psi>" "\<Phi>"]
  using beweisIdee [of _ "a" "as" "\<Psi>" "\<Phi>"]
  by auto



lemma [code]: "ltl_semantics s (FalseLtl) = False"
  by auto

lemma [code]: "ltl_semantics \<epsilon> (ExPropLtl P) = False"
   and [code]: "ltl_semantics (updis a && as) (ExPropLtl P) = (P a)"
  by (simp, simp add: shd_def)

lemma [code]: "ltl_semantics \<epsilon> (AllPropLtl P) = True"
   and [code]: "ltl_semantics (updis a && as) (AllPropLtl P) = (P a)"
  by (simp, simp add: shd_def)

lemma [code]: "ltl_semantics s (NotLtl \<Phi>) = (\<not> (ltl_semantics s \<Phi>))"
  by auto

lemma [code]: "ltl_semantics s (OrLtl \<Phi> \<Psi> ) = ((ltl_semantics s \<Phi>) \<or> (ltl_semantics s \<Psi>))"
  by (simp_all)

lemma [code]: "ltl_semantics \<epsilon> (NextLtl \<Phi>) = ltl_semantics \<epsilon> \<Phi>"
   and [code]: "ltl_semantics (updis a && \<epsilon>) (NextLtl \<Phi>) = ltl_semantics \<epsilon> \<Phi>"
   and [code]: "ltl_semantics (updis a && (updis b && bs)) (NextLtl \<Phi>) = (ltl_semantics (updis b && bs) \<Phi>)"
    apply (simp_all)
   apply (metis lscons_conv sdrop_0 sdrop_scons)+
  done

lemma [code]: "ltl_semantics \<epsilon> (UntilLtl \<Phi> \<Psi>) = False"
   and [code]: "ltl_semantics (updis a && as) (UntilLtl \<Phi> \<Psi>) 
                  =  ((ltl_semantics (updis a && as) \<Psi>) 
                     \<or>
                     ((ltl_semantics (updis a && as) \<Phi>) \<and> (ltl_semantics as (UntilLtl \<Phi> \<Psi>))))"
  using until_empty
  apply auto[2]
     apply (metis less_nat_zero_code linorder_neqE_nat sdrop_0)
  using testCU5 [of _ a as \<Psi> \<Phi>]
    apply auto[1]
   apply (rule exI [where x="0"])
   apply (metis Fin_02bot gr_0 less_nat_zero_code lnzero_def sdrop_0 slen_scons upstream_abbrev)
  apply (rule_tac x="Suc i" in exI)
  apply (simp add: lscons_conv)
  using less_Suc_eq_0_disj by auto[1]


primrec alternating :: "bool \<Rightarrow> nat \<Rightarrow> bool stream" 
  where "alternating b 0 = \<epsilon>" | "alternating b (Suc n) = (updis b && (alternating (\<not> b) n))"

definition checkAlternating :: "bool ltl" where
  "checkAlternating = GloballyLtl (EqualityLtl (AllPropLtl (\<lambda>x. x)) (NextLtl (AllPropLtl (\<lambda>x. \<not> x))))"

value "ltl_semantics ((updis True && (updis True && \<epsilon>))) (checkAlternating)"

value "ltl_semantics (alternating False 0) (checkAlternating)"
value "ltl_semantics (alternating False 2) (checkAlternating)"
value "ltl_semantics (alternating False 126) (checkAlternating)"
value "ltl_semantics (alternating True 1) (checkAlternating)"
value "ltl_semantics (alternating True 21) (checkAlternating)"
value "ltl_semantics (alternating False 3) (checkAlternating)"
value "ltl_semantics (alternating True 4) (checkAlternating)"
definition checkAlternatingExProp :: "bool ltl" where
  "checkAlternatingExProp = GloballyLtl (EqualityLtl (ExPropLtl (\<lambda>x. x)) (NextLtl (ExPropLtl (\<lambda>x. \<not> x))))"
value "ltl_semantics (alternating False 3) (checkAlternatingExProp)"
value "ltl_semantics (alternating False 4) (checkAlternatingExProp)"
value "ltl_semantics (alternating True 3) (checkAlternatingExProp)"
value "ltl_semantics (alternating True 4) (checkAlternatingExProp)"
text\<open>We can specify the property of an alternating sequence in a different way using LTL while
     also handling finite streams by using the wrapper @{term HasNextLtl}. Thereby, we only check
     whether the current stream element is True iff the next stream element is False if a successor
     of this stream element exists.\<close>
definition checkAlternating2 :: "bool ltl" where
  "checkAlternating2 = GloballyLtl (HasNextLtl (EqualityLtl (PropLtl (\<lambda>x. x)) (NextLtl (PropLtl (\<lambda>x. \<not> x)))))"

value "ltl_semantics (alternating True 5) (checkAlternating2)"
value "ltl_semantics (alternating True 4) (checkAlternating2)"
value "ltl_semantics (alternating False 5) (checkAlternating2)"
value "ltl_semantics (alternating False 4) (checkAlternating2)"





text\<open>In the following we inspect in which ways ltl_semantics behaves admissibly. This means we check
     for which formulas the following property holds: If the formula holds for all streams in a
     chain of streams, it also holds for the least upper bound of this chain w.r.t. prefix order.
     Admissability of @{term ltl_semantics} is not generally given for every ltl formula.
     Consider the next formula that is true iff the stream is finite.\<close>

definition is_finite :: "nat ltl"
  where "is_finite = FinallyLtl (NotLtl (NextLtl (ExPropLtl (\<lambda>x. True))))"


definition generic_stream_chain :: "nat \<Rightarrow> nat stream"
  where "generic_stream_chain n = sup' 0 \<Zcat> sntimes n (sup' 0)"

lemma gsc1: "\<up>0 \<Zcat> (i\<star>\<up>0) \<sqsubseteq> \<up>0 \<Zcat> \<up>0 \<Zcat> (i\<star>\<up>0)"
  apply (induction i)
  apply auto[1]
  by (simp add: monofun_cfun_arg)

lemma gsc: "chain generic_stream_chain"
  apply (simp add: chain_def generic_stream_chain_def)
  using gsc1 by auto

lemma gsl1: "(\<Squnion>x. \<up>0 \<Zcat> (x\<star>\<up>0)) = \<up>0 \<Zcat> (\<Squnion>x. (x\<star>\<up>0))"
  by (simp add: sntimes_stake contlub_cfun_arg)
  
lemma gslub: "(\<Squnion>x. \<up>0 \<Zcat> (x\<star>\<up>0)) = (sinftimes (sup' 0))"
  by (metis (no_types) gsl1 sinftimes_unfold sntimesLub)

theorem "\<not> (adm (\<lambda>s. ltl_semantics s is_finite))"
  apply (simp add: adm_def is_finite_def FinallyLtl_def2)
  apply (rule exI [where x=generic_stream_chain], auto)
  using gsc apply auto[1]
   apply (rule_tac x="i" in exI, simp_all add: generic_stream_chain_def)
  apply (simp add: sntimes_stake)
  apply (metis sdrop_0 sdrop_back_rt sdropostake stake_Suc)
  (*apply (subgoal_tac "(\<Squnion>x. \<up>0 \<Zcat> (x\<star>\<up>0)) = sup' 0 \<Zcat> ((\<up>0)\<^sup>\<infinity>)")*)
  apply (simp add: sdrop_forw_rt)
  by (simp add: gslub)

text\<open>We can however show some simplifications for admissibility of ltl formulas:
  If a ltl formula \<Phi> is admissible, then wrapping it in @{term NextLtl} keeps this property.\<close>

lemma adm_next:  "adm (\<lambda>s. ltl_semantics s \<Phi>) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s (NextLtl \<Phi>))"
  by (simp add: adm_def cont2contlubE)

theorem com_adm_next: assumes "\<not> (adm (\<lambda>s. ltl_semantics s \<Phi>)) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s (NotLtl \<Phi>))"
  shows "\<not> (adm (\<lambda>s. ltl_semantics s (NextLtl \<Phi>))) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s (NotLtl (NextLtl \<Phi>)))"
  apply (subgoal_tac "\<not> (adm (\<lambda>s. ltl_semantics s \<Phi>))")
  defer
  using adm_next apply auto[1]
  apply (subgoal_tac "adm (\<lambda>s. ltl_semantics s (NotLtl \<Phi>))")
  defer
  using assms apply auto[1]
  apply (subgoal_tac "adm (\<lambda>s. ltl_semantics s (NextLtl (NotLtl \<Phi>)))")
  using adm_next next_dual_next apply force
  using adm_next by blast
  
(*
lemma "adm (\<lambda>s. ltl_semantics s \<phi>) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s \<theta>) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s (ReleaseLtl \<phi> \<theta>))"
  apply (simp add: ReleaseLtl_def2)
  sorry
 *) 

(*
theorem com_adm_ltl: "\<not> (adm (\<lambda>s. ltl_semantics s \<Phi>)) \<Longrightarrow> adm (\<lambda>s. ltl_semantics s (NotLtl \<Phi>))"
  apply (induction \<Phi>)
        apply auto
      apply (simp add: adm_def, metis below_lub below_shd bottomI chain_tord)
     apply (simp add: adm_def, metis below_lub below_shd bottomI chain_tord)
    defer
  using com_adm_next apply auto[1]
  überhaupt wahr?
*) 



primrec ltl_block_semantics :: "'m list stream \<Rightarrow> 'm ltl \<Rightarrow> bool" where
exprop_block_def: "ltl_block_semantics s (ExPropLtl P)  = ((\<not> (s = \<epsilon>)) \<and> (\<exists>m \<in> (set (shd s)). P m))" |
"ltl_block_semantics s (AllPropLtl P) = ((s = \<epsilon>) \<or> (\<forall>m \<in> (set (shd s)). P m))" |
"ltl_block_semantics s FalseLtl       = False" |
"ltl_block_semantics s (NotLtl \<Phi>)     = (\<not> (ltl_block_semantics s \<Phi>))" |
"ltl_block_semantics s (OrLtl \<Phi> \<Psi>)    = ((ltl_block_semantics s \<Phi>) \<or> (ltl_block_semantics s \<Psi>))" |
"ltl_block_semantics s (NextLtl \<Phi>)    = (ltl_block_semantics (sdrop 1\<cdot>s) \<Phi>)" |
"ltl_block_semantics s (UntilLtl \<Phi> \<Psi>) = (\<exists>i :: nat. (((Fin i) < #s) \<and> (ltl_block_semantics (sdrop i\<cdot>s) \<Psi>)
                   \<and> (\<forall>j . j < i \<longrightarrow> (ltl_block_semantics (sdrop j\<cdot>s) \<Phi>))))"


definition ltl_event_block_semantics :: "'m event stream \<Rightarrow> 'm ltl \<Rightarrow> bool" where
"ltl_event_block_semantics s = ltl_block_semantics (sEventToList\<cdot>s)"



definition ltl_event_semantics :: "'m event stream \<Rightarrow> 'm list ltl \<Rightarrow> bool" where
"ltl_event_semantics s \<Phi> = ltl_semantics (sEventToList\<cdot>s) \<Phi>"



primrec block2sequence :: "'m ltl => 'm list ltl" where
"block2sequence (ExPropLtl P) = (ExPropLtl (\<lambda> l. \<exists>m \<in> set(l). P m))" |
"block2sequence (AllPropLtl P) = (AllPropLtl (\<lambda> l. \<forall>m \<in> set(l). P m))" |
"block2sequence FalseLtl = FalseLtl" |
"block2sequence (NotLtl \<Phi>) = (NotLtl (block2sequence \<Phi>))" |
"block2sequence (NextLtl \<Phi>) = (NextLtl (block2sequence \<Phi>))" |
"block2sequence (OrLtl \<Phi> \<Psi>) = (OrLtl (block2sequence \<Phi>) (block2sequence \<Psi>))" |
"block2sequence (UntilLtl \<Phi> \<Psi>) = (UntilLtl (block2sequence \<Phi>) (block2sequence \<Psi>))"


lemma ECUS_h1: "Tick \<in> sValues\<cdot>s \<Longrightarrow> \<exists>\<sigma>. sdrop 1\<cdot>(sEventToList\<cdot>s) = sEventToList\<cdot>\<sigma>"
  by (metis stimedtolist_tsstep [of s] inject_scons split_streaml1 stake2shd2 strict_sdrop)

lemma ECUS_h2: "Tick \<notin> sValues\<cdot>s \<Longrightarrow>sdrop 1\<cdot>(sEventToList\<cdot>s) = (sEventToList\<cdot>s)"
  by simp

lemma e2list_closed_under_sdrop: "\<exists>\<sigma>. sdrop i\<cdot>(sEventToList\<cdot>s) = sEventToList\<cdot>\<sigma>"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  have "\<exists>\<sigma>. sdrop i\<cdot>(sEventToList\<cdot>s) = sEventToList\<cdot>\<sigma> \<Longrightarrow> \<exists>k. sdrop (Suc i)\<cdot>(sEventToList\<cdot>s) = sdrop 1\<cdot>(sEventToList\<cdot>k)"
    by (metis plus_1_eq_Suc sdrop_plus)
  then show ?case 
    using Suc
    by (metis ECUS_h1 ECUS_h2)
  qed



theorem event_block_red_event:
"\<forall>s. ltl_event_block_semantics s \<Phi>  = ltl_event_semantics s (block2sequence \<Phi>)"
  apply (simp add: ltl_event_block_semantics_def, simp add: ltl_event_semantics_def)
  apply (induction \<Phi>, simp_all)
  using e2list_closed_under_sdrop
  by metis+ 

lemma ltl_event_gen_simp: assumes "ltl_semantics (sEventToList\<cdot>s) \<Phi> = ltl_semantics (sEventToList\<cdot>s) \<Psi>"
  shows "ltl_event_semantics s \<Phi> = ltl_event_semantics s \<Psi>"
  using assms
  by (simp add: ltl_event_semantics_def)

lemma "ltl_event_semantics s (NotLtl (ReleaseLtl (NotLtl \<Phi>) (NotLtl \<Psi>))) = ltl_event_semantics s (UntilLtl \<Phi> \<Psi>)"
  using release_dual_until [of "sEventToList\<cdot>s" \<Phi> \<Psi>]
  using ltl_event_gen_simp [of s "(NotLtl (ReleaseLtl (NotLtl \<Phi>) (NotLtl \<Psi>)))" "(UntilLtl \<Phi> \<Psi>)"]
  by auto


fun ltlauttransition::"('a ltl \<times> 'a stream) \<Rightarrow> 'a \<Rightarrow> (('a ltl \<times> 'a stream) \<times> bool)"where
ltlauttransition_def: "ltlauttransition (f,s) a = ((f, s\<Zcat>\<up>a),ltl_semantics (s\<Zcat>\<up>a) f)"

fun ltlconfig::"'a ltl \<Rightarrow> ('a ltl \<times> 'a stream) \<times> bool stream"where
"ltlconfig f = ((f,\<epsilon>), sup' (ltl_semantics \<epsilon> f))"

definition ltlautomaton::"'a ltl \<Rightarrow> (('a ltl \<times> 'a stream),'a,bool stream) dAutomaton"where
"ltlautomaton f = (|dautTransition=(\<lambda>s m. apsnd sup' (ltlauttransition s m))  , 
                    dautInitConfig= ltlconfig f  |)"

definition ltlautomaton_semantics::"'a stream \<Rightarrow> 'a ltl \<Rightarrow> bool stream" where
"ltlautomaton_semantics s f = (daSem stream_step (ltlautomaton f))\<cdot>s"


lemma shdltlaut[simp]: "shd (ltlautomaton_semantics \<epsilon> f) = ltl_semantics \<epsilon> f"
  apply (simp add: ltlautomaton_semantics_def)
  by (simp add: ltlautomaton_def)

lemma AENH1: "daStateSem stream_step (ltlautomaton f) (f,acc)\<cdot>((sup' a) \<Zcat> s) 
= (sup' (ltl_semantics (acc\<Zcat>\<up>a) f))\<Zcat>(daStateSem stream_step (ltlautomaton f) (f,acc\<Zcat>(sup' a))\<cdot>s)"
  using dastatesem_step [of stream_step "(ltlautomaton f)" "(f,acc)"]
  apply simp
  by (simp add: ltlautomaton_def)

lemma AENH2: "daStateSem stream_step (ltlautomaton f) (f,acc)\<cdot>((sup' a) \<Zcat> \<epsilon>) 
= (sup' (ltl_semantics (acc\<Zcat>\<up>a) f))"
  using dastatesem_step [of stream_step "(ltlautomaton f)" "(f,acc)"]
  by (simp add: ltlautomaton_def)

lemma AENH3: "sdrop (Suc n)\<cdot>(ltlautomaton_semantics (\<up>a \<Zcat> sa) f) = sdrop n\<cdot>(daStateSem stream_step (ltlautomaton f) (f,\<epsilon>)\<cdot>(\<up>a \<Zcat> sa))"
  apply (simp add: ltlautomaton_semantics_def)
  by (simp add: daSem_def, simp add: ltlautomaton_def)

lemma AENH4: "\<forall>s acc. #s = Fin n \<longrightarrow> (sdrop n\<cdot>(daStateSem stream_step (ltlautomaton f) (f,acc)\<cdot>(s\<Zcat>(sup' a)))) = sup' (ltl_semantics (acc\<Zcat>s\<Zcat>(sup' a)) f)"
proof (induction n)
  case 0
  then show ?case using AENH2 by auto
next
  case (Suc n)
  then show ?case 
    apply auto[1]
    apply (subgoal_tac "\<exists>b sb. s = (sup' b) \<Zcat> sb")
     apply auto[1]
    using AENH1 [of f] apply auto[1]
    by (metis sconc_fst_empty sdrop_scons sdropl6 streamcases strict_sdrop)
qed

lemma AENH5: "Fin (Suc n) \<le> #s  \<Longrightarrow> \<exists>a. \<exists>sa. ((stake (Suc n)\<cdot>s = sa \<Zcat> (sup' a)))"
  by (metis sfood_id slen_stake)

lemma AENH61: "Fin (Suc n) = #s \<Longrightarrow> stake (Suc n)\<cdot>s = sa \<Zcat> \<up>a \<Longrightarrow> shd (sdrop (Suc n)\<cdot>(ltlautomaton_semantics (sa \<Zcat> \<up>a) f)) = ltl_semantics (sa \<Zcat> \<up>a) f"
  apply (cases sa)
   apply simp_all
  using AENH3 [of n a \<epsilon> f]
   apply simp
   apply (subgoal_tac "n=0")
    apply (metis AENH2 sconc_fst_empty sconc_snd_empty sdrop_0 shd1)
   apply (simp add: fin2stake; fail)
  using AENH3 [of n _ _ f]
  apply simp
  apply (subgoal_tac "#sa = n")
   apply (metis (no_types, lifting) AENH1 AENH2 AENH4 assoc_sconc sconc_fst_empty shd1)
  by (metis Fin_Suc fin2stake inject_lnsuc slen_lnsuc slen_scons)

lemma AENH6: "Fin (Suc n) = #s \<Longrightarrow> snth (Suc n) (ltlautomaton_semantics (stake (Suc n)\<cdot>s) f) = (ltl_semantics (stake (Suc n)\<cdot>s) f)"
  apply (simp add: snth_def)
  using AENH5 [of "n" s]
  apply auto[1]
  by (simp_all add: AENH61)


theorem assumes "#s = Fin n"
  shows "snth n (ltlautomaton_semantics s f) =  ltl_semantics s f"
  apply (cases s)
  using assms
  apply (simp; fail)
proof -
  have b: "s = \<up>a \<Zcat> sa \<Longrightarrow> #s = Fin n \<Longrightarrow> #sa = m\<Longrightarrow> (Fin (Suc m) = #s \<and> m = #sa \<and> (Suc m) = n)
           \<Longrightarrow> snth (Suc m) (ltlautomaton_semantics (\<up>a \<Zcat> sa) f) = ltl_semantics (\<up>a \<Zcat> sa) f"
    by (metis AENH6 fin2stake)   
  show "\<And>a sa. s = \<up>a \<Zcat> sa \<Longrightarrow> snth n (ltlautomaton_semantics s f) = ltl_semantics s f"
    apply (subgoal_tac "\<exists>m. (Fin (Suc m) = #s \<and> m = #sa \<and> (Suc m) = n)")
    using b
     apply (metis AENH6 fin2stake)
    apply (subgoal_tac "\<exists>l. Fin (Suc l) = #s")
    using assms apply force
    by (metis assms not0_implies_Suc sconc_snd_empty sdrop_0 sdropostake sntimes_eps sntimes_len stake_prefix2 strictI)
qed

declare nat_all_enum [simp]

end