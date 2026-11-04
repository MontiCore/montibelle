theory UntimedExpressions
imports Main

begin


definition toBool::"bool \<Rightarrow> bool" where
"toBool \<equiv> id"

declare toBool_def[simp]

definition liftedNot::"bool \<Rightarrow> bool" where
"liftedNot \<equiv> Not"

declare liftedNot_def[simp]

definition liftedAnd::"bool \<Rightarrow> bool \<Rightarrow> bool" where
"liftedAnd \<equiv> conj"

declare liftedAnd_def[simp]

definition liftedOr::"bool \<Rightarrow> bool \<Rightarrow> bool" where
"liftedOr \<equiv> disj"

declare liftedOr_def[simp]

definition liftedImplication::"bool \<Rightarrow> bool \<Rightarrow> bool"where
"liftedImplication \<equiv> implies"

declare liftedImplication_def[simp]

definition liftedEq::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
"liftedEq \<equiv> HOL.eq"

declare liftedEq_def[simp]

definition lift:: "'a \<Rightarrow> 'a" where
"lift \<equiv> id"

declare lift_def[simp]

definition unlift:: "'a \<Rightarrow> 'a" where
"unlift \<equiv> id"

declare unlift_def[simp]

definition liftedApplyOne::"('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"liftedApplyOne \<equiv> id"

declare liftedApplyOne_def[simp]

definition liftedApplyTwo::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c" where
"liftedApplyTwo \<equiv> id"

declare liftedApplyTwo_def[simp]




lemma [code_abbrev]: "(\<and>) = liftedAnd"
  by auto

lemma [code_abbrev]: "(\<or>) = liftedOr"
  by auto

lemma [code_abbrev]: "(Not) = liftedNot"
  by auto

lemma [code_abbrev]: "(x) = liftedApplyTwo (x)"
  by auto

lemma [code_abbrev]: "implies = liftedImplication"
  by auto

lemma [code_abbrev]: "m = toBool m"
  by auto

lemma [code_abbrev]: "m = lift m"
  by auto

lemma [code_abbrev]: "m = unlift m"
  by auto






end
