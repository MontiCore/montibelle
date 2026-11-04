theory TSynExpressions
imports inc.TSynDatatype

begin

fun toBool::"bool tsyn \<Rightarrow> bool" where
"toBool Eps = False" |
"toBool (TSynMsg a) = a"

fun liftedNot::"bool tsyn \<Rightarrow> bool tsyn" where
"liftedNot Eps = TSynMsg True" |
"liftedNot (TSynMsg a) = TSynMsg  (\<not> a)"

fun liftedAnd::"bool tsyn \<Rightarrow> bool tsyn \<Rightarrow> bool tsyn" where
"liftedAnd Eps Eps = TSynMsg False" |
"liftedAnd Eps b = TSynMsg False" |
"liftedAnd a Eps = TSynMsg False" |
"liftedAnd (TSynMsg a) (TSynMsg b) = TSynMsg  (a \<and> b)"

fun liftedOr::"bool tsyn \<Rightarrow> bool tsyn \<Rightarrow> bool tsyn" where
"liftedOr Eps Eps = TSynMsg False" |
"liftedOr Eps b = b" |
"liftedOr a Eps = a" |
"liftedOr (TSynMsg a) (TSynMsg b) = TSynMsg (a \<or> b)"

fun liftedImplication::"bool tsyn \<Rightarrow> bool tsyn \<Rightarrow> bool tsyn" where
"liftedImplication Eps Eps = TSynMsg True" |
"liftedImplication Eps b = TSynMsg True" |
"liftedImplication (TSynMsg a) Eps = TSynMsg (\<not> a)" |
"liftedImplication (TSynMsg a) (TSynMsg b) = TSynMsg (a \<longrightarrow> b)"

fun liftedEq::"'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> bool tsyn" where
"liftedEq Eps Eps = TSynMsg True" |
"liftedEq a Eps = TSynMsg False" |
"liftedEq Eps b = TSynMsg False" |
"liftedEq (TSynMsg a) (TSynMsg b) = TSynMsg (a = b)"

definition lift:: "'a \<Rightarrow> 'a tsyn" where
"lift \<equiv> TSynMsg"

declare lift_def[simp]

definition unlift:: "'a tsyn \<Rightarrow> 'a" where
"unlift \<equiv> invMsg"

declare unlift_def[simp]

fun liftedApplyOne :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
"liftedApplyOne f (TSynMsg m) = TSynMsg (f m)" | 
"liftedApplyOne f Eps = Eps"

fun liftedApplyTwo :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn \<Rightarrow> 'c tsyn" where
"liftedApplyTwo f (TSynMsg a) (TSynMsg b) = TSynMsg (f a b)" | 
"liftedApplyTwo _ _ _             = Eps"


end
