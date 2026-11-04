theory EventExpressions
  imports inc.EventDatatype

begin


fun toBool::"bool event \<Rightarrow> bool" where
"toBool Tick = False" |
"toBool (EventMsg a) = a"

fun liftedNot::"bool event \<Rightarrow> bool event" where
"liftedNot Tick = EventMsg True" |
"liftedNot (EventMsg a) = EventMsg  (\<not> a)"

fun liftedAnd::"bool event \<Rightarrow> bool event \<Rightarrow> bool event" where
"liftedAnd Tick Tick = EventMsg False" |
"liftedAnd Tick b = EventMsg False" |
"liftedAnd a Tick = EventMsg False" |
"liftedAnd (EventMsg a) (EventMsg b) = EventMsg  (a \<and> b)"

fun liftedOr::"bool event \<Rightarrow> bool event \<Rightarrow> bool event" where
"liftedOr Tick Tick = EventMsg False" |
"liftedOr Tick b = b" |
"liftedOr a Tick = a" |
"liftedOr (EventMsg a) (EventMsg b) = EventMsg (a \<or> b)"

fun liftedImplication::"bool event \<Rightarrow> bool event \<Rightarrow> bool event" where
"liftedImplication Tick Tick = EventMsg True" |
"liftedImplication Tick b = EventMsg True" |
"liftedImplication (EventMsg a) Tick = EventMsg (\<not> a)" |
"liftedImplication (EventMsg a) (EventMsg b) = EventMsg (a \<longrightarrow> b)"

fun liftedEq::"'a event \<Rightarrow> 'a event \<Rightarrow> bool event" where
"liftedEq Tick Tick = EventMsg True" |
"liftedEq a Tick = EventMsg False" |
"liftedEq Tick b = EventMsg False" |
"liftedEq (EventMsg a) (EventMsg b) = EventMsg (a = b)"

definition lift:: "'a \<Rightarrow> 'a event" where
"lift \<equiv> EventMsg"

declare lift_def[simp]

definition unlift:: "'a event \<Rightarrow> 'a" where
"unlift \<equiv> invEventMsg"

declare unlift_def[simp]

fun liftedApplyOne :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event \<Rightarrow> 'b event" where
"liftedApplyOne f (EventMsg m) = EventMsg (f m)" | 
"liftedApplyOne f Tick = Tick"

fun liftedApplyTwo :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a event \<Rightarrow> 'b event \<Rightarrow> 'c event" where
"liftedApplyTwo f (EventMsg a) (EventMsg b) = EventMsg (f a b)" | 
"liftedApplyTwo _ _ _             = Tick"


end