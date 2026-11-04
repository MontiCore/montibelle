theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Hwl  *)

begin


default_sort type



datatype msgType = TboolSYNC | TNone

datatype channel = CH string timeType msgType

datatype msg =
  boolSYNCConstr "bool"

instance msg :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> msg set" where
"cMsgt TboolSYNC = range boolSYNCConstr" |
"cMsgt TNone = {}"

lemma [simp]:
  assumes "cMsgt x = cMsgt y"
    shows "x = y"
  apply(insert assms)
  by(cases x; cases y; simp; blast+)

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH _ _ mt) = cMsgt mt"

lemma boolSYNCConstr_inj[simp]: "inj boolSYNCConstr"
  by (simp add: inj_def)

lemma boolSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn boolSYNCConstr)"
  by (simp add: tsyn.inj_map)

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
