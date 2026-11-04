theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *) calc_Decrypt calc_Encrypt
    (* Hwl  *)

begin


default_sort type



datatype msgType = TboolSYNC |TnattimesboolSYNC |TstringSYNC |TstringtimesboolSYNC | TNone

datatype channel = CH string timeType msgType

datatype msg =
  boolSYNCConstr "bool" |
  nattimesboolSYNCConstr "(nat\<times>bool)" |
  stringSYNCConstr "string" |
  stringtimesboolSYNCConstr "(string\<times>bool)"

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
"cMsgt TnattimesboolSYNC = range nattimesboolSYNCConstr" |
"cMsgt TstringSYNC = range stringSYNCConstr" |
"cMsgt TstringtimesboolSYNC = range stringtimesboolSYNCConstr" |
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

lemma nattimesboolSYNCConstr_inj[simp]: "inj nattimesboolSYNCConstr"
  by (simp add: inj_def)

lemma nattimesboolSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn nattimesboolSYNCConstr)"
  by (simp add: tsyn.inj_map)

lemma stringSYNCConstr_inj[simp]: "inj stringSYNCConstr"
  by (simp add: inj_def)

lemma stringSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn stringSYNCConstr)"
  by (simp add: tsyn.inj_map)

lemma stringtimesboolSYNCConstr_inj[simp]: "inj stringtimesboolSYNCConstr"
  by (simp add: inj_def)

lemma stringtimesboolSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn stringtimesboolSYNCConstr)"
  by (simp add: tsyn.inj_map)

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
