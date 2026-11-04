theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Hwl  *)

begin


default_sort type



datatype AEnum = EnumValue1 | EnumValue2

instance AEnum::countable
apply(intro_classes)
by(countable_datatype)

datatype user_defined_Datatype = user_defined_DatatypeConstr               "int"                "nat"

instance user_defined_Datatype::countable
by(countable_datatype)

fun user_defined_Datatype_get_first :: "user_defined_Datatype => int" where
"user_defined_Datatype_get_first (user_defined_DatatypeConstr first_pattern second_pattern) = first_pattern"

fun user_defined_Datatype_get_second :: "user_defined_Datatype => nat" where
"user_defined_Datatype_get_second (user_defined_DatatypeConstr first_pattern second_pattern) = second_pattern"



datatype msgType = TboolEVENT |TboolSYNC |TnatEVENT |TnatSYNC |TstringEVENT |TstringSYNC | TNone

datatype channel = CH string timeType msgType

datatype msg =
  boolEVENTConstr "bool" |
  boolSYNCConstr "bool" |
  natEVENTConstr "nat" |
  natSYNCConstr "nat" |
  stringEVENTConstr "string" |
  stringSYNCConstr "string"

instance msg :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> msg set" where
"cMsgt TboolEVENT = range boolEVENTConstr" |
"cMsgt TboolSYNC = range boolSYNCConstr" |
"cMsgt TnatEVENT = range natEVENTConstr" |
"cMsgt TnatSYNC = range natSYNCConstr" |
"cMsgt TstringEVENT = range stringEVENTConstr" |
"cMsgt TstringSYNC = range stringSYNCConstr" |
"cMsgt TNone = {}"

lemma [simp]:
  assumes "cMsgt x = cMsgt y"
    shows "x = y"
  apply(insert assms)
  by(cases x; cases y; simp; blast+)

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH _ _ mt) = cMsgt mt"

lemma boolEVENTConstr_inj[simp]: "inj boolEVENTConstr"
  by (simp add: inj_def)

lemma boolEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn boolEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma boolSYNCConstr_inj[simp]: "inj boolSYNCConstr"
  by (simp add: inj_def)

lemma boolSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn boolSYNCConstr)"
  by (simp add: tsyn.inj_map)

lemma natEVENTConstr_inj[simp]: "inj natEVENTConstr"
  by (simp add: inj_def)

lemma natEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn natEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma natSYNCConstr_inj[simp]: "inj natSYNCConstr"
  by (simp add: inj_def)

lemma natSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn natSYNCConstr)"
  by (simp add: tsyn.inj_map)

lemma stringEVENTConstr_inj[simp]: "inj stringEVENTConstr"
  by (simp add: inj_def)

lemma stringEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn stringEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma stringSYNCConstr_inj[simp]: "inj stringSYNCConstr"
  by (simp add: inj_def)

lemma stringSYNCConstr_tsyn_inj[simp]: "inj (map_tsyn stringSYNCConstr)"
  by (simp add: tsyn.inj_map)

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
