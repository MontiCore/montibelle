theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Hwl  *)

begin


default_sort type



datatype Data_Bool_Tuple = Data_Bool_TupleConstr             "nat"             "bool"

instance Data_Bool_Tuple::countable
by(countable_datatype)

fun Data_Bool_Tuple_get_fst :: "Data_Bool_Tuple => nat" where
"Data_Bool_Tuple_get_fst (Data_Bool_TupleConstr fst_pattern snd_pattern) = fst_pattern"

fun Data_Bool_Tuple_get_snd :: "Data_Bool_Tuple => bool" where
"Data_Bool_Tuple_get_snd (Data_Bool_TupleConstr fst_pattern snd_pattern) = snd_pattern"

fun Data_Bool_Tuple2tuple :: "Data_Bool_Tuple \<Rightarrow> (nat \<times> bool)" where
  "Data_Bool_Tuple2tuple (Data_Bool_TupleConstr d b) = (d, b)"

lemma Data_Bool_Tuple2tuple_inj[simp]: "inj Data_Bool_Tuple2tuple"
  apply(auto simp add: inj_def)
  by(case_tac x, case_tac y, auto)


datatype msgType = TDataBoolTupleEVENT |TboolEVENT |TnatEVENT | TNone

datatype channel = CH string timeType msgType

datatype msg =
  DataBoolTupleEVENTConstr "Data_Bool_Tuple" |
  boolEVENTConstr "bool" |
  natEVENTConstr "nat"

instance msg :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> msg set" where
"cMsgt TDataBoolTupleEVENT = range DataBoolTupleEVENTConstr" |
"cMsgt TboolEVENT = range boolEVENTConstr" |
"cMsgt TnatEVENT = range natEVENTConstr" |
"cMsgt TNone = {}"

lemma [simp]:
  assumes "cMsgt x = cMsgt y"
    shows "x = y"
  apply(insert assms)
  by(cases x; cases y; simp; blast+)

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH _ _ mt) = cMsgt mt"

lemma DataBoolTupleEVENTConstr_inj[simp]: "inj DataBoolTupleEVENTConstr"
  by (simp add: inj_def)

lemma DataBoolTupleEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn DataBoolTupleEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma boolEVENTConstr_inj[simp]: "inj boolEVENTConstr"
  by (simp add: inj_def)

lemma boolEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn boolEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma natEVENTConstr_inj[simp]: "inj natEVENTConstr"
  by (simp add: inj_def)

lemma natEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn natEVENTConstr)"
  by (simp add: tsyn.inj_map)

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
