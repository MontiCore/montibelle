theory Datatypes
  imports inc.Prelude inc.TSynDatatype inc.EventDatatype
          

begin


default_sort type

datatype StatusEnum = EInhibited | EWaiting | EListening | EConfirmed
instance StatusEnum::countable
  by(countable_datatype)
datatype CtrlEnum = Confirmation
instance CtrlEnum::countable
  by(countable_datatype)
datatype Packet = PConstr nat
instance Packet::countable
  by(countable_datatype)
fun size :: "Packet => nat" where
"size (PConstr x) = x"
fun tail :: "'a::type list => 'a list" where
"tail (x # xs) = xs" |
"tail [] = []"
fun head :: "'a::type list => 'a" where
"head (x # xs) = x" |
"head [] = undefined"



datatype msgType = TboolEVENT |TboolSYNC |TnatEVENT |TnatSYNC |TstringEVENT |TstringSYNC | TNone

datatype channel = CH string timeType msgType

datatype M_pure =
  boolEVENTConstr "bool" |
  boolSYNCConstr "bool" |
  natEVENTConstr "nat" |
  natSYNCConstr "nat" |
  stringEVENTConstr "string" |
  stringSYNCConstr "string"

instance M_pure :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> M_pure set" where
"cMsgt TboolEVENT = range boolEVENTConstr" |
"cMsgt TboolSYNC = range boolSYNCConstr" |
"cMsgt TnatEVENT = range natEVENTConstr" |
"cMsgt TnatSYNC = range natSYNCConstr" |
"cMsgt TstringEVENT = range stringEVENTConstr" |
"cMsgt TstringSYNC = range stringSYNCConstr" |
"cMsgt TNone = {}"

lemma [simp]:
  assumes"cMsgt x = cMsgt y"
  shows "x = y"
  (* by (metis assms cMsgt.elims empty_is_image empty_not_UNIV) *)
  sorry

fun cMsg :: "channel \<Rightarrow> M_pure set" where
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
  (* using cMsg.simps cMsgt.simps by blast *)
  sorry


end
