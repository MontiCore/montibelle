theory Datatypes
  imports inc.Prelude inc.TSynDatatype inc.EventDatatype
          

begin

default_sort type

fun tail :: "'a::type list => 'a list" where
"tail (x # xs) = xs" |
"tail [] = []"

fun head :: "'a::type list => 'a" where
"head (x # xs) = x" |
"head [] = undefined"



datatype msgType = TboolEVENT | TNone

datatype channel = CH string timeType msgType

datatype M_pure =
  boolEVENTConstr "bool"

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

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  (* using cMsg.simps cMsgt.simps by blast *)
  sorry


end
