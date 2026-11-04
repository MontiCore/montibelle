theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *) Reject Section
    (* Hwl  *)

begin


default_sort type



datatype Access_Point = Access_PointConstr              "Section"                "bool"                 "bool"

instance Access_Point::countable
by(countable_datatype)

fun Access_Point_get_sect :: "Access_Point => Section" where
"Access_Point_get_sect (Access_PointConstr sect_pattern isOpen_pattern isGreen_pattern) = sect_pattern"

fun Access_Point_get_isOpen :: "Access_Point => bool" where
"Access_Point_get_isOpen (Access_PointConstr sect_pattern isOpen_pattern isGreen_pattern) = isOpen_pattern"

fun Access_Point_get_isGreen :: "Access_Point => bool" where
"Access_Point_get_isGreen (Access_PointConstr sect_pattern isOpen_pattern isGreen_pattern) = isGreen_pattern"

datatype Train = TrainConstr                  "Access_Point"

instance Train::countable
by(countable_datatype)

fun Train_get_position :: "Train => Access_Point" where
"Train_get_position (TrainConstr position_pattern) = position_pattern"

datatype Railway_Network = Railway_NetworkConstr                       "Access_Point list"                "Train list"

instance Railway_Network::countable
by(countable_datatype)

fun Railway_Network_get_access_points :: "Railway_Network => Access_Point list" where
"Railway_Network_get_access_points (Railway_NetworkConstr access_points_pattern trains_pattern) = access_points_pattern"

fun Railway_Network_get_trains :: "Railway_Network => Train list" where
"Railway_Network_get_trains (Railway_NetworkConstr access_points_pattern trains_pattern) = trains_pattern"

datatype SetColor = SetColorConstr                "Access_Point"           "bool"

instance SetColor::countable
by(countable_datatype)

fun SetColor_get_access :: "SetColor => Access_Point" where
"SetColor_get_access (SetColorConstr access_pattern b_pattern) = access_pattern"

fun SetColor_get_b :: "SetColor => bool" where
"SetColor_get_b (SetColorConstr access_pattern b_pattern) = b_pattern"

datatype OpenUp = OpenUpConstr           "Access_Point"           "Access_Point"

instance OpenUp::countable
by(countable_datatype)

fun OpenUp_get_a :: "OpenUp => Access_Point" where
"OpenUp_get_a (OpenUpConstr a_pattern b_pattern) = a_pattern"

fun OpenUp_get_b :: "OpenUp => Access_Point" where
"OpenUp_get_b (OpenUpConstr a_pattern b_pattern) = b_pattern"

datatype Enters = EntersConstr               "Train"                "Access_Point"

instance Enters::countable
by(countable_datatype)

fun Enters_get_train :: "Enters => Train" where
"Enters_get_train (EntersConstr train_pattern access_pattern) = train_pattern"

fun Enters_get_access :: "Enters => Access_Point" where
"Enters_get_access (EntersConstr train_pattern access_pattern) = access_pattern"



datatype msgType = TboolEVENT | TNone

datatype channel = CH string timeType msgType

datatype msg =
  boolEVENTConstr "bool"

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

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
