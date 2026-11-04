theory Datatypes
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *) CtrlEnum
    (* Hwl  *)

begin


default_sort type



datatype Packet = PacketConstr              "nat"

instance Packet::countable
by(countable_datatype)

fun Packet_get_size :: "Packet => nat" where
"Packet_get_size (PacketConstr size_pattern) = size_pattern"



datatype msgType = TCtrlEnumEVENT |TPacketEVENT | TNone

datatype channel = CH string timeType msgType

datatype msg =
  CtrlEnumEVENTConstr "CtrlEnum" |
  PacketEVENTConstr "Packet"

instance msg :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> msg set" where
"cMsgt TCtrlEnumEVENT = range CtrlEnumEVENTConstr" |
"cMsgt TPacketEVENT = range PacketEVENTConstr" |
"cMsgt TNone = {}"

lemma [simp]:
  assumes "cMsgt x = cMsgt y"
    shows "x = y"
  apply(insert assms)
  by(cases x; cases y; simp; blast+)

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH _ _ mt) = cMsgt mt"

lemma CtrlEnumEVENTConstr_inj[simp]: "inj CtrlEnumEVENTConstr"
  by (simp add: inj_def)

lemma CtrlEnumEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn CtrlEnumEVENTConstr)"
  by (simp add: tsyn.inj_map)

lemma PacketEVENTConstr_inj[simp]: "inj PacketEVENTConstr"
  by (simp add: inj_def)

lemma PacketEVENTConstr_tsyn_inj[simp]: "inj (map_tsyn PacketEVENTConstr)"
  by (simp add: tsyn.inj_map)

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
