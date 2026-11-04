theory Data_inc
  imports
    (* Core *) bundle.SB inc.Classes bundlelocale.SBEGen bundlelocale.SBGen
    (* Hwl  *)

begin


default_sort type



definition minus_lnat:: "lnat \<Rightarrow> lnat \<Rightarrow> lnat" (infixl "-" 65)  where
"minus_lnat ln1 ln2 \<equiv> if (ln1 = \<infinity>)
                      then (\<infinity>)
                      else if ((ln1 > ln2) \<or> (ln1 = ln2))
                           then Fin ((inv Fin) ln1 - (inv Fin) ln2)
                           else undefined"

fun removeAll::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"removeAll xs [] = xs" |
"removeAll xs (y#ys) = removeAll (remove1 y xs) ys"

definition symmetricDifference::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"symmetricDifference a b = (a - b) \<union> (b - a)"



lemma cmsg_empty: "cMsg c = {} \<longleftrightarrow> cType c = TNone"
  by(cases c; case_tac x3;simp)

lemma cempty[simp]: "cEmpty = {c. cType c = TNone}"
  using ctype_empty_iff cEmpty_def cmsg_empty by simp

lemma boolEVENT_ran[simp]: "range (Timed o TLive o (map_event) boolEVENTConstr) = ctype (CH boolEVENT TTLive TboolEVENT)"
  apply(auto simp add: ctype_def)
  by (metis event.simps(8) rangeI)

lemma boolSYNC_ran[simp]: "range (Timed o Tsyn o (map_tsyn) boolSYNCConstr) = ctype (CH boolSYNC TTsyn TboolSYNC)"
  apply(auto simp add: ctype_def)
  by (metis tsyn.simps(8) range_eqI)

lemma natEVENT_ran[simp]: "range (Timed o TLive o (map_event) natEVENTConstr) = ctype (CH natEVENT TTLive TnatEVENT)"
  apply(auto simp add: ctype_def)
  by (metis event.simps(8) rangeI)

lemma natSYNC_ran[simp]: "range (Timed o Tsyn o (map_tsyn) natSYNCConstr) = ctype (CH natSYNC TTsyn TnatSYNC)"
  apply(auto simp add: ctype_def)
  by (metis tsyn.simps(8) range_eqI)

lemma stringEVENT_ran[simp]: "range (Timed o TLive o (map_event) stringEVENTConstr) = ctype (CH stringEVENT TTLive TstringEVENT)"
  apply(auto simp add: ctype_def)
  by (metis event.simps(8) rangeI)

lemma stringSYNC_ran[simp]: "range (Timed o Tsyn o (map_tsyn) stringSYNCConstr) = ctype (CH stringSYNC TTsyn TstringSYNC)"
  apply(auto simp add: ctype_def)
  by (metis tsyn.simps(8) range_eqI)


end
