theory def_Bob_LLR_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__Send | state__Block

datatype State = StateConstr Substate           "nat"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getC :: "State \<Rightarrow> nat" where
"getC (StateConstr _ var_c) = var_c"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
