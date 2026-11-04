theory def_Bob_LLR_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S

datatype State = StateConstr Substate              "bool"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getCtrl :: "State \<Rightarrow> bool" where
"getCtrl (StateConstr _ var_ctrl) = var_ctrl"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
