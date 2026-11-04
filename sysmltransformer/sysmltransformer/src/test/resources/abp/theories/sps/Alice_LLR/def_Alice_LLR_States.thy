theory def_Alice_LLR_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__EmptyBuf | state__SingleBuf | state__MultiBuf

datatype State = StateConstr Substate              "bool"                "string list"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _ _) = s"

fun getCtrl :: "State \<Rightarrow> bool" where
"getCtrl (StateConstr _ var_ctrl var_buffer) = var_ctrl"

fun getBuffer :: "State \<Rightarrow> string list" where
"getBuffer (StateConstr _ var_ctrl var_buffer) = var_buffer"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
