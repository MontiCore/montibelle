theory VariableComprehension_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S | state__T

datatype State = StateConstr Substate              "int"              "string"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _ _) = s"

fun getIvar :: "State \<Rightarrow> int" where
"getIvar (StateConstr _ iVar sVar) = iVar"

fun getSvar :: "State \<Rightarrow> string" where
"getSvar (StateConstr _ iVar sVar) = sVar"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
