theory def_EmptyAutOneState_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S

datatype State = StateConstr Substate 

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s ) = s"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
