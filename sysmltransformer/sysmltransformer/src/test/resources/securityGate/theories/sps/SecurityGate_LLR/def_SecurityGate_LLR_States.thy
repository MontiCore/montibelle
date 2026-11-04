theory def_SecurityGate_LLR_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__Bob_Alice | state__Bob | state__Alice | state__Bob_Alice_Eve | state__Alarm_Eve_detected

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
