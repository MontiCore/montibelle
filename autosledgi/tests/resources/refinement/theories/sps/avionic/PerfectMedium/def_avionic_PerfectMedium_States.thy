theory def_avionic_PerfectMedium_States
  imports data_inc.Data_inc

begin


datatype Substate = state__State

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
