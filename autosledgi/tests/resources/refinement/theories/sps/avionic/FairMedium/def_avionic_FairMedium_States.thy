theory def_avionic_FairMedium_States
  imports data_inc.Data_inc

begin


datatype Substate = state__State

datatype State = StateConstr Substate                 "nat"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getCounter :: "State \<Rightarrow> nat" where
"getCounter (StateConstr _ var_counter) = var_counter"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
