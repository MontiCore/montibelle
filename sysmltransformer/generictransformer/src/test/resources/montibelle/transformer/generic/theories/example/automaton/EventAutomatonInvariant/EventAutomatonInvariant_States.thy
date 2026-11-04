theory EventAutomatonInvariant_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S | state__T

datatype State = StateConstr Substate               "int"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getItest :: "State \<Rightarrow> int" where
"getItest (StateConstr _ iTest) = iTest"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
