theory def_Lambdas_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S

datatype State = StateConstr Substate             "(bool=>bool)"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getMap :: "State \<Rightarrow> (bool=>bool)" where
"getMap (StateConstr _ var_Map) = var_Map"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
