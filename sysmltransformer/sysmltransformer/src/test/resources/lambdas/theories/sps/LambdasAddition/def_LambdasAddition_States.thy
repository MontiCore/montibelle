theory def_LambdasAddition_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S

datatype State = StateConstr Substate             "(nat=>nat=>nat)"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _) = s"

fun getMap :: "State \<Rightarrow> (nat=>nat=>nat)" where
"getMap (StateConstr _ var_Map) = var_Map"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)


end
