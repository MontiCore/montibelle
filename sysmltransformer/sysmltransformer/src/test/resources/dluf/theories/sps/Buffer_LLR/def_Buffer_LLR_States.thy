theory def_Buffer_LLR_States
  imports
    (* Gen *) data_inc.Data_inc
    (* Hwl  *)

begin


datatype Substate = state__S

datatype State = StateConstr Substate                     "Packet list"                     "Packet list"

fun getSubstate :: "State \<Rightarrow> Substate" where
"getSubstate (StateConstr s _ _) = s"

fun getOld_packets :: "State \<Rightarrow> Packet list" where
"getOld_packets (StateConstr _ var_old_packets var_new_packets) = var_old_packets"

fun getNew_packets :: "State \<Rightarrow> Packet list" where
"getNew_packets (StateConstr _ var_old_packets var_new_packets) = var_new_packets"

instance Substate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance State :: countable
  apply(intro_classes)
  by(countable_datatype)


end
