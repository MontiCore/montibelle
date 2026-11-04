theory RefinementInvariant_StateInv
  imports
    (* Gen  *)  EventAutomatonInvariant.EventAutomatonInvariant EventAutomatonInvariant.EventAutomatonInvariant
    (* Hwl  *)

begin


fun stateInv:: "EventAutomatonInvariant_States.State \<Rightarrow> bool" where
"stateInv (EventAutomatonInvariant_States.StateConstr s iTest) = True"


end
