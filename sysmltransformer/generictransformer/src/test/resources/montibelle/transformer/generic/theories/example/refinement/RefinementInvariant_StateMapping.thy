theory RefinementInvariant_StateMapping
  imports
    (* Gen *) EventAutomatonInvariant.EventAutomatonInvariant_States EventAutomatonInvariant.EventAutomatonInvariant_States
    (* Hwl  *)

begin


fun stateMap :: "EventAutomatonInvariant_States.State \<Rightarrow> EventAutomatonInvariant_States.State" where
"stateMap (EventAutomatonInvariant_States.StateConstr s iTest) =
  (if (s=EventAutomatonInvariant_States.Substate.state__S) then
    (EventAutomatonInvariant_States.StateConstr EventAutomatonInvariant_States.Substate.state__S iTest)
  else
    (EventAutomatonInvariant_States.StateConstr EventAutomatonInvariant_States.Substate.state__T iTest)
)"


end
