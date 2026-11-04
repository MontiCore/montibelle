theory TimesliceAutomatonRefinement_StateMapping
  imports
    (* Gen *) MultipleInitialStates.MultipleInitialStates_States MultipleInitialStates.MultipleInitialStates_States
    (* Hwl  *)

begin


fun stateMap :: "MultipleInitialStates_States.State \<Rightarrow> MultipleInitialStates_States.State" where
"stateMap (MultipleInitialStates_States.StateConstr s iVar sVar) =
  (if (s=MultipleInitialStates_States.Substate.state__S) then
    (MultipleInitialStates_States.StateConstr MultipleInitialStates_States.Substate.state__S iVar sVar)
  else
    (MultipleInitialStates_States.StateConstr MultipleInitialStates_States.Substate.state__T iVar sVar)
)"


end
