theory EventAutomatonRefinement_StateMapping
  imports
    (* Gen *) MultipleParameters.MultipleParameters_States MultipleParameters.MultipleParameters_States
    (* Hwl  *)

begin


fun stateMap :: "MultipleParameters_States.State \<Rightarrow> MultipleParameters_States.State" where
"stateMap (MultipleParameters_States.StateConstr s ) =
  (if (s=MultipleParameters_States.Substate.state__S) then
    (MultipleParameters_States.StateConstr MultipleParameters_States.Substate.state__S )
  else
    (MultipleParameters_States.StateConstr MultipleParameters_States.Substate.state__T )
)"


end
