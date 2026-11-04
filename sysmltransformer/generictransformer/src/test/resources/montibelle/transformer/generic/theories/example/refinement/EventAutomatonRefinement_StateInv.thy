theory EventAutomatonRefinement_StateInv
  imports
    (* Gen  *)  Event.Event Event.Event
    (* Hwl  *)

begin


fun stateInv:: "MultipleParameters_States.State \<Rightarrow> bool" where
"stateInv (MultipleParameters_States.StateConstr s) = True"


end
