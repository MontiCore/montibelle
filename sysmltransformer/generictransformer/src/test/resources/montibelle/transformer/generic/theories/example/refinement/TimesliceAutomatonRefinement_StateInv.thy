theory TimesliceAutomatonRefinement_StateInv
  imports
    (* Gen  *)  MultipleInitialStates.MultipleInitialStates MultipleInitialStates.MultipleInitialStates
    (* Hwl  *)

begin


fun stateInv:: "MultipleInitialStates_States.State \<Rightarrow> bool" where
"stateInv (MultipleInitialStates_States.StateConstr s iVar sVar) = True"


end
