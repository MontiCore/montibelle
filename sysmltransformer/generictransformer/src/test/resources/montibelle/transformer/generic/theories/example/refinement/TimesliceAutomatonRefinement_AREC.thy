theory TimesliceAutomatonRefinement_AREC
  imports
    (* Core *) automaton.AREC
    (* Gen  *) MultipleInitialStates.MultipleInitialStates MultipleInitialStates.MultipleInitialStates TimesliceAutomatonRefinement_StateMapping TimesliceAutomatonRefinement_ParamMapping
    (* Hwl  *)

begin


ML_val \<open>checkStateRefinement @{context}
  @{term MultipleInitialStates.transition}
  @{term "paramMap"}
  @{term "stateMap"}
  MultipleInitialStates.transitionList \<close>


end
