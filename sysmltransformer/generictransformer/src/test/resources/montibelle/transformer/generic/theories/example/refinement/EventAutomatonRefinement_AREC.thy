theory EventAutomatonRefinement_AREC
  imports
    (* Core *) automaton.AREC
    (* Gen  *) Event.Event Event.Event EventAutomatonRefinement_StateMapping EventAutomatonRefinement_ParamMapping
    (* Hwl  *)

begin


ML_val \<open>checkStateRefinement @{context}
  @{term "(\<lambda> p state sbe. Event.transitionH_00 p state sbe \<union> Event.transitionH_01 p state sbe)"}
  @{term "paramMap"}
  @{term "stateMap"}
  Event.beInChannel_transitionList \<close>

ML_val \<open>checkStateRefinement_tick @{context}
  @{term "(\<lambda> p state. Event.transitionTH_0 p state \<union> Event.transitionTH_1 p state)"}
  @{term "paramMap"}
  @{term "stateMap"}
  Event.tick_transitionList \<close>


end
