theory Reachability
  imports
    (* Core *) stream.StreamCodegen
    (* Gen  *) Reachability
    (* Hwl  *)
begin

lemma Reachability:
  assumes "{channel_Cockpit_LLR_input_dataConstr P2_plus_Eve_request_P1_accepts,
channel_Cockpit_LLR_input_dataConstr P1_plus_Eve_request_P2_accepts} \<inter> eValues\<cdot>input = {}"
    shows "(StateConstr state__P1_P2_Eve) \<notin> sreachableStates (behavior.eaut ())\<cdot>input"
  apply(simp add: sreachableStates_def autInitConfig.rep_eq autTransition.rep_eq behavior.eaut.rep_eq)
  apply(simp add: initialConfigs_def eventGen.config_def outconv_def image_comp behavior.ndaInitConfigC_def eventGen.ndaInitConfigC_def)
  apply(simp add: h assms)
  (* autosledgi *) oops

end
