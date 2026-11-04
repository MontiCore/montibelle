theory req_SecurityOfGate
  imports
    (* Core *) stream.StreamCodegen
    (* Gen  *) sps_SecurityGate_LLR.def_SecurityGate_LLR
    (* Hwl  *) SecurityGate_HWL.SecurityGate_HWL
begin

lemma req_SecurityOfGate:
  assumes "{channel_SecurityGate_LLR_input_dataConstr Alice_plus_Eve_request_Camera_accepts,
    channel_SecurityGate_LLR_input_dataConstr Bob_plus_Eve_request_Camera_accepts} \<inter> eValues\<cdot>input = {}"
    shows "(StateConstr state__Bob_Alice_Eve) \<notin> sreachableStates (behavior.eaut ())\<cdot>input"
  apply(simp add: sreachableStates_def autInitConfig.rep_eq autTransition.rep_eq behavior.eaut.rep_eq)
  apply(simp add: initialConfigs_def eventGen.config_def outconv_def image_comp behavior.ndaInitConfigC_def eventGen.ndaInitConfigC_def)
  apply(simp add: reachability_induction assms)
  (* autosledgi *) oops

end
