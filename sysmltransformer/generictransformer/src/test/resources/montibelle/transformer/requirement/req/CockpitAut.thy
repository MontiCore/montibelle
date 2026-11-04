theory Reachability
  imports (* Gen *) sps_Cockpit_LLR.def_Cockpit_LLR
          (* HWL *) hwl.Reachability_HWL
begin

lemma security_eve_not_in_cockpit:
  assumes "{channel_Cockpit_LLR_input_dataConstr P2_plus_Eve_request_P1_accepts,
    channel_Cockpit_LLR_input_dataConstr P1_plus_Eve_request_P2_accepts} \<inter> eValues\<cdot>input = {}"
  shows "(StateConstr state__P1_P2_Eve) \<notin> sreachableStates (behavior.eaut ())\<cdot>input"
  apply(simp add: sreachableStates_def autInitConfig.rep_eq autTransition.rep_eq behavior.eaut.rep_eq)
  apply(simp add: initialConfigs_def eventGen.config_def outconv_def image_comp behavior.ndaInitConfigC_def eventGen.ndaInitConfigC_def)
  apply(simp add: h assms)
  (* autosledgi *) oops

end
