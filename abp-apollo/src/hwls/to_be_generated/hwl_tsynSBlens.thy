theory hwl_tsynSBlens
  imports
    bundle.TsynSBFunction

    move_to_core.hwl_core_ext
    move_to_core.TsynSBFunctionExtension

    tsynchans
begin




lemma def_SecureProtocol_HLR1_Input_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR1_Input.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR1_Input.channels_exists)
   defer
   apply(case_tac "c")       
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR1_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?



lemma def_Eve1_HLR_Input_tsynSBlen_setter: "tsynSBlen (def_Eve1_HLR_Input.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Eve1_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")       
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve1_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Eve1_HLR_Input_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Eve1_HLR_Input.SB.setter\<cdot>out)) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Eve1_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")       
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve1_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Eve1_HLR_Output_tsynSBlen_setter: "tsynSBlen (def_Eve1_HLR_Output.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Eve1_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve1_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Eve1_HLR_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Eve1_HLR_Output.SB.setter\<cdot>out)) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Eve1_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve1_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?



lemma def_Eve2_HLR_Input_tsynSBlen_setter: "tsynSBlen (def_Eve2_HLR_Input.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Eve2_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")       
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve2_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Eve2_HLR_Input_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Eve2_HLR_Input.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Eve2_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")       
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve2_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Eve2_HLR_Output_tsynSBlen_setter: "tsynSBlen (def_Eve2_HLR_Output.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Eve2_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve2_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_Eve2_HLR_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Eve2_HLR_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Eve2_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Eve2_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_Bob_HLR_Input_tsynSBlen_setter: "tsynSBlen (def_Bob_HLR_Input.SB.setter\<cdot>out1) = Min {tsynLen\<cdot>out1}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Bob_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Bob_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_Bob_HLR_Input_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Bob_HLR_Input.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Bob_HLR_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Bob_HLR_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_Bob_HLR_Output_tsynSBlen_setter: "tsynSBlen (def_Bob_HLR_Output.SB.setter\<cdot>(out1, out2)) = Min {tsynLen\<cdot>out1, tsynLen\<cdot>out2}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_Bob_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Bob_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_Bob_HLR_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_Bob_HLR_Output.SB.setter\<cdot>(out1, out2))) = Min {
    tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>out1)),
    tsynLen\<cdot>(f\<cdot>((smap (map_tsyn natEVENTConstr))\<cdot>out2))
  }"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_Bob_HLR_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_Bob_HLR_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_alice_Output_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_alice_Output.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_alice_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_alice_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_SecureProtocol_HLR2_decrypt2_Output_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_decrypt2_Output.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_decrypt2_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_decrypt2_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_alice_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_alice_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_alice_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_alice_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_eve2_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve2_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_eve2_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_eve2_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve2_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_eve1_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_eve1_Output.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_eve1_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_eve1_Input.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_eve1_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_eve1_Input.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_eve1_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve1_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_bob_Input.SB.setter\<cdot>(ins)) = Min {tsynLen\<cdot>ins}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_bob_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_bob_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?

lemma def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter_f: 
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_bob_Input.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn DataBoolTupleEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_bob_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_bob_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_bob_Output_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>(ctrl, out)) = Min {tsynLen\<cdot>ctrl, tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_bob_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_bob_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_bob_Output_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_bob_Output.SB.setter\<cdot>(ctrl, out))) = Min {
    tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>ctrl)),
    tsynLen\<cdot>(f\<cdot>((smap (map_tsyn natEVENTConstr))\<cdot>out))
  }"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_bob_Output.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_bob_Output.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter: "tsynSBlen (def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>(out)) = Min {tsynLen\<cdot>out}"
  apply(rule tsynSBlen_rule, simp_all)
  defer
   apply (rule def_SecureProtocol_HLR2_eve2_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve2_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?


lemma def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_f:
  assumes "is_lifted_tsyn_stream_fn F f"
  shows "tsynSBlen (F\<cdot>(def_SecureProtocol_HLR2_eve2_Input.SB.setter\<cdot>(out))) = Min {tsynLen\<cdot>(f\<cdot>((smap (map_tsyn boolEVENTConstr))\<cdot>out))}"
  apply(rule tsynSBlen_rule_liftedTsynSpf[of _ f], simp_all add: assms)
  defer
   apply (rule def_SecureProtocol_HLR2_eve2_Input.channels_exists)
   defer
   apply(case_tac "c")
     apply(simp_all add: tsynLenM_def toTsynMsgStream_def def_SecureProtocol_HLR2_eve2_Input.buildSB_def smapsmap2smap comp_def
              tsynLen_smap_map_tsyn[symmetric] min_le_iff_disj)
  by (metis min_def)?



lemma
def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter_eq_def_Eve1_HLR_Input_tsynSBlen_setter:
"tsynSBlen (def_SecureProtocol_HLR2_eve1_Input.sbsetter\<cdot>(def_Eve1_HLR_Input.sbgetter\<cdot>sb))
  = tsynSBlen sb"
  apply(simp add: def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter)
  by (metis Min.singleton def_Eve1_HLR_Input.SB.set_get def_Eve1_HLR_Input_tsynSBlen_setter)

lemma
def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter_eq_def_Eve1_HLR_Output_tsynSBlen_setter:
 "tsynSBlen (def_SecureProtocol_HLR2_eve1_Output.sbsetter\<cdot>(def_Eve1_HLR_Output.sbgetter\<cdot>(spf\<cdot>gsb))) = tsynSBlen (spf\<cdot>gsb)"
  apply(simp add: def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter)
  by (metis Min.singleton def_Eve1_HLR_Output.SB.set_get def_Eve1_HLR_Output_tsynSBlen_setter)

lemma
def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_eq_def_Eve2_HLR_Input_tsynSBlen_setter:
"tsynSBlen (def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(def_Eve2_HLR_Input.sbgetter\<cdot>sb))
  = tsynSBlen sb"
  apply(simp add: def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter)
  by (metis Min.singleton def_Eve2_HLR_Input.SB.set_get def_Eve2_HLR_Input_tsynSBlen_setter)

lemma
def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter_eq_def_Eve2_HLR_Output_tsynSBlen_setter:
 "tsynSBlen (def_SecureProtocol_HLR2_eve2_Output.sbsetter\<cdot>(def_Eve2_HLR_Output.sbgetter\<cdot>(spf\<cdot>gsb))) = tsynSBlen (spf\<cdot>gsb)"
  apply(simp add: def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter)
  by (metis Min.singleton def_Eve2_HLR_Output.SB.set_get def_Eve2_HLR_Output_tsynSBlen_setter)


lemma
def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_geq_def_Bob_HLR_Output_tsynSBlen_setter_fst:
"tsynSBlen (def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(fst (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>sb)))
  \<ge> tsynSBlen sb"
  apply(simp add: def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter)
  apply(insert def_SecureProtocol_HLR2_bob_Output_tsynSBlen_setter[of "fst (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>sb)"  "snd (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>sb)"])
  by auto

lemma
def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter_eq_def_Bob_HLR_Input_tsynSBlen_setter:
"tsynSBlen (def_SecureProtocol_HLR2_bob_Input.sbsetter\<cdot>(def_Bob_HLR_Input.sbgetter\<cdot>sb))
  = tsynSBlen sb"
  apply(simp add: def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter)
  by (metis Min.singleton def_Bob_HLR_Input.SB.set_get def_Bob_HLR_Input_tsynSBlen_setter)

lemma
def_SecureProtocol_HLR2_bob_Output_tsynSBlen_setter_eq_def_Bob_HLR_Output_tsynSBlen_setter:
 "tsynSBlen (def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>(def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))) = tsynSBlen (spf\<cdot>sb)"
proof -
  obtain ctrl outs where s: "def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb) = (ctrl, outs)"
    by fastforce
  show ?thesis
    apply(subst s)
    apply(simp add: def_SecureProtocol_HLR2_bob_Output_tsynSBlen_setter)
    by (metis Min_insert Min_singleton def_Bob_HLR_Output.SB.set_get def_Bob_HLR_Output_tsynSBlen_setter finite.emptyI finite_insert insert_not_empty s)
qed

end
