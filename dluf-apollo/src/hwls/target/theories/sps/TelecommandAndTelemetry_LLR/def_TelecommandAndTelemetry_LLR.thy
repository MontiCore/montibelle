theory def_TelecommandAndTelemetry_LLR
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_TelecommandAndTelemetry_HLR.def_TelecommandAndTelemetry_HLR_Input bundle_TelecommandAndTelemetry_HLR.def_TelecommandAndTelemetry_HLR_Output sps_TelecommandAndTelemetry_LLR_connector.def_TelecommandAndTelemetry_LLR_connector sps_TelecommandAndTelemetry_LLR_router.def_TelecommandAndTelemetry_LLR_router sps_TelecommandAndTelemetry_LLR_sorter.def_TelecommandAndTelemetry_LLR_sorter sps_TelecommandAndTelemetry_LLR_mergex.def_TelecommandAndTelemetry_LLR_mergex sps_TelecommandAndTelemetry_LLR_dldf.def_TelecommandAndTelemetry_LLR_dldf bundle_TelecommandAndTelemetry_LLR.def_TelecommandAndTelemetry_LLR_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern) .
    ((channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern), (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = ((channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern), (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_mergex_Input.buildSB"
               "def_TelecommandAndTelemetry_LLR_dldf_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_h2_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern) .
    ((channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern), (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = ((channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern), (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_sorter_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h2_map_def)+
    by(intro cont2cont)?

definition rawinput_h3_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h3_map \<equiv>
    \<lambda> (channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern) .
    ((channel_router_input_data_pattern), (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"

lemma rawinput_h3_map_insert[simp]:
    "rawinput_h3_map (channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = ((channel_router_input_data_pattern), (channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"
  by(simp add: rawinput_h3_map_def)

interpretation RawInput_h3:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_router_Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h3_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern) .
    ((channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern), (channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = ((channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern), (channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.buildSB"
               "RawInput_h3.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern) .
  ((channel_mergex_output_data_pattern), (channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = ((channel_mergex_output_data_pattern), (channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_mergex_Output.buildSB"
               "def_TelecommandAndTelemetry_LLR_dldf_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_h2_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern) .
  ((channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern), (channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = ((channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern), (channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_sorter_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h2_map_def)+
    by(intro cont2cont)?

definition rawoutput_h3_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h3_map \<equiv>
  \<lambda> (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern) .
  ((channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern), (channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"

lemma rawoutput_h3_map_insert[simp]:
  "rawoutput_h3_map (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = ((channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern), (channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"
  by(simp add: rawoutput_h3_map_def)

interpretation RawOutput_h3:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_router_Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h3_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern) .
  ((channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern), (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = ((channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern), (channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.buildSB"
               "RawOutput_h3.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_TelecommandAndTelemetry_LLR_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_TelecommandAndTelemetry_LLR_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.buildSB" "def_TelecommandAndTelemetry_LLR_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.buildSB" "def_TelecommandAndTelemetry_LLR_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_TelecommandAndTelemetry_LLR_rawinput2router \<equiv> (fst o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_TelecommandAndTelemetry_LLR_rawoutput2router \<equiv> (fst o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation router_input_Sub:
    subsetGen "RawInput.constructor" "def_TelecommandAndTelemetry_LLR_router_Input.buildSB" "def_TelecommandAndTelemetry_LLR_rawinput2router"
  apply(rule subsetgen_transitive)
  using RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation router_output_Sub:
    subsetGen "RawOutput.constructor" "def_TelecommandAndTelemetry_LLR_router_Output.buildSB" "def_TelecommandAndTelemetry_LLR_rawoutput2router"
  apply(rule subsetgen_transitive)
  using RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_TelecommandAndTelemetry_LLR_rawinput2sorter \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_TelecommandAndTelemetry_LLR_rawoutput2sorter \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation sorter_input_Sub:
    subsetGen "RawInput.constructor" "def_TelecommandAndTelemetry_LLR_sorter_Input.buildSB" "def_TelecommandAndTelemetry_LLR_rawinput2sorter"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation sorter_output_Sub:
    subsetGen "RawOutput.constructor" "def_TelecommandAndTelemetry_LLR_sorter_Output.buildSB" "def_TelecommandAndTelemetry_LLR_rawoutput2sorter"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_TelecommandAndTelemetry_LLR_rawinput2mergex \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_TelecommandAndTelemetry_LLR_rawoutput2mergex \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation mergex_input_Sub:
    subsetGen "RawInput.constructor" "def_TelecommandAndTelemetry_LLR_mergex_Input.buildSB" "def_TelecommandAndTelemetry_LLR_rawinput2mergex"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation mergex_output_Sub:
    subsetGen "RawOutput.constructor" "def_TelecommandAndTelemetry_LLR_mergex_Output.buildSB" "def_TelecommandAndTelemetry_LLR_rawoutput2mergex"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_TelecommandAndTelemetry_LLR_rawinput2dldf \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_TelecommandAndTelemetry_LLR_rawoutput2dldf \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation dldf_input_Sub:
    subsetGen "RawInput.constructor" "def_TelecommandAndTelemetry_LLR_dldf_Input.buildSB" "def_TelecommandAndTelemetry_LLR_rawinput2dldf"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation dldf_output_Sub:
    subsetGen "RawOutput.constructor" "def_TelecommandAndTelemetry_LLR_dldf_Output.buildSB" "def_TelecommandAndTelemetry_LLR_rawoutput2dldf"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_telecommandandtelemetry_llr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_telecommandandtelemetry_llr
    (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mirmisIn_data_pattern)"

interpretation def_TelecommandAndTelemetry_LLR_input_Sub:
    subsetGen "RawInput.constructor"
              "def_TelecommandAndTelemetry_HLR_Input.buildSB"
              "rawinput2def_telecommandandtelemetry_llr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_TelecommandAndTelemetry_HLR_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_router_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_sorter_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_mergex_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_dldf_Input.buildSB_def)+

fun rawoutput2def_telecommandandtelemetry_llr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_telecommandandtelemetry_llr
    (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mirmisOut_data_pattern)"

interpretation def_TelecommandAndTelemetry_LLR_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_TelecommandAndTelemetry_HLR_Output.buildSB"
              "rawoutput2def_telecommandandtelemetry_llr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_TelecommandAndTelemetry_HLR_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_router_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_sorter_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_mergex_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_dldf_Output.buildSB_def)+


fun rawinput2def_telecommandandtelemetry_llr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_telecommandandtelemetry_llr_feedback
    (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_cocaIn_data_pattern, channel_dfpIn_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern, channel_groundIn_data_pattern, channel_maniacIn_data_pattern, channel_mergex_output_data_pattern, channel_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern)
  = (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_TelecommandAndTelemetry_LLR_Feedback.buildSB"
              "rawinput2def_telecommandandtelemetry_llr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_TelecommandAndTelemetry_LLR_Feedback.buildSB_def
               def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_router_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_sorter_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_mergex_Input.buildSB_def
               def_TelecommandAndTelemetry_LLR_dldf_Input.buildSB_def)+

fun rawoutput2def_telecommandandtelemetry_llr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_telecommandandtelemetry_llr_feedback
    (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_cocaOut_data_pattern, channel_dfpOut_data_pattern, channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_groundOut_data_pattern, channel_maniacOut_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_mirmisOut_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)
  = (channel_dldf_input1_data_pattern, channel_dldf_input2_data_pattern, channel_dldf_input3_data_pattern, channel_dldf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_router_input_data_pattern, channel_sorter_b1In_data_pattern, channel_sorter_b2In_data_pattern, channel_sorter_cocaIn_data_pattern, channel_sorter_dfpIn_data_pattern, channel_sorter_maniacIn_data_pattern, channel_sorter_mirmisIn_data_pattern, channel_router_b1Out_data_pattern, channel_router_b2Out_data_pattern, channel_router_cocaOut_data_pattern, channel_router_dfpOut_data_pattern, channel_router_maniacOut_data_pattern, channel_router_mirmisOut_data_pattern, channel_sorter_prio1_data_pattern, channel_sorter_prio2_data_pattern, channel_sorter_prio3_data_pattern, channel_sorter_prio4_data_pattern, channel_mergex_output_data_pattern, channel_dldf_output1_data_pattern, channel_dldf_output2_data_pattern, channel_dldf_output3_data_pattern, channel_dldf_output4_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_TelecommandAndTelemetry_LLR_Feedback.buildSB"
              "rawoutput2def_telecommandandtelemetry_llr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_TelecommandAndTelemetry_LLR_Feedback.buildSB_def
               def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_router_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_sorter_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_mergex_Output.buildSB_def
               def_TelecommandAndTelemetry_LLR_dldf_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_router_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_sorter_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_mergex_Input.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Input.channels) - def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.channels \<union> def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.channels \<union> def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_TelecommandAndTelemetry_LLR_connector.Sps () \<Otimes> def_TelecommandAndTelemetry_LLR_router.Sps () \<Otimes> def_TelecommandAndTelemetry_LLR_sorter.Sps () \<Otimes> def_TelecommandAndTelemetry_LLR_mergex.Sps () \<Otimes> def_TelecommandAndTelemetry_LLR_dldf.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_TelecommandAndTelemetry_HLR_Input.channels) = chDom TYPE(((def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_router_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_sorter_Input.channels \<union> (def_TelecommandAndTelemetry_LLR_mergex_Input.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Input.channels) - def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels) - def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.channels \<union> def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_TelecommandAndTelemetry_HLR_Output.channels) \<subseteq> chDom TYPE((def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.channels \<union> def_TelecommandAndTelemetry_LLR_router_Output.channels \<union> def_TelecommandAndTelemetry_LLR_sorter_Output.channels \<union> def_TelecommandAndTelemetry_LLR_mergex_Output.channels \<union> def_TelecommandAndTelemetry_LLR_dldf_Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma connector_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma connector_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma router_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma router_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma sorter_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma sorter_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma mergex_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma mergex_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma dldf_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma dldf_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma router_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Router.Sps () \<Longrightarrow> P (def_Router_Input.SB.getter\<cdot>sb) (def_Router_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_TelecommandAndTelemetry_LLR_router_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_TelecommandAndTelemetry_LLR_router_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst router_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst router_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_TelecommandAndTelemetry_LLR_router.pred_inst2def assms: assms)
 

lemma sorter_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Sorter.Sps () \<Longrightarrow> P (def_Sorter_Input.SB.getter\<cdot>sb) (def_Sorter_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_TelecommandAndTelemetry_LLR_sorter_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_TelecommandAndTelemetry_LLR_sorter_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sorter_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst sorter_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_TelecommandAndTelemetry_LLR_sorter.pred_inst2def assms: assms)
 

lemma mergex_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Merge_LLR.Sps () \<Longrightarrow> P (def_Merge_LLR_Input.SB.getter\<cdot>sb) (def_Merge_LLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_TelecommandAndTelemetry_LLR_mergex_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_TelecommandAndTelemetry_LLR_mergex_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst mergex_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst mergex_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_TelecommandAndTelemetry_LLR_mergex.pred_inst2def assms: assms)
 

lemma dldf_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_DLDF_LLR.Sps (400, 300, 200, 100) \<Longrightarrow> P (def_DLDF_HLR1_Input.SB.getter\<cdot>sb) (def_DLDF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_TelecommandAndTelemetry_LLR_dldf_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_TelecommandAndTelemetry_LLR_dldf_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst dldf_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst dldf_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_TelecommandAndTelemetry_LLR_dldf.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_TelecommandAndTelemetry_LLR_connector.connector\<cdot>(def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_TelecommandAndTelemetry_LLR_connector_TelecommandAndTelemetry_LLR_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_TelecommandAndTelemetry_LLR_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_TelecommandAndTelemetry_LLR_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_TelecommandAndTelemetry_LLR_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_TelecommandAndTelemetry_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_TelecommandAndTelemetry_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
