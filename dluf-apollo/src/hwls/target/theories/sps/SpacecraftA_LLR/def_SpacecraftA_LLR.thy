theory def_SpacecraftA_LLR
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_SpacecraftA_HLR.def_SpacecraftA_HLR_Input bundle_SpacecraftA_HLR.def_SpacecraftA_HLR_Output sps_SpacecraftA_LLR_connector.def_SpacecraftA_LLR_connector sps_SpacecraftA_LLR_coca.def_SpacecraftA_LLR_coca sps_SpacecraftA_LLR_maniac.def_SpacecraftA_LLR_maniac sps_SpacecraftA_LLR_dfp.def_SpacecraftA_LLR_dfp sps_SpacecraftA_LLR_mirmis.def_SpacecraftA_LLR_mirmis sps_SpacecraftA_LLR_tele.def_SpacecraftA_LLR_tele bundle_SpacecraftA_LLR.def_SpacecraftA_LLR_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern) .
    ((channel_mirmis_input_data_pattern), (channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = ((channel_mirmis_input_data_pattern), (channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_SpacecraftA_LLR_mirmis_Input.buildSB"
               "def_SpacecraftA_LLR_tele_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_h2_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern) .
    ((channel_dfp_input_data_pattern), (channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = ((channel_dfp_input_data_pattern), (channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "def_SpacecraftA_LLR_dfp_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h2_map_def)+
    by(intro cont2cont)?

definition rawinput_h3_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h3_map \<equiv>
    \<lambda> (channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern) .
    ((channel_maniac_input_data_pattern), (channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"

lemma rawinput_h3_map_insert[simp]:
    "rawinput_h3_map (channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = ((channel_maniac_input_data_pattern), (channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"
  by(simp add: rawinput_h3_map_def)

interpretation RawInput_h3:
    sbUnionGen "def_SpacecraftA_LLR_maniac_Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h3_map_def)+
    by(intro cont2cont)?

definition rawinput_h4_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h4_map \<equiv>
    \<lambda> (channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern) .
    ((channel_coca_input_data_pattern), (channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"

lemma rawinput_h4_map_insert[simp]:
    "rawinput_h4_map (channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = ((channel_coca_input_data_pattern), (channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"
  by(simp add: rawinput_h4_map_def)

interpretation RawInput_h4:
    sbUnionGen "def_SpacecraftA_LLR_coca_Input.buildSB"
               "RawInput_h3.constructor"
               "rawinput_h4_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h4_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern, channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern) .
    ((channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern), (channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern, channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = ((channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern), (channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.buildSB"
               "RawInput_h4.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern) .
  ((channel_mirmis_output_data_pattern), (channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = ((channel_mirmis_output_data_pattern), (channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_SpacecraftA_LLR_mirmis_Output.buildSB"
               "def_SpacecraftA_LLR_tele_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_h2_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern) .
  ((channel_dfp_output_data_pattern), (channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = ((channel_dfp_output_data_pattern), (channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "def_SpacecraftA_LLR_dfp_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h2_map_def)+
    by(intro cont2cont)?

definition rawoutput_h3_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h3_map \<equiv>
  \<lambda> (channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern) .
  ((channel_maniac_output_data_pattern), (channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"

lemma rawoutput_h3_map_insert[simp]:
  "rawoutput_h3_map (channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = ((channel_maniac_output_data_pattern), (channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"
  by(simp add: rawoutput_h3_map_def)

interpretation RawOutput_h3:
    sbUnionGen "def_SpacecraftA_LLR_maniac_Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h3_map_def)+
    by(intro cont2cont)?

definition rawoutput_h4_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h4_map \<equiv>
  \<lambda> (channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern) .
  ((channel_coca_output_data_pattern), (channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"

lemma rawoutput_h4_map_insert[simp]:
  "rawoutput_h4_map (channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = ((channel_coca_output_data_pattern), (channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"
  by(simp add: rawoutput_h4_map_def)

interpretation RawOutput_h4:
    sbUnionGen "def_SpacecraftA_LLR_coca_Output.buildSB"
               "RawOutput_h3.constructor"
               "rawoutput_h4_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h4_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern) .
  ((channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern), (channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = ((channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern), (channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.buildSB"
               "RawOutput_h4.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_SpacecraftA_LLR_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.buildSB" "def_SpacecraftA_LLR_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SpacecraftA_LLR_rawinput2coca \<equiv> (fst o rawinput_h4_map) o (snd o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2coca \<equiv> (fst o rawoutput_h4_map) o (snd o rawoutput_map)"

interpretation coca_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_coca_Input.buildSB" "def_SpacecraftA_LLR_rawinput2coca"
  apply(rule subsetgen_transitive)
  using RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation coca_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_coca_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2coca"
  apply(rule subsetgen_transitive)
  using RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SpacecraftA_LLR_rawinput2maniac \<equiv> (fst o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2maniac \<equiv> (fst o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_map)"

interpretation maniac_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_maniac_Input.buildSB" "def_SpacecraftA_LLR_rawinput2maniac"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation maniac_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_maniac_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2maniac"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SpacecraftA_LLR_rawinput2dfp \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2dfp \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_map)"

interpretation dfp_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_dfp_Input.buildSB" "def_SpacecraftA_LLR_rawinput2dfp"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation dfp_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_dfp_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2dfp"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SpacecraftA_LLR_rawinput2mirmis \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2mirmis \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_map)"

interpretation mirmis_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_mirmis_Input.buildSB" "def_SpacecraftA_LLR_rawinput2mirmis"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation mirmis_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_mirmis_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2mirmis"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SpacecraftA_LLR_rawinput2tele \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_map)"

abbreviation "def_SpacecraftA_LLR_rawoutput2tele \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_map)"

interpretation tele_input_Sub:
    subsetGen "RawInput.constructor" "def_SpacecraftA_LLR_tele_Input.buildSB" "def_SpacecraftA_LLR_rawinput2tele"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation tele_output_Sub:
    subsetGen "RawOutput.constructor" "def_SpacecraftA_LLR_tele_Output.buildSB" "def_SpacecraftA_LLR_rawoutput2tele"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_spacecrafta_llr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_spacecrafta_llr
    (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern, channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_groundIn_data_pattern)"

interpretation def_SpacecraftA_LLR_input_Sub:
    subsetGen "RawInput.constructor"
              "def_SpacecraftA_HLR_Input.buildSB"
              "rawinput2def_spacecrafta_llr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_SpacecraftA_HLR_Input.buildSB_def
               def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.buildSB_def
               def_SpacecraftA_LLR_coca_Input.buildSB_def
               def_SpacecraftA_LLR_maniac_Input.buildSB_def
               def_SpacecraftA_LLR_dfp_Input.buildSB_def
               def_SpacecraftA_LLR_mirmis_Input.buildSB_def
               def_SpacecraftA_LLR_tele_Input.buildSB_def)+

fun rawoutput2def_spacecrafta_llr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_spacecrafta_llr
    (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_groundOut_data_pattern)"

interpretation def_SpacecraftA_LLR_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_SpacecraftA_HLR_Output.buildSB"
              "rawoutput2def_spacecrafta_llr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_SpacecraftA_HLR_Output.buildSB_def
               def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.buildSB_def
               def_SpacecraftA_LLR_coca_Output.buildSB_def
               def_SpacecraftA_LLR_maniac_Output.buildSB_def
               def_SpacecraftA_LLR_dfp_Output.buildSB_def
               def_SpacecraftA_LLR_mirmis_Output.buildSB_def
               def_SpacecraftA_LLR_tele_Output.buildSB_def)+


fun rawinput2def_spacecrafta_llr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_spacecrafta_llr_feedback
    (channel_b1In_data_pattern, channel_b2In_data_pattern, channel_coca_output_data_pattern, channel_dfp_output_data_pattern, channel_groundIn_data_pattern, channel_maniac_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern, channel_coca_input_data_pattern, channel_maniac_input_data_pattern, channel_dfp_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern)
  = (channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_SpacecraftA_LLR_Feedback.buildSB"
              "rawinput2def_spacecrafta_llr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_SpacecraftA_LLR_Feedback.buildSB_def
               def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.buildSB_def
               def_SpacecraftA_LLR_coca_Input.buildSB_def
               def_SpacecraftA_LLR_maniac_Input.buildSB_def
               def_SpacecraftA_LLR_dfp_Input.buildSB_def
               def_SpacecraftA_LLR_mirmis_Input.buildSB_def
               def_SpacecraftA_LLR_tele_Input.buildSB_def)+

fun rawoutput2def_spacecrafta_llr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_spacecrafta_llr_feedback
    (channel_b1Out_data_pattern, channel_b2Out_data_pattern, channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_groundOut_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)
  = (channel_coca_input_data_pattern, channel_dfp_input_data_pattern, channel_maniac_input_data_pattern, channel_mirmis_input_data_pattern, channel_tele_b1In_data_pattern, channel_tele_b2In_data_pattern, channel_tele_cocaIn_data_pattern, channel_tele_dfpIn_data_pattern, channel_tele_groundIn_data_pattern, channel_tele_maniacIn_data_pattern, channel_tele_mirmisIn_data_pattern, channel_coca_output_data_pattern, channel_maniac_output_data_pattern, channel_dfp_output_data_pattern, channel_mirmis_output_data_pattern, channel_tele_b1Out_data_pattern, channel_tele_b2Out_data_pattern, channel_tele_cocaOut_data_pattern, channel_tele_dfpOut_data_pattern, channel_tele_groundOut_data_pattern, channel_tele_maniacOut_data_pattern, channel_tele_mirmisOut_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_SpacecraftA_LLR_Feedback.buildSB"
              "rawoutput2def_spacecrafta_llr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_SpacecraftA_LLR_Feedback.buildSB_def
               def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.buildSB_def
               def_SpacecraftA_LLR_coca_Output.buildSB_def
               def_SpacecraftA_LLR_maniac_Output.buildSB_def
               def_SpacecraftA_LLR_dfp_Output.buildSB_def
               def_SpacecraftA_LLR_mirmis_Output.buildSB_def
               def_SpacecraftA_LLR_tele_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.channels \<union> (def_SpacecraftA_LLR_coca_Input.channels \<union> (def_SpacecraftA_LLR_maniac_Input.channels \<union> (def_SpacecraftA_LLR_dfp_Input.channels \<union> (def_SpacecraftA_LLR_mirmis_Input.channels \<union> def_SpacecraftA_LLR_tele_Input.channels) - def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.channels \<union> def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.channels \<union> def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_SpacecraftA_LLR_connector.Sps () \<Otimes> def_SpacecraftA_LLR_coca.Sps () \<Otimes> def_SpacecraftA_LLR_maniac.Sps () \<Otimes> def_SpacecraftA_LLR_dfp.Sps () \<Otimes> def_SpacecraftA_LLR_mirmis.Sps () \<Otimes> def_SpacecraftA_LLR_tele.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_SpacecraftA_HLR_Input.channels) = chDom TYPE(((def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.channels \<union> (def_SpacecraftA_LLR_coca_Input.channels \<union> (def_SpacecraftA_LLR_maniac_Input.channels \<union> (def_SpacecraftA_LLR_dfp_Input.channels \<union> (def_SpacecraftA_LLR_mirmis_Input.channels \<union> def_SpacecraftA_LLR_tele_Input.channels) - def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels) - def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.channels \<union> def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_SpacecraftA_HLR_Output.channels) \<subseteq> chDom TYPE((def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.channels \<union> def_SpacecraftA_LLR_coca_Output.channels \<union> def_SpacecraftA_LLR_maniac_Output.channels \<union> def_SpacecraftA_LLR_dfp_Output.channels \<union> def_SpacecraftA_LLR_mirmis_Output.channels \<union> def_SpacecraftA_LLR_tele_Output.channels))"
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


lemma coca_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma coca_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma maniac_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma maniac_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma dfp_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma dfp_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma mirmis_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma mirmis_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma tele_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma tele_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma coca_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_CometCamera.Sps () \<Longrightarrow> P (def_CometCamera_Input.SB.getter\<cdot>sb) (def_CometCamera_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SpacecraftA_LLR_coca_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SpacecraftA_LLR_coca_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst coca_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst coca_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SpacecraftA_LLR_coca.pred_inst2def assms: assms)
 

lemma maniac_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_MANiaC.Sps () \<Longrightarrow> P (def_MANiaC_Input.SB.getter\<cdot>sb) (def_MANiaC_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SpacecraftA_LLR_maniac_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SpacecraftA_LLR_maniac_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst maniac_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst maniac_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SpacecraftA_LLR_maniac.pred_inst2def assms: assms)
 

lemma dfp_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_DFP.Sps () \<Longrightarrow> P (def_DFP_Input.SB.getter\<cdot>sb) (def_DFP_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SpacecraftA_LLR_dfp_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SpacecraftA_LLR_dfp_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst dfp_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst dfp_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SpacecraftA_LLR_dfp.pred_inst2def assms: assms)
 

lemma mirmis_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_MIRMIS.Sps () \<Longrightarrow> P (def_MIRMIS_Input.SB.getter\<cdot>sb) (def_MIRMIS_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SpacecraftA_LLR_mirmis_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SpacecraftA_LLR_mirmis_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst mirmis_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst mirmis_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SpacecraftA_LLR_mirmis.pred_inst2def assms: assms)
 

lemma tele_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_TelecommandAndTelemetry_LLR.Sps () \<Longrightarrow> P (def_TelecommandAndTelemetry_HLR_Input.SB.getter\<cdot>sb) (def_TelecommandAndTelemetry_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SpacecraftA_LLR_tele_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SpacecraftA_LLR_tele_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst tele_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst tele_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SpacecraftA_LLR_tele.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_SpacecraftA_LLR_connector.connector\<cdot>(def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_SpacecraftA_LLR_connector_SpacecraftA_LLR_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_SpacecraftA_LLR_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_SpacecraftA_LLR_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_SpacecraftA_LLR_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_SpacecraftA_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_SpacecraftA_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
