theory def_SecureProtocol_HLR2
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_SecureProtocol_HLR1.def_SecureProtocol_HLR1_Input bundle_SecureProtocol_HLR1.def_SecureProtocol_HLR1_Output sps_SecureProtocol_HLR2_connector.def_SecureProtocol_HLR2_connector sps_SecureProtocol_HLR2_alice.def_SecureProtocol_HLR2_alice sps_SecureProtocol_HLR2_encrypt1.def_SecureProtocol_HLR2_encrypt1 sps_SecureProtocol_HLR2_eve1.def_SecureProtocol_HLR2_eve1 sps_SecureProtocol_HLR2_decrypt1.def_SecureProtocol_HLR2_decrypt1 sps_SecureProtocol_HLR2_bob.def_SecureProtocol_HLR2_bob sps_SecureProtocol_HLR2_encrypt2.def_SecureProtocol_HLR2_encrypt2 sps_SecureProtocol_HLR2_eve2.def_SecureProtocol_HLR2_eve2 sps_SecureProtocol_HLR2_decrypt2.def_SecureProtocol_HLR2_decrypt2 bundle_SecureProtocol_HLR2.def_SecureProtocol_HLR2_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((bool tsyn stream) \<times> (bool tsyn stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_eve2_input_val_pattern), (channel_decrypt2_input_val_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_eve2_input_val_pattern), (channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_SecureProtocol_HLR2_eve2_Input.buildSB"
               "def_SecureProtocol_HLR2_decrypt2_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_h2_map ::
    "(bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((bool tsyn stream) \<times> (bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_encrypt2_input_val_pattern), (channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_encrypt2_input_val_pattern), (channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "def_SecureProtocol_HLR2_encrypt2_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h2_map_def)+
    by(intro cont2cont)?

definition rawinput_h3_map ::
    "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((Data_Bool_Tuple tsyn stream) \<times> (bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h3_map \<equiv>
    \<lambda> (channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_bob_input_val_pattern), (channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h3_map_insert[simp]:
    "rawinput_h3_map (channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_bob_input_val_pattern), (channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h3_map_def)

interpretation RawInput_h3:
    sbUnionGen "def_SecureProtocol_HLR2_bob_Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h3_map_def)+
    by(intro cont2cont)?

definition rawinput_h4_map ::
    "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h4_map \<equiv>
    \<lambda> (channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_decrypt1_input_val_pattern), (channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h4_map_insert[simp]:
    "rawinput_h4_map (channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_decrypt1_input_val_pattern), (channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h4_map_def)

interpretation RawInput_h4:
    sbUnionGen "def_SecureProtocol_HLR2_decrypt1_Input.buildSB"
               "RawInput_h3.constructor"
               "rawinput_h4_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h4_map_def)+
    by(intro cont2cont)?

definition rawinput_h5_map ::
    "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h5_map \<equiv>
    \<lambda> (channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_eve1_input_val_pattern), (channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h5_map_insert[simp]:
    "rawinput_h5_map (channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_eve1_input_val_pattern), (channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h5_map_def)

interpretation RawInput_h5:
    sbUnionGen "def_SecureProtocol_HLR2_eve1_Input.buildSB"
               "RawInput_h4.constructor"
               "rawinput_h5_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h5_map_def)+
    by(intro cont2cont)?

definition rawinput_h6_map ::
    "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h6_map \<equiv>
    \<lambda> (channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_encrypt1_input_val_pattern), (channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h6_map_insert[simp]:
    "rawinput_h6_map (channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_encrypt1_input_val_pattern), (channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h6_map_def)

interpretation RawInput_h6:
    sbUnionGen "def_SecureProtocol_HLR2_encrypt1_Input.buildSB"
               "RawInput_h5.constructor"
               "rawinput_h6_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h6_map_def)+
    by(intro cont2cont)?

definition rawinput_h7_map ::
    "(bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((bool tsyn stream \<times> nat tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_h7_map \<equiv>
    \<lambda> (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_alice_control_val_pattern, channel_alice_input_val_pattern), (channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_h7_map_insert[simp]:
    "rawinput_h7_map (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_alice_control_val_pattern, channel_alice_input_val_pattern), (channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_h7_map_def)

interpretation RawInput_h7:
    sbUnionGen "def_SecureProtocol_HLR2_alice_Input.buildSB"
               "RawInput_h6.constructor"
               "rawinput_h7_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h7_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
    ((Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream) \<times> (bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern, channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern) .
    ((channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern), (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern, channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = ((channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern), (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.buildSB"
               "RawInput_h7.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((bool tsyn stream) \<times> (bool tsyn stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_eve2_output_val_pattern), (channel_decrypt2_output_val_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_eve2_output_val_pattern), (channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_SecureProtocol_HLR2_eve2_Output.buildSB"
               "def_SecureProtocol_HLR2_decrypt2_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_h2_map ::
  "(bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((bool tsyn stream) \<times> (bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_encrypt2_output_val_pattern), (channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_encrypt2_output_val_pattern), (channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "def_SecureProtocol_HLR2_encrypt2_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h2_map_def)+
    by(intro cont2cont)?

definition rawoutput_h3_map ::
  "(bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((bool tsyn stream \<times> nat tsyn stream) \<times> (bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h3_map \<equiv>
  \<lambda> (channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_bob_control_val_pattern, channel_bob_output_val_pattern), (channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h3_map_insert[simp]:
  "rawoutput_h3_map (channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_bob_control_val_pattern, channel_bob_output_val_pattern), (channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h3_map_def)

interpretation RawOutput_h3:
    sbUnionGen "def_SecureProtocol_HLR2_bob_Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h3_map_def)+
    by(intro cont2cont)?

definition rawoutput_h4_map ::
  "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((Data_Bool_Tuple tsyn stream) \<times> (bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h4_map \<equiv>
  \<lambda> (channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_decrypt1_output_val_pattern), (channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h4_map_insert[simp]:
  "rawoutput_h4_map (channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_decrypt1_output_val_pattern), (channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h4_map_def)

interpretation RawOutput_h4:
    sbUnionGen "def_SecureProtocol_HLR2_decrypt1_Output.buildSB"
               "RawOutput_h3.constructor"
               "rawoutput_h4_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h4_map_def)+
    by(intro cont2cont)?

definition rawoutput_h5_map ::
  "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h5_map \<equiv>
  \<lambda> (channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_eve1_output_val_pattern), (channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h5_map_insert[simp]:
  "rawoutput_h5_map (channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_eve1_output_val_pattern), (channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h5_map_def)

interpretation RawOutput_h5:
    sbUnionGen "def_SecureProtocol_HLR2_eve1_Output.buildSB"
               "RawOutput_h4.constructor"
               "rawoutput_h5_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h5_map_def)+
    by(intro cont2cont)?

definition rawoutput_h6_map ::
  "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h6_map \<equiv>
  \<lambda> (channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_encrypt1_output_val_pattern), (channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h6_map_insert[simp]:
  "rawoutput_h6_map (channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_encrypt1_output_val_pattern), (channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h6_map_def)

interpretation RawOutput_h6:
    sbUnionGen "def_SecureProtocol_HLR2_encrypt1_Output.buildSB"
               "RawOutput_h5.constructor"
               "rawoutput_h6_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h6_map_def)+
    by(intro cont2cont)?

definition rawoutput_h7_map ::
  "(Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((Data_Bool_Tuple tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_h7_map \<equiv>
  \<lambda> (channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_alice_output_val_pattern), (channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_h7_map_insert[simp]:
  "rawoutput_h7_map (channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_alice_output_val_pattern), (channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_h7_map_def)

interpretation RawOutput_h7:
    sbUnionGen "def_SecureProtocol_HLR2_alice_Output.buildSB"
               "RawOutput_h6.constructor"
               "rawoutput_h7_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h7_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream) \<Rightarrow>
  ((bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream) \<times> (Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern) .
  ((channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern), (channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = ((channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern), (channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.buildSB"
               "RawOutput_h7.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_SecureProtocol_HLR2_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2alice \<equiv> (fst o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2alice \<equiv> (fst o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation alice_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_alice_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2alice"
  apply(rule subsetgen_transitive)
  using RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation alice_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_alice_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2alice"
  apply(rule subsetgen_transitive)
  using RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2encrypt1 \<equiv> (fst o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2encrypt1 \<equiv> (fst o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation encrypt1_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_encrypt1_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2encrypt1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation encrypt1_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_encrypt1_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2encrypt1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2eve1 \<equiv> (fst o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2eve1 \<equiv> (fst o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation eve1_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_eve1_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2eve1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation eve1_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_eve1_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2eve1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2decrypt1 \<equiv> (fst o rawinput_h4_map) o (snd o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2decrypt1 \<equiv> (fst o rawoutput_h4_map) o (snd o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation decrypt1_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_decrypt1_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2decrypt1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation decrypt1_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_decrypt1_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2decrypt1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2bob \<equiv> (fst o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2bob \<equiv> (fst o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation bob_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_bob_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2bob"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation bob_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_bob_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2bob"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2encrypt2 \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2encrypt2 \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation encrypt2_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_encrypt2_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2encrypt2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation encrypt2_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_encrypt2_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2encrypt2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2eve2 \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2eve2 \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation eve2_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_eve2_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2eve2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation eve2_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_eve2_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2eve2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_SecureProtocol_HLR2_rawinput2decrypt2 \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_h4_map) o (snd o rawinput_h5_map) o (snd o rawinput_h6_map) o (snd o rawinput_h7_map) o (snd o rawinput_map)"

abbreviation "def_SecureProtocol_HLR2_rawoutput2decrypt2 \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_h4_map) o (snd o rawoutput_h5_map) o (snd o rawoutput_h6_map) o (snd o rawoutput_h7_map) o (snd o rawoutput_map)"

interpretation decrypt2_input_Sub:
    subsetGen "RawInput.constructor" "def_SecureProtocol_HLR2_decrypt2_Input.buildSB" "def_SecureProtocol_HLR2_rawinput2decrypt2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput_h4.subset_fst RawInput_h4.subset_snd
        RawInput_h5.subset_fst RawInput_h5.subset_snd
        RawInput_h6.subset_fst RawInput_h6.subset_snd
        RawInput_h7.subset_fst RawInput_h7.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation decrypt2_output_Sub:
    subsetGen "RawOutput.constructor" "def_SecureProtocol_HLR2_decrypt2_Output.buildSB" "def_SecureProtocol_HLR2_rawoutput2decrypt2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput_h4.subset_fst RawOutput_h4.subset_snd
        RawOutput_h5.subset_fst RawOutput_h5.subset_snd
        RawOutput_h6.subset_fst RawOutput_h6.subset_snd
        RawOutput_h7.subset_fst RawOutput_h7.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_SecureProtocol_hlr2 ::
    "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)
  \<Rightarrow> (nat tsyn stream)" where
"rawinput2def_SecureProtocol_hlr2
    (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern, channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = (channel_input_val_pattern)"

interpretation def_SecureProtocol_HLR2_input_Sub:
    subsetGen "RawInput.constructor"
              "def_SecureProtocol_HLR1_Input.buildSB"
              "rawinput2def_SecureProtocol_hlr2"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_SecureProtocol_HLR1_Input.buildSB_def
               def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.buildSB_def
               def_SecureProtocol_HLR2_alice_Input.buildSB_def
               def_SecureProtocol_HLR2_encrypt1_Input.buildSB_def
               def_SecureProtocol_HLR2_eve1_Input.buildSB_def
               def_SecureProtocol_HLR2_decrypt1_Input.buildSB_def
               def_SecureProtocol_HLR2_bob_Input.buildSB_def
               def_SecureProtocol_HLR2_encrypt2_Input.buildSB_def
               def_SecureProtocol_HLR2_eve2_Input.buildSB_def
               def_SecureProtocol_HLR2_decrypt2_Input.buildSB_def)+

fun rawoutput2def_SecureProtocol_hlr2 ::
    "(bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)
  \<Rightarrow> (nat tsyn stream)" where
"rawoutput2def_SecureProtocol_hlr2
    (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = (channel_output_val_pattern)"

interpretation def_SecureProtocol_HLR2_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_SecureProtocol_HLR1_Output.buildSB"
              "rawoutput2def_SecureProtocol_hlr2"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_SecureProtocol_HLR1_Output.buildSB_def
               def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.buildSB_def
               def_SecureProtocol_HLR2_alice_Output.buildSB_def
               def_SecureProtocol_HLR2_encrypt1_Output.buildSB_def
               def_SecureProtocol_HLR2_eve1_Output.buildSB_def
               def_SecureProtocol_HLR2_decrypt1_Output.buildSB_def
               def_SecureProtocol_HLR2_bob_Output.buildSB_def
               def_SecureProtocol_HLR2_encrypt2_Output.buildSB_def
               def_SecureProtocol_HLR2_eve2_Output.buildSB_def
               def_SecureProtocol_HLR2_decrypt2_Output.buildSB_def)+


fun rawinput2def_SecureProtocol_hlr2_feedback ::
    "(Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)
  \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)" where
"rawinput2def_SecureProtocol_hlr2_feedback
    (channel_alice_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_decrypt1_output_val_pattern, channel_decrypt2_output_val_pattern, channel_encrypt1_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve1_output_val_pattern, channel_eve2_output_val_pattern, channel_input_val_pattern, channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_encrypt1_input_val_pattern, channel_eve1_input_val_pattern, channel_decrypt1_input_val_pattern, channel_bob_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve2_input_val_pattern, channel_decrypt2_input_val_pattern)
  = (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_SecureProtocol_HLR2_Feedback.buildSB"
              "rawinput2def_SecureProtocol_hlr2_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_SecureProtocol_HLR2_Feedback.buildSB_def
               def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.buildSB_def
               def_SecureProtocol_HLR2_alice_Input.buildSB_def
               def_SecureProtocol_HLR2_encrypt1_Input.buildSB_def
               def_SecureProtocol_HLR2_eve1_Input.buildSB_def
               def_SecureProtocol_HLR2_decrypt1_Input.buildSB_def
               def_SecureProtocol_HLR2_bob_Input.buildSB_def
               def_SecureProtocol_HLR2_encrypt2_Input.buildSB_def
               def_SecureProtocol_HLR2_eve2_Input.buildSB_def
               def_SecureProtocol_HLR2_decrypt2_Input.buildSB_def)+

fun rawoutput2def_SecureProtocol_hlr2_feedback ::
    "(bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)
  \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> Data_Bool_Tuple tsyn stream \<times> bool tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream \<times> bool tsyn stream)" where
"rawoutput2def_SecureProtocol_hlr2_feedback
    (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_output_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)
  = (channel_alice_control_val_pattern, channel_alice_input_val_pattern, channel_bob_input_val_pattern, channel_decrypt1_input_val_pattern, channel_decrypt2_input_val_pattern, channel_encrypt1_input_val_pattern, channel_encrypt2_input_val_pattern, channel_eve1_input_val_pattern, channel_eve2_input_val_pattern, channel_alice_output_val_pattern, channel_encrypt1_output_val_pattern, channel_eve1_output_val_pattern, channel_decrypt1_output_val_pattern, channel_bob_control_val_pattern, channel_bob_output_val_pattern, channel_encrypt2_output_val_pattern, channel_eve2_output_val_pattern, channel_decrypt2_output_val_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_SecureProtocol_HLR2_Feedback.buildSB"
              "rawoutput2def_SecureProtocol_hlr2_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_SecureProtocol_HLR2_Feedback.buildSB_def
               def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.buildSB_def
               def_SecureProtocol_HLR2_alice_Output.buildSB_def
               def_SecureProtocol_HLR2_encrypt1_Output.buildSB_def
               def_SecureProtocol_HLR2_eve1_Output.buildSB_def
               def_SecureProtocol_HLR2_decrypt1_Output.buildSB_def
               def_SecureProtocol_HLR2_bob_Output.buildSB_def
               def_SecureProtocol_HLR2_encrypt2_Output.buildSB_def
               def_SecureProtocol_HLR2_eve2_Output.buildSB_def
               def_SecureProtocol_HLR2_decrypt2_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channels \<union> (def_SecureProtocol_HLR2_alice_Input.channels \<union> (def_SecureProtocol_HLR2_encrypt1_Input.channels \<union> (def_SecureProtocol_HLR2_eve1_Input.channels \<union> (def_SecureProtocol_HLR2_decrypt1_Input.channels \<union> (def_SecureProtocol_HLR2_bob_Input.channels \<union> (def_SecureProtocol_HLR2_encrypt2_Input.channels \<union> (def_SecureProtocol_HLR2_eve2_Input.channels \<union> def_SecureProtocol_HLR2_decrypt2_Input.channels) - def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels \<union> def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels \<union> def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_SecureProtocol_HLR2_connector.Sps () \<Otimes> def_SecureProtocol_HLR2_alice.Sps () \<Otimes> def_SecureProtocol_HLR2_encrypt1.Sps () \<Otimes> def_SecureProtocol_HLR2_eve1.Sps () \<Otimes> def_SecureProtocol_HLR2_decrypt1.Sps () \<Otimes> def_SecureProtocol_HLR2_bob.Sps () \<Otimes> def_SecureProtocol_HLR2_encrypt2.Sps () \<Otimes> def_SecureProtocol_HLR2_eve2.Sps () \<Otimes> def_SecureProtocol_HLR2_decrypt2.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_SecureProtocol_HLR1_Input.channels) = chDom TYPE(((def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channels \<union> (def_SecureProtocol_HLR2_alice_Input.channels \<union> (def_SecureProtocol_HLR2_encrypt1_Input.channels \<union> (def_SecureProtocol_HLR2_eve1_Input.channels \<union> (def_SecureProtocol_HLR2_decrypt1_Input.channels \<union> (def_SecureProtocol_HLR2_bob_Input.channels \<union> (def_SecureProtocol_HLR2_encrypt2_Input.channels \<union> (def_SecureProtocol_HLR2_eve2_Input.channels \<union> def_SecureProtocol_HLR2_decrypt2_Input.channels) - def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels) - def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels \<union> def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_SecureProtocol_HLR1_Output.channels) \<subseteq> chDom TYPE((def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels \<union> def_SecureProtocol_HLR2_alice_Output.channels \<union> def_SecureProtocol_HLR2_encrypt1_Output.channels \<union> def_SecureProtocol_HLR2_eve1_Output.channels \<union> def_SecureProtocol_HLR2_decrypt1_Output.channels \<union> def_SecureProtocol_HLR2_bob_Output.channels \<union> def_SecureProtocol_HLR2_encrypt2_Output.channels \<union> def_SecureProtocol_HLR2_eve2_Output.channels \<union> def_SecureProtocol_HLR2_decrypt2_Output.channels))"
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


lemma alice_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma alice_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma encrypt1_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma encrypt1_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma eve1_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma eve1_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma decrypt1_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma decrypt1_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma bob_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma bob_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma encrypt2_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma encrypt2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma eve2_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma eve2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma decrypt2_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((((((((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma decrypt2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((((((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma alice_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Alice_HLR.Sps () \<Longrightarrow> P (def_Alice_HLR_Input.SB.getter\<cdot>sb) (def_Alice_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_alice_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst alice_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst alice_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_alice.pred_inst2def assms: assms)
 

lemma encrypt1_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Encrypt1_HLR.Sps () \<Longrightarrow> P (def_Encrypt1_HLR_Input.SB.getter\<cdot>sb) (def_Encrypt1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_encrypt1_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_encrypt1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst encrypt1_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst encrypt1_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_encrypt1.pred_inst2def assms: assms)
 

lemma eve1_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Eve1_HLR.Sps () \<Longrightarrow> P (def_Eve1_HLR_Input.SB.getter\<cdot>sb) (def_Eve1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_eve1_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_eve1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst eve1_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst eve1_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_eve1.pred_inst2def assms: assms)
 

lemma decrypt1_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Decrypt1_HLR.Sps () \<Longrightarrow> P (def_Decrypt1_HLR_Input.SB.getter\<cdot>sb) (def_Decrypt1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_decrypt1_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_decrypt1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst decrypt1_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst decrypt1_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_decrypt1.pred_inst2def assms: assms)
 

lemma bob_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Bob_HLR.Sps () \<Longrightarrow> P (def_Bob_HLR_Input.SB.getter\<cdot>sb) (def_Bob_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_bob_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_bob_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst bob_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst bob_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_bob.pred_inst2def assms: assms)
 

lemma encrypt2_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Encrypt2_HLR.Sps () \<Longrightarrow> P (def_Encrypt2_HLR_Input.SB.getter\<cdot>sb) (def_Encrypt2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_encrypt2_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_encrypt2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst encrypt2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst encrypt2_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_encrypt2.pred_inst2def assms: assms)
 

lemma eve2_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Eve2_HLR.Sps () \<Longrightarrow> P (def_Eve2_HLR_Input.SB.getter\<cdot>sb) (def_Eve2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_eve2_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_eve2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst eve2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst eve2_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_eve2.pred_inst2def assms: assms)
 

lemma decrypt2_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Decrypt2_HLR.Sps () \<Longrightarrow> P (def_Decrypt2_HLR_Input.SB.getter\<cdot>sb) (def_Decrypt2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_SecureProtocol_HLR2_decrypt2_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_SecureProtocol_HLR2_decrypt2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst decrypt2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst decrypt2_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_SecureProtocol_HLR2_decrypt2.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_SecureProtocol_HLR2_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_SecureProtocol_HLR2_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_SecureProtocol_HLR2_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
