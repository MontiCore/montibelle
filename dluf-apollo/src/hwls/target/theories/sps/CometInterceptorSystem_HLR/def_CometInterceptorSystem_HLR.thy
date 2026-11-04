theory def_CometInterceptorSystem_HLR
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_CometInterceptorSystem_HLR.def_CometInterceptorSystem_HLR_Input bundle_CometInterceptorSystem_HLR.def_CometInterceptorSystem_HLR_Output sps_CometInterceptorSystem_HLR_connector.def_CometInterceptorSystem_HLR_connector sps_CometInterceptorSystem_HLR_spacecrafta.def_CometInterceptorSystem_HLR_spacecrafta sps_CometInterceptorSystem_HLR_b1.def_CometInterceptorSystem_HLR_b1 sps_CometInterceptorSystem_HLR_b2.def_CometInterceptorSystem_HLR_b2 bundle_CometInterceptorSystem_HLR.def_CometInterceptorSystem_HLR_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_b1_input_data_pattern, channel_b2_input_data_pattern) .
    ((channel_b1_input_data_pattern), (channel_b2_input_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_b1_input_data_pattern, channel_b2_input_data_pattern)
  = ((channel_b1_input_data_pattern), (channel_b2_input_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_CometInterceptorSystem_HLR_b1_Input.buildSB"
               "def_CometInterceptorSystem_HLR_b2_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_h2_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern) .
    ((channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern), (channel_b1_input_data_pattern, channel_b2_input_data_pattern))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern)
  = ((channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern), (channel_b1_input_data_pattern, channel_b2_input_data_pattern))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "def_CometInterceptorSystem_HLR_spacecrafta_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h2_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern) .
    ((channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern), (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern)
  = ((channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern), (channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_b1_output_data_pattern, channel_b2_output_data_pattern) .
  ((channel_b1_output_data_pattern), (channel_b2_output_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_b1_output_data_pattern, channel_b2_output_data_pattern)
  = ((channel_b1_output_data_pattern), (channel_b2_output_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_CometInterceptorSystem_HLR_b1_Output.buildSB"
               "def_CometInterceptorSystem_HLR_b2_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_h2_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern) .
  ((channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern), (channel_b1_output_data_pattern, channel_b2_output_data_pattern))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)
  = ((channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern), (channel_b1_output_data_pattern, channel_b2_output_data_pattern))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "def_CometInterceptorSystem_HLR_spacecrafta_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h2_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern) .
  ((channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern), (channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)
  = ((channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern), (channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_CometInterceptorSystem_HLR_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_CometInterceptorSystem_HLR_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.buildSB" "def_CometInterceptorSystem_HLR_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.buildSB" "def_CometInterceptorSystem_HLR_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_CometInterceptorSystem_HLR_rawinput2spacecrafta \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "def_CometInterceptorSystem_HLR_rawoutput2spacecrafta \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation spacecrafta_input_Sub:
    subsetGen "RawInput.constructor" "def_CometInterceptorSystem_HLR_spacecrafta_Input.buildSB" "def_CometInterceptorSystem_HLR_rawinput2spacecrafta"
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation spacecrafta_output_Sub:
    subsetGen "RawOutput.constructor" "def_CometInterceptorSystem_HLR_spacecrafta_Output.buildSB" "def_CometInterceptorSystem_HLR_rawoutput2spacecrafta"
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_CometInterceptorSystem_HLR_rawinput2b1 \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "def_CometInterceptorSystem_HLR_rawoutput2b1 \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation b1_input_Sub:
    subsetGen "RawInput.constructor" "def_CometInterceptorSystem_HLR_b1_Input.buildSB" "def_CometInterceptorSystem_HLR_rawinput2b1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation b1_output_Sub:
    subsetGen "RawOutput.constructor" "def_CometInterceptorSystem_HLR_b1_Output.buildSB" "def_CometInterceptorSystem_HLR_rawoutput2b1"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_CometInterceptorSystem_HLR_rawinput2b2 \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_map)"

abbreviation "def_CometInterceptorSystem_HLR_rawoutput2b2 \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_map)"

interpretation b2_input_Sub:
    subsetGen "RawInput.constructor" "def_CometInterceptorSystem_HLR_b2_Input.buildSB" "def_CometInterceptorSystem_HLR_rawinput2b2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation b2_output_Sub:
    subsetGen "RawOutput.constructor" "def_CometInterceptorSystem_HLR_b2_Output.buildSB" "def_CometInterceptorSystem_HLR_rawoutput2b2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_cometinterceptorsystem_hlr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream)" where
"rawinput2def_cometinterceptorsystem_hlr
    (channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern)
  = (channel_groundIn_data_pattern)"

interpretation def_CometInterceptorSystem_HLR_input_Sub:
    subsetGen "RawInput.constructor"
              "def_CometInterceptorSystem_HLR_Input.buildSB"
              "rawinput2def_cometinterceptorsystem_hlr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_CometInterceptorSystem_HLR_Input.buildSB_def
               def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.buildSB_def
               def_CometInterceptorSystem_HLR_spacecrafta_Input.buildSB_def
               def_CometInterceptorSystem_HLR_b1_Input.buildSB_def
               def_CometInterceptorSystem_HLR_b2_Input.buildSB_def)+

fun rawoutput2def_cometinterceptorsystem_hlr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream)" where
"rawoutput2def_cometinterceptorsystem_hlr
    (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)
  = (channel_groundOut_data_pattern)"

interpretation def_CometInterceptorSystem_HLR_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_CometInterceptorSystem_HLR_Output.buildSB"
              "rawoutput2def_cometinterceptorsystem_hlr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_CometInterceptorSystem_HLR_Output.buildSB_def
               def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.buildSB_def
               def_CometInterceptorSystem_HLR_spacecrafta_Output.buildSB_def
               def_CometInterceptorSystem_HLR_b1_Output.buildSB_def
               def_CometInterceptorSystem_HLR_b2_Output.buildSB_def)+


fun rawinput2def_cometinterceptorsystem_hlr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_cometinterceptorsystem_hlr_feedback
    (channel_b1_output_data_pattern, channel_b2_output_data_pattern, channel_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_b1_input_data_pattern, channel_b2_input_data_pattern)
  = (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_CometInterceptorSystem_HLR_Feedback.buildSB"
              "rawinput2def_cometinterceptorsystem_hlr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_CometInterceptorSystem_HLR_Feedback.buildSB_def
               def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.buildSB_def
               def_CometInterceptorSystem_HLR_spacecrafta_Input.buildSB_def
               def_CometInterceptorSystem_HLR_b1_Input.buildSB_def
               def_CometInterceptorSystem_HLR_b2_Input.buildSB_def)+

fun rawoutput2def_cometinterceptorsystem_hlr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_cometinterceptorsystem_hlr_feedback
    (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_groundOut_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)
  = (channel_b1_input_data_pattern, channel_b2_input_data_pattern, channel_spacecrafta_b1In_data_pattern, channel_spacecrafta_b2In_data_pattern, channel_spacecrafta_groundIn_data_pattern, channel_spacecrafta_b1Out_data_pattern, channel_spacecrafta_b2Out_data_pattern, channel_spacecrafta_groundOut_data_pattern, channel_b1_output_data_pattern, channel_b2_output_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_CometInterceptorSystem_HLR_Feedback.buildSB"
              "rawoutput2def_cometinterceptorsystem_hlr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_CometInterceptorSystem_HLR_Feedback.buildSB_def
               def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.buildSB_def
               def_CometInterceptorSystem_HLR_spacecrafta_Output.buildSB_def
               def_CometInterceptorSystem_HLR_b1_Output.buildSB_def
               def_CometInterceptorSystem_HLR_b2_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.channels \<union> (def_CometInterceptorSystem_HLR_spacecrafta_Input.channels \<union> (def_CometInterceptorSystem_HLR_b1_Input.channels \<union> def_CometInterceptorSystem_HLR_b2_Input.channels) - def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels) - def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels) - def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.channels \<union> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.channels \<union> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_CometInterceptorSystem_HLR_connector.Sps () \<Otimes> def_CometInterceptorSystem_HLR_spacecrafta.Sps () \<Otimes> def_CometInterceptorSystem_HLR_b1.Sps () \<Otimes> def_CometInterceptorSystem_HLR_b2.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_CometInterceptorSystem_HLR_Input.channels) = chDom TYPE(((def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.channels \<union> (def_CometInterceptorSystem_HLR_spacecrafta_Input.channels \<union> (def_CometInterceptorSystem_HLR_b1_Input.channels \<union> def_CometInterceptorSystem_HLR_b2_Input.channels) - def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels) - def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels) - def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.channels \<union> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_CometInterceptorSystem_HLR_Output.channels) \<subseteq> chDom TYPE((def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.channels \<union> def_CometInterceptorSystem_HLR_spacecrafta_Output.channels \<union> def_CometInterceptorSystem_HLR_b1_Output.channels \<union> def_CometInterceptorSystem_HLR_b2_Output.channels))"
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


lemma spacecrafta_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma spacecrafta_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma b1_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma b1_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma b2_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma b2_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma spacecrafta_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_SpacecraftA_HLR.Sps () \<Longrightarrow> P (def_SpacecraftA_HLR_Input.SB.getter\<cdot>sb) (def_SpacecraftA_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_CometInterceptorSystem_HLR_spacecrafta_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_CometInterceptorSystem_HLR_spacecrafta_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst spacecrafta_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst spacecrafta_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_CometInterceptorSystem_HLR_spacecrafta.pred_inst2def assms: assms)
 

lemma b1_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_ProbeB1.Sps () \<Longrightarrow> P (def_ProbeB1_Input.SB.getter\<cdot>sb) (def_ProbeB1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_CometInterceptorSystem_HLR_b1_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_CometInterceptorSystem_HLR_b1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst b1_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst b1_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_CometInterceptorSystem_HLR_b1.pred_inst2def assms: assms)
 

lemma b2_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_ProbeB2.Sps () \<Longrightarrow> P (def_ProbeB2_Input.SB.getter\<cdot>sb) (def_ProbeB2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_CometInterceptorSystem_HLR_b2_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_CometInterceptorSystem_HLR_b2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst b2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst b2_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_CometInterceptorSystem_HLR_b2.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_CometInterceptorSystem_HLR_connector.connector\<cdot>(def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_CometInterceptorSystem_HLR_connector_CometInterceptorSystem_HLR_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_CometInterceptorSystem_HLR_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_CometInterceptorSystem_HLR_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_CometInterceptorSystem_HLR_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_CometInterceptorSystem_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_CometInterceptorSystem_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
