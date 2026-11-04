theory def_DLDF_HLR3
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_DLDF_HLR1.def_DLDF_HLR1_Input bundle_DLDF_HLR1.def_DLDF_HLR1_Output sps_DLDF_HLR3_connector.def_DLDF_HLR3_connector sps_DLDF_HLR3_scheduler1.def_DLDF_HLR3_scheduler1 sps_DLDF_HLR3_scheduler2.def_DLDF_HLR3_scheduler2 sps_DLDF_HLR3_scheduler3.def_DLDF_HLR3_scheduler3 sps_DLDF_HLR3_scheduler4.def_DLDF_HLR3_scheduler4 bundle_DLDF_HLR3.def_DLDF_HLR3_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern) .
    ((channel_scheduler3_input_data_pattern), (channel_scheduler4_input_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = ((channel_scheduler3_input_data_pattern), (channel_scheduler4_input_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_DLDF_HLR3_scheduler3_Input.buildSB"
               "def_DLDF_HLR3_scheduler4_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_h2_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream))" where
"rawinput_h2_map \<equiv>
    \<lambda> (channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern) .
    ((channel_scheduler2_input_data_pattern), (channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"

lemma rawinput_h2_map_insert[simp]:
    "rawinput_h2_map (channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = ((channel_scheduler2_input_data_pattern), (channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"
  by(simp add: rawinput_h2_map_def)

interpretation RawInput_h2:
    sbUnionGen "def_DLDF_HLR3_scheduler2_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h2_map_def)+
    by(intro cont2cont)?

definition rawinput_h3_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h3_map \<equiv>
    \<lambda> (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern) .
    ((channel_scheduler1_input_data_pattern), (channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"

lemma rawinput_h3_map_insert[simp]:
    "rawinput_h3_map (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = ((channel_scheduler1_input_data_pattern), (channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"
  by(simp add: rawinput_h3_map_def)

interpretation RawInput_h3:
    sbUnionGen "def_DLDF_HLR3_scheduler1_Input.buildSB"
               "RawInput_h2.constructor"
               "rawinput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h3_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern) .
    ((channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern), (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = ((channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern), (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.buildSB"
               "RawInput_h3.constructor"
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
  \<lambda> (channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern) .
  ((channel_scheduler3_output_data_pattern), (channel_scheduler4_output_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = ((channel_scheduler3_output_data_pattern), (channel_scheduler4_output_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_DLDF_HLR3_scheduler3_Output.buildSB"
               "def_DLDF_HLR3_scheduler4_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_h2_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream))" where
"rawoutput_h2_map \<equiv>
  \<lambda> (channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern) .
  ((channel_scheduler2_output_data_pattern), (channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"

lemma rawoutput_h2_map_insert[simp]:
  "rawoutput_h2_map (channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = ((channel_scheduler2_output_data_pattern), (channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"
  by(simp add: rawoutput_h2_map_def)

interpretation RawOutput_h2:
    sbUnionGen "def_DLDF_HLR3_scheduler2_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_h2_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h2_map_def)+
    by(intro cont2cont)?

definition rawoutput_h3_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_h3_map \<equiv>
  \<lambda> (channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern) .
  ((channel_scheduler1_output_data_pattern), (channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"

lemma rawoutput_h3_map_insert[simp]:
  "rawoutput_h3_map (channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = ((channel_scheduler1_output_data_pattern), (channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"
  by(simp add: rawoutput_h3_map_def)

interpretation RawOutput_h3:
    sbUnionGen "def_DLDF_HLR3_scheduler1_Output.buildSB"
               "RawOutput_h2.constructor"
               "rawoutput_h3_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h3_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern) .
  ((channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern), (channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = ((channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern), (channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.buildSB"
               "RawOutput_h3.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_DLDF_HLR3_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_DLDF_HLR3_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.buildSB" "def_DLDF_HLR3_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.buildSB" "def_DLDF_HLR3_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_DLDF_HLR3_rawinput2scheduler1 \<equiv> (fst o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_DLDF_HLR3_rawoutput2scheduler1 \<equiv> (fst o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation scheduler1_input_Sub:
    subsetGen "RawInput.constructor" "def_DLDF_HLR3_scheduler1_Input.buildSB" "def_DLDF_HLR3_rawinput2scheduler1"
  apply(rule subsetgen_transitive)
  using RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation scheduler1_output_Sub:
    subsetGen "RawOutput.constructor" "def_DLDF_HLR3_scheduler1_Output.buildSB" "def_DLDF_HLR3_rawoutput2scheduler1"
  apply(rule subsetgen_transitive)
  using RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_DLDF_HLR3_rawinput2scheduler2 \<equiv> (fst o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_DLDF_HLR3_rawoutput2scheduler2 \<equiv> (fst o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation scheduler2_input_Sub:
    subsetGen "RawInput.constructor" "def_DLDF_HLR3_scheduler2_Input.buildSB" "def_DLDF_HLR3_rawinput2scheduler2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation scheduler2_output_Sub:
    subsetGen "RawOutput.constructor" "def_DLDF_HLR3_scheduler2_Output.buildSB" "def_DLDF_HLR3_rawoutput2scheduler2"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_DLDF_HLR3_rawinput2scheduler3 \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_DLDF_HLR3_rawoutput2scheduler3 \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation scheduler3_input_Sub:
    subsetGen "RawInput.constructor" "def_DLDF_HLR3_scheduler3_Input.buildSB" "def_DLDF_HLR3_rawinput2scheduler3"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation scheduler3_output_Sub:
    subsetGen "RawOutput.constructor" "def_DLDF_HLR3_scheduler3_Output.buildSB" "def_DLDF_HLR3_rawoutput2scheduler3"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_DLDF_HLR3_rawinput2scheduler4 \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_h2_map) o (snd o rawinput_h3_map) o (snd o rawinput_map)"

abbreviation "def_DLDF_HLR3_rawoutput2scheduler4 \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_h2_map) o (snd o rawoutput_h3_map) o (snd o rawoutput_map)"

interpretation scheduler4_input_Sub:
    subsetGen "RawInput.constructor" "def_DLDF_HLR3_scheduler4_Input.buildSB" "def_DLDF_HLR3_rawinput2scheduler4"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput_h2.subset_fst RawInput_h2.subset_snd
        RawInput_h3.subset_fst RawInput_h3.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation scheduler4_output_Sub:
    subsetGen "RawOutput.constructor" "def_DLDF_HLR3_scheduler4_Output.buildSB" "def_DLDF_HLR3_rawoutput2scheduler4"
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput_h2.subset_fst RawOutput_h2.subset_snd
        RawOutput_h3.subset_fst RawOutput_h3.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_dldf_hlr3 ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_dldf_hlr3
    (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern)"

interpretation def_DLDF_HLR3_input_Sub:
    subsetGen "RawInput.constructor"
              "def_DLDF_HLR1_Input.buildSB"
              "rawinput2def_dldf_hlr3"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_DLDF_HLR1_Input.buildSB_def
               def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.buildSB_def
               def_DLDF_HLR3_scheduler1_Input.buildSB_def
               def_DLDF_HLR3_scheduler2_Input.buildSB_def
               def_DLDF_HLR3_scheduler3_Input.buildSB_def
               def_DLDF_HLR3_scheduler4_Input.buildSB_def)+

fun rawoutput2def_dldf_hlr3 ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_dldf_hlr3
    (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"

interpretation def_DLDF_HLR3_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_DLDF_HLR1_Output.buildSB"
              "rawoutput2def_dldf_hlr3"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_DLDF_HLR1_Output.buildSB_def
               def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.buildSB_def
               def_DLDF_HLR3_scheduler1_Output.buildSB_def
               def_DLDF_HLR3_scheduler2_Output.buildSB_def
               def_DLDF_HLR3_scheduler3_Output.buildSB_def
               def_DLDF_HLR3_scheduler4_Output.buildSB_def)+


fun rawinput2def_dldf_hlr3_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_dldf_hlr3_feedback
    (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern)
  = (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_DLDF_HLR3_Feedback.buildSB"
              "rawinput2def_dldf_hlr3_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_DLDF_HLR3_Feedback.buildSB_def
               def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.buildSB_def
               def_DLDF_HLR3_scheduler1_Input.buildSB_def
               def_DLDF_HLR3_scheduler2_Input.buildSB_def
               def_DLDF_HLR3_scheduler3_Input.buildSB_def
               def_DLDF_HLR3_scheduler4_Input.buildSB_def)+

fun rawoutput2def_dldf_hlr3_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_dldf_hlr3_feedback
    (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern, channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)
  = (channel_scheduler1_input_data_pattern, channel_scheduler2_input_data_pattern, channel_scheduler3_input_data_pattern, channel_scheduler4_input_data_pattern, channel_scheduler1_output_data_pattern, channel_scheduler2_output_data_pattern, channel_scheduler3_output_data_pattern, channel_scheduler4_output_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_DLDF_HLR3_Feedback.buildSB"
              "rawoutput2def_dldf_hlr3_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_DLDF_HLR3_Feedback.buildSB_def
               def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.buildSB_def
               def_DLDF_HLR3_scheduler1_Output.buildSB_def
               def_DLDF_HLR3_scheduler2_Output.buildSB_def
               def_DLDF_HLR3_scheduler3_Output.buildSB_def
               def_DLDF_HLR3_scheduler4_Output.buildSB_def)+




definition rawSps :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (((def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.channels \<union> (def_DLDF_HLR3_scheduler1_Input.channels \<union> (def_DLDF_HLR3_scheduler2_Input.channels \<union> (def_DLDF_HLR3_scheduler3_Input.channels \<union> def_DLDF_HLR3_scheduler4_Input.channels) - def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.channels \<union> def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.channels \<union> def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4). def_DLDF_HLR3_connector.Sps () \<Otimes> def_DLDF_HLR3_scheduler1.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<Otimes> def_DLDF_HLR3_scheduler2.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<Otimes> def_DLDF_HLR3_scheduler3.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<Otimes> def_DLDF_HLR3_scheduler4.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_DLDF_HLR1_Input.channels) = chDom TYPE(((def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.channels \<union> (def_DLDF_HLR3_scheduler1_Input.channels \<union> (def_DLDF_HLR3_scheduler2_Input.channels \<union> (def_DLDF_HLR3_scheduler3_Input.channels \<union> def_DLDF_HLR3_scheduler4_Input.channels) - def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels) - def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.channels \<union> def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_DLDF_HLR1_Output.channels) \<subseteq> chDom TYPE((def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.channels \<union> def_DLDF_HLR3_scheduler1_Output.channels \<union> def_DLDF_HLR3_scheduler2_Output.channels \<union> def_DLDF_HLR3_scheduler3_Output.channels \<union> def_DLDF_HLR3_scheduler4_Output.channels))"
  by auto


declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]



lemma connector_input_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma connector_output_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(spf\<cdot>sb)\<star> = ((spf\<cdot>sb)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma scheduler1_input_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma scheduler1_output_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma scheduler2_input_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
     shows "((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma scheduler2_output_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(spf\<cdot>sb)\<star> = ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma scheduler3_input_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
     shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma scheduler3_output_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma scheduler4_input_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "((((((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) \<uplus>\<^sub>- ((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma scheduler4_output_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(spf\<cdot>sb)\<star> = (((((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma scheduler1_pred_general:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
      and "\<And>sb spf. spf \<in> def_Scheduler_HLR3.Sps (var_cap1) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_DLDF_HLR3_scheduler1_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_DLDF_HLR3_scheduler1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst scheduler1_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst scheduler1_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_DLDF_HLR3_scheduler1.pred_inst2def assms: assms)
 

lemma scheduler2_pred_general:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
      and "\<And>sb spf. spf \<in> def_Scheduler_HLR3.Sps (var_cap2) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_DLDF_HLR3_scheduler2_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_DLDF_HLR3_scheduler2_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst scheduler2_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst scheduler2_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_DLDF_HLR3_scheduler2.pred_inst2def assms: assms)
 

lemma scheduler3_pred_general:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
      and "\<And>sb spf. spf \<in> def_Scheduler_HLR3.Sps (var_cap3) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_DLDF_HLR3_scheduler3_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_DLDF_HLR3_scheduler3_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst scheduler3_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst scheduler3_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_DLDF_HLR3_scheduler3.pred_inst2def assms: assms)
 

lemma scheduler4_pred_general:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
      and "\<And>sb spf. spf \<in> def_Scheduler_HLR3.Sps (var_cap4) \<Longrightarrow> P (def_Scheduler_HLR2_Input.SB.getter\<cdot>sb) (def_Scheduler_HLR2_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_DLDF_HLR3_scheduler4_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_DLDF_HLR3_scheduler4_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst scheduler4_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst scheduler4_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_DLDF_HLR3_scheduler4.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "def_DLDF_HLR3_connector.connector\<cdot>(def_DLDF_HLR3_connector_DLDF_HLR3_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_DLDF_HLR3_connector_DLDF_HLR3_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_DLDF_HLR3_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4))"
    shows "(def_DLDF_HLR3_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_DLDF_HLR3_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "(nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (def_DLDF_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_DLDF_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_cap1, var_cap2, var_cap3, var_cap4). spsConvert \<cdot> (rawSps (var_cap1, var_cap2, var_cap3, var_cap4)) "

declare len_prod_inf_snd[simp]


end
