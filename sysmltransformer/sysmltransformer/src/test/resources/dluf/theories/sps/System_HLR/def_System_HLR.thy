theory def_System_HLR
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) bundle_System_HLR.def_System_HLR_Input bundle_System_HLR.def_System_HLR_Output sps_System_HLR_connector.def_System_HLR_connector sps_System_HLR_dluf.def_System_HLR_dluf sps_System_HLR_mergex.def_System_HLR_mergex bundle_System_HLR.def_System_HLR_Feedback
    (* Hwl  *)

begin


declare len_prod_inf_snd[simp del]



definition rawinput_h1_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_h1_map \<equiv>
    \<lambda> (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern) .
    ((channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern), (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern))"

lemma rawinput_h1_map_insert[simp]:
    "rawinput_h1_map (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern)
  = ((channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern), (channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern))"
  by(simp add: rawinput_h1_map_def)

interpretation RawInput_h1:
    sbUnionGen "def_System_HLR_dluf_Input.buildSB"
               "def_System_HLR_mergex_Input.buildSB"
               "rawinput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_h1_map_def)+
    by(intro cont2cont)?

definition rawinput_map ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
    ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawinput_map \<equiv>
    \<lambda> (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern, channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern) .
    ((channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern), (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern))"

lemma rawinput_map_insert[simp]:
    "rawinput_map (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern, channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern)
  = ((channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern), (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern))"
  by(simp add: rawinput_map_def)

interpretation RawInput:
    sbUnionGen "def_System_HLR_connector_System_HLR_connector_Input.buildSB"
               "RawInput_h1.constructor"
               "rawinput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput_map_def)+
    by(intro cont2cont)?



definition rawoutput_h1_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream))" where
"rawoutput_h1_map \<equiv>
  \<lambda> (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern) .
  ((channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern), (channel_mergex_output_data_pattern))"

lemma rawoutput_h1_map_insert[simp]:
  "rawoutput_h1_map (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)
  = ((channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern), (channel_mergex_output_data_pattern))"
  by(simp add: rawoutput_h1_map_def)

interpretation RawOutput_h1:
    sbUnionGen "def_System_HLR_dluf_Output.buildSB"
               "def_System_HLR_mergex_Output.buildSB"
               "rawoutput_h1_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_h1_map_def)+
    by(intro cont2cont)?

definition rawoutput_map ::
  "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<Rightarrow>
  ((Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream) \<times> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream))" where
"rawoutput_map \<equiv>
  \<lambda> (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern) .
  ((channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern), (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern))"

lemma rawoutput_map_insert[simp]:
  "rawoutput_map (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)
  = ((channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern), (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern))"
  by(simp add: rawoutput_map_def)

interpretation RawOutput:
    sbUnionGen "def_System_HLR_connector_System_HLR_connector_Output.buildSB"
               "RawOutput_h1.constructor"
               "rawoutput_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput_map_def)+
    by(intro cont2cont)?





abbreviation "def_System_HLR_rawinput2connector \<equiv> (fst o rawinput_map)"

abbreviation "def_System_HLR_rawoutput2connector \<equiv> (fst o rawoutput_map)"

interpretation connector_input_Sub:
    subsetGen "RawInput.constructor" "def_System_HLR_connector_System_HLR_connector_Input.buildSB" "def_System_HLR_rawinput2connector"
  using RawInput.subset_fst RawInput.subset_snd by blast+

interpretation connector_output_Sub:
    subsetGen "RawOutput.constructor" "def_System_HLR_connector_System_HLR_connector_Output.buildSB" "def_System_HLR_rawoutput2connector"
  using RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_System_HLR_rawinput2dluf \<equiv> (fst o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "def_System_HLR_rawoutput2dluf \<equiv> (fst o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation dluf_input_Sub:
    subsetGen "RawInput.constructor" "def_System_HLR_dluf_Input.buildSB" "def_System_HLR_rawinput2dluf"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation dluf_output_Sub:
    subsetGen "RawOutput.constructor" "def_System_HLR_dluf_Output.buildSB" "def_System_HLR_rawoutput2dluf"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



abbreviation "def_System_HLR_rawinput2mergex \<equiv> (snd o rawinput_h1_map) o (snd o rawinput_map)"

abbreviation "def_System_HLR_rawoutput2mergex \<equiv> (snd o rawoutput_h1_map) o (snd o rawoutput_map)"

interpretation mergex_input_Sub:
    subsetGen "RawInput.constructor" "def_System_HLR_mergex_Input.buildSB" "def_System_HLR_rawinput2mergex"
  apply(rule subsetgen_transitive)
  using RawInput_h1.subset_fst RawInput_h1.subset_snd
        RawInput.subset_fst RawInput.subset_snd by blast+

interpretation mergex_output_Sub:
    subsetGen "RawOutput.constructor" "def_System_HLR_mergex_Output.buildSB" "def_System_HLR_rawoutput2mergex"
  apply(rule subsetgen_transitive)
  using RawOutput_h1.subset_fst RawOutput_h1.subset_snd
        RawOutput.subset_fst RawOutput.subset_snd by blast+



fun rawinput2def_system_hlr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_system_hlr
    (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern, channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern)
  = (channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern)"

interpretation def_System_HLR_input_Sub:
    subsetGen "RawInput.constructor"
              "def_System_HLR_Input.buildSB"
              "rawinput2def_system_hlr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_System_HLR_Input.buildSB_def
               def_System_HLR_connector_System_HLR_connector_Input.buildSB_def
               def_System_HLR_dluf_Input.buildSB_def
               def_System_HLR_mergex_Input.buildSB_def)+

fun rawoutput2def_system_hlr ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream)" where
"rawoutput2def_system_hlr
    (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)
  = (channel_link_data_pattern)"

interpretation def_System_HLR_output_Sub:
    subsetGen "RawOutput.constructor"
              "def_System_HLR_Output.buildSB"
              "rawoutput2def_system_hlr"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add: def_System_HLR_Output.buildSB_def
               def_System_HLR_connector_System_HLR_connector_Output.buildSB_def
               def_System_HLR_dluf_Output.buildSB_def
               def_System_HLR_mergex_Output.buildSB_def)+


fun rawinput2def_system_hlr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawinput2def_system_hlr_feedback
    (channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern, channel_user1_data_pattern, channel_user2_data_pattern, channel_user3_data_pattern, channel_user4_data_pattern, channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern)
  = (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "def_System_HLR_Feedback.buildSB"
              "rawinput2def_system_hlr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_System_HLR_Feedback.buildSB_def
               def_System_HLR_connector_System_HLR_connector_Input.buildSB_def
               def_System_HLR_dluf_Input.buildSB_def
               def_System_HLR_mergex_Input.buildSB_def)+

fun rawoutput2def_system_hlr_feedback ::
    "(Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)
  \<Rightarrow> (Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream \<times> Packet event stream)" where
"rawoutput2def_system_hlr_feedback
    (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_link_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)
  = (channel_dluf_input1_data_pattern, channel_dluf_input2_data_pattern, channel_dluf_input3_data_pattern, channel_dluf_input4_data_pattern, channel_mergex_input1_data_pattern, channel_mergex_input2_data_pattern, channel_mergex_input3_data_pattern, channel_mergex_input4_data_pattern, channel_dluf_output1_data_pattern, channel_dluf_output2_data_pattern, channel_dluf_output3_data_pattern, channel_dluf_output4_data_pattern, channel_mergex_output_data_pattern)"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "def_System_HLR_Feedback.buildSB"
              "rawoutput2def_system_hlr_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add: def_System_HLR_Feedback.buildSB_def
               def_System_HLR_connector_System_HLR_connector_Output.buildSB_def
               def_System_HLR_dluf_Output.buildSB_def
               def_System_HLR_mergex_Output.buildSB_def)+




definition rawSps :: "unit \<Rightarrow> (((def_System_HLR_connector_System_HLR_connector_Input.channels \<union> (def_System_HLR_dluf_Input.channels \<union> def_System_HLR_mergex_Input.channels) - def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels) - def_System_HLR_connector_System_HLR_connector_Output.channels \<union> def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels)\<^sup>\<Omega> \<rightarrow> (def_System_HLR_connector_System_HLR_connector_Output.channels \<union> def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels)\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> (). def_System_HLR_connector.Sps () \<Otimes> def_System_HLR_dluf.Sps () \<Otimes> def_System_HLR_mergex.Sps ()"



(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (def_System_HLR_Input.channels) = chDom TYPE(((def_System_HLR_connector_System_HLR_connector_Input.channels \<union> (def_System_HLR_dluf_Input.channels \<union> def_System_HLR_mergex_Input.channels) - def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels) - def_System_HLR_connector_System_HLR_connector_Output.channels \<union> def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels))"
  by auto

lemma assert_output_type: "chDom TYPE (def_System_HLR_Output.channels) \<subseteq> chDom TYPE((def_System_HLR_connector_System_HLR_connector_Output.channels \<union> def_System_HLR_dluf_Output.channels \<union> def_System_HLR_mergex_Output.channels))"
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


lemma dluf_input_eq:
  assumes "spf \<in> (rawSps ())"
     shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>1) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma dluf_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>1)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)


lemma mergex_input_eq:
  assumes "spf \<in> (rawSps ())"
    shows "((((sb \<uplus>\<^sub>- spf\<cdot>sb)\<star>\<^sub>2) \<uplus>\<^sub>- ((spf\<cdot>sb)\<star>\<^sub>2))\<star>\<^sub>2) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma mergex_output_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(spf\<cdot>sb)\<star> = (((spf\<cdot>sb)\<star>\<^sub>2)\<star>\<^sub>2)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
 

lemma dluf_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_DLUF_HLR1.Sps (400, 300, 200, 100) \<Longrightarrow> P (def_DLUF_HLR1_Input.SB.getter\<cdot>sb) (def_DLUF_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_System_HLR_dluf_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_System_HLR_dluf_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst dluf_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst dluf_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_System_HLR_dluf.pred_inst2def assms: assms)
 

lemma mergex_pred_general:
  assumes "spf \<in> (rawSps ())"
      and "\<And>sb spf. spf \<in> def_Merge_LLR.Sps () \<Longrightarrow> P (def_Merge_LLR_Input.SB.getter\<cdot>sb) (def_Merge_LLR_Output.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (def_System_HLR_mergex_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) (def_System_HLR_mergex_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst mergex_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst mergex_output_eq[OF assms(1)])
  by(pred_solver inst2def: def_System_HLR_mergex.pred_inst2def assms: assms)

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps ())"
    shows "def_System_HLR_connector.connector\<cdot>(def_System_HLR_connector_System_HLR_connector_Input.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (def_System_HLR_connector_System_HLR_connector_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst connector_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst connector_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: def_System_HLR_connector.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps ())"
    shows "(def_System_HLR_Feedback.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (def_System_HLR_Feedback.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]


definition Sps :: "unit \<Rightarrow> (def_System_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_System_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). spsConvert \<cdot> (rawSps ()) "

declare len_prod_inf_snd[simp]


end
