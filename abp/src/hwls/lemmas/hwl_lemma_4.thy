theory hwl_lemma_4
  imports
    move_to_core.hwl_core_ext

    to_be_generated.hwl_tsynSBlens

    hwl_lemma_1
    hwl_lemma_util

begin


lemma tsynRemDups_smap_Data_Bool_Tuple2tuple:
  "smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>(tsynRemDups\<cdot>s) = 
   tsynRemDups\<cdot>(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s)"
  apply (rule tsynRemDups_smap)
  by (simp add: tsyn.inj_map)+

lemma tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq_Data_Bool_Tuple:
  assumes fin: "#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-y)) < \<infinity>"
      and eq1: "#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-y)) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>y))"
      and eq2: "#\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>y)) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora)))"
    shows "(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-y))\<^sup>-
            = (smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y\<cdot>ora)))\<^sup>-"
proof -
  define y' where "y' = (smap (map_tsyn Data_Bool_Tuple2tuple))\<cdot>y"

  have filter_eq: "(smap (map_tsyn Data_Bool_Tuple2tuple))\<cdot>(tsynBoolFilter\<cdot>y\<cdot>ora) = tsynBoolFilter\<cdot>y'\<cdot>ora"
    by (simp add: smap_tsynBoolFilter y'_def)

  have fin': "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y')) < \<infinity>"
    unfolding y'_def using fin
    by (metis tsynLen_smap_map_tsyn tsynRemDups_smap_Data_Bool_Tuple2tuple tsynprojfst_tsynlen)
  
  have eq1': "#\<^sub>-(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y')) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y'))"
    unfolding y'_def using eq1
    by (simp add: smap_Data_Bool_Tuple_get_fst_def2 smap_Data_Bool_Tuple_get_snd_def2 tsynRemDups_smap_Data_Bool_Tuple2tuple)
  
  have eq2': "#\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-y')) = #\<^sub>-(\<alpha>\<^sub>-(\<Pi>\<^sub>2\<^sub>-(tsynBoolFilter\<cdot>y'\<cdot>ora)))"
    unfolding y'_def
    using eq2 filter_eq smap_Data_Bool_Tuple_get_snd_def2 y'_def
    by auto
  have result: "tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-y')) = tsyn2ustream\<cdot>(\<Pi>\<^sub>1\<^sub>-(\<alpha>\<^sub>-(tsynBoolFilter\<cdot>y'\<cdot>ora)))"
    using fin' eq1' eq2' tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq
    by blast
  
  show ?thesis
    unfolding y'_def using filter_eq result
    by (simp add: smap_Data_Bool_Tuple_get_fst_def2 tsynRemDups_smap_Data_Bool_Tuple2tuple y'_def)
qed

lemma lemma4_streams_1:
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
      and "eve1_input = alice_output" 
      and fin:"#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-alice_output)) < \<infinity> " 
      and eq1:" #\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-alice_output)) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>alice_output))"
      and eq2:"#\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>(alice_output))) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>eve1_output))"
    shows "(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-alice_output))\<^sup>- = (smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-eve1_output))\<^sup>-" 
  apply(insert assms)
  apply(simp add:
      def_SecureProtocol_HLR2_eve1_InputMap.connector_def
      def_SecureProtocol_HLR2_eve1_OutputMap.connector_def)
  apply(simp add: def_Eve1_HLR.wholePredicate_def)
  apply(simp add:
      def_Eve1_HLR.assumption_0_def
      def_Eve1_HLR.predicate_0_def)
  apply auto
  using well_all apply blast
  using tsynprojfst_tsynremdups_tsynbolfilter_id_if_fin_tsynlen_eq_Data_Bool_Tuple fin eq1 eq2
  by blast



definition lemma4_pred where
"lemma4_pred \<equiv> \<lambda> alice_output eve1_output.
  (#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-alice_output)) < \<infinity>
  \<and> #\<^sub>-(((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-alice_output))) = #\<^sub>-(\<alpha>\<^sub>-(((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>alice_output)))
  \<and> #\<^sub>-(\<alpha>\<^sub>-(((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>(alice_output)))) = #\<^sub>-(\<alpha>\<^sub>-(((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>eve1_output)))
) \<longrightarrow>
(tsyn2ustream\<cdot>((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-alice_output)) = tsyn2ustream\<cdot>((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-eve1_output)))"


lemma lemma4_pred_whole:
  assumes "def_Alice_HLR.wholePredicate () (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(alice_ctrl, alice_input)) (def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(alice_output))"
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(bob_input)) (def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(bob_control, bob_output))"
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(eve1_input)) (def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(eve1_output))"
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(eve2_input)) (def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(eve2_output))"
  assumes "def_Encrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(enc1_input)) (def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(enc1_output))"
  assumes "def_Encrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(enc2_input)) (def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(enc2_output))"
  assumes "def_Decrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(dec1_input)) (def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(dec1_output))"
  assumes "def_Decrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(dec2_input)) (def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(dec2_output))"
      and "enc1_input = alice_output"
      and "eve1_input = enc1_output"
      and "dec1_input = eve1_output"
      and "bob_input = dec1_output"
      and "enc2_input = bob_control"
      and "eve2_input = enc2_output"
      and "dec2_input = eve2_output"
      and "alice_ctrl = dec2_output"
  shows "lemma4_pred alice_output dec1_output"
  apply(subst lemma4_pred_def)
  apply(insert assms)
  using
    def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq
    def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq
    lemma4_streams_1
    encrypt_decrypt_1[OF assms(3,5,7,10,11)]
    encrypt_decrypt_2[OF assms(4,6,8,14,15)]
    assms
  by blast

lemma lemma4_pred_whole2:
  assumes "def_Alice_HLR.wholePredicate () (def_SecureProtocol_HLR2_alice_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2alice input))(def_SecureProtocol_HLR2_alice_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output))"
  assumes "def_Encrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2encrypt1 input))(def_SecureProtocol_HLR2_encrypt1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2encrypt1 output))"
  assumes "def_Eve1_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2eve1 input))(def_SecureProtocol_HLR2_eve1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2eve1 output))"
  assumes "def_Decrypt1_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt1_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2decrypt1 input))(def_SecureProtocol_HLR2_decrypt1_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt1 output))"
  assumes "def_Bob_HLR.wholePredicate () (def_SecureProtocol_HLR2_bob_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2bob input))(def_SecureProtocol_HLR2_bob_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2bob output))"
  assumes "def_Encrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_encrypt2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2encrypt2 input))(def_SecureProtocol_HLR2_encrypt2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2encrypt2 output))"
  assumes "def_Eve2_HLR.wholePredicate () (def_SecureProtocol_HLR2_eve2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2eve2 input))(def_SecureProtocol_HLR2_eve2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2eve2 output))"
  assumes "def_Decrypt2_HLR.wholePredicate () (def_SecureProtocol_HLR2_decrypt2_InputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawinput2decrypt2 input))(def_SecureProtocol_HLR2_decrypt2_OutputMap.connector\<cdot>(def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt2 output))"
  assumes "def_SecureProtocol_HLR2_connector.connector\<cdot>(def_SecureProtocol_HLR2_rawinput2connector input) = def_SecureProtocol_HLR2_rawoutput2connector output"
  assumes "rawinput2def_SecureProtocol_hlr2_feedback input = rawoutput2def_SecureProtocol_hlr2_feedback output"
  shows "lemma4_pred
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2alice output)
          (def_SecureProtocol_HLR2.def_SecureProtocol_HLR2_rawoutput2decrypt1 output)"
  apply(case_tac "output", case_tac "input")
  apply(rule lemma4_pred_whole) 
  using assms by (auto simp add: def_SecureProtocol_HLR2_connector.connector.rep_eq)

lemma lemma4_raw_pred_whole:
  assumes "spf \<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "lemma4_pred 
          (def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))
          (def_SecureProtocol_HLR2_decrypt1_Output.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst raw_output1_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(subst raw_output5_eq[OF assms(1) raw_input_type_helper, of sb])
  apply(simp only: def_SecureProtocol_HLR2_alice_Output.sbgetter_def
                  def_SecureProtocol_HLR2_decrypt1_Output.sbgetter_def)
  apply(simp only:
      def_SecureProtocol_HLR2.alice_output_Sub.getter_sub_eq
      def_SecureProtocol_HLR2.decrypt1_output_Sub.getter_sub_eq)

  apply(rule lemma4_pred_whole2[of "def_SecureProtocol_HLR2.RawInput.getter\<cdot>(sb \<uplus> spf\<cdot>sb\<star>)"])


  apply(simp only: alice_input_Sub.getter_sub_eq[symmetric] alice_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_alice_InputMap.connector.rep_eq def_SecureProtocol_HLR2_alice_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_alice_Input.getter_fold,
        subst def_SecureProtocol_HLR2_alice_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule alice_pred_general[OF assms(1)])
  apply(simp add: def_Alice_HLR.Sps_def)
  apply(simp only: encrypt1_input_Sub.getter_sub_eq[symmetric] encrypt1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_encrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_encrypt1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_encrypt1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule encrypt1_pred_general[OF assms(1)])
  apply(simp add: def_Encrypt1_HLR.Sps_def)
  apply(simp only: eve1_input_Sub.getter_sub_eq[symmetric] eve1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_eve1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_eve1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_eve1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule eve1_pred_general[OF assms(1)])
  apply(simp add: def_Eve1_HLR.Sps_def)
  apply(simp only: decrypt1_input_Sub.getter_sub_eq[symmetric] decrypt1_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_decrypt1_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt1_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_decrypt1_Input.getter_fold,
        subst def_SecureProtocol_HLR2_decrypt1_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule decrypt1_pred_general[OF assms(1)])
  apply(simp add: def_Decrypt1_HLR.Sps_def)
  apply(simp only: bob_input_Sub.getter_sub_eq[symmetric] bob_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_bob_InputMap.connector.rep_eq def_SecureProtocol_HLR2_bob_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_bob_Input.getter_fold,
        subst def_SecureProtocol_HLR2_bob_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule bob_pred_general[OF assms(1)])
  apply(simp add: def_Bob_HLR.Sps_def)
  apply(simp only: encrypt2_input_Sub.getter_sub_eq[symmetric] encrypt2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_encrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_encrypt2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_encrypt2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_encrypt2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule encrypt2_pred_general[OF assms(1)])
  apply(simp add: def_Encrypt2_HLR.Sps_def)
  apply(simp only: eve2_input_Sub.getter_sub_eq[symmetric] eve2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_eve2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_eve2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_eve2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_eve2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule eve2_pred_general[OF assms(1)])
  apply(simp add: def_Eve2_HLR.Sps_def)
  apply(simp only: decrypt2_input_Sub.getter_sub_eq[symmetric] decrypt2_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: def_SecureProtocol_HLR2_decrypt2_InputMap.connector.rep_eq def_SecureProtocol_HLR2_decrypt2_OutputMap.connector.rep_eq)
  apply(subst def_SecureProtocol_HLR2_decrypt2_Input.getter_fold,
        subst def_SecureProtocol_HLR2_decrypt2_Output.getter_fold,
        subst sb_star21, simp)
  apply(rule decrypt2_pred_general[OF assms(1)])
  apply(simp add: def_Decrypt2_HLR.Sps_def)
  apply(simp only: connector_input_Sub.getter_sub_eq[symmetric]
                   connector_output_Sub.getter_sub_eq[symmetric])
  apply(subst def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.getter_fold,
        subst def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst def_SecureProtocol_HLR2_Feedback.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

lemma lemma4:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "i = def_SecureProtocol_HLR2_alice_Output.SB.getter\<cdot>(spf\<cdot>(sb)\<star>)"
    and "out = def_SecureProtocol_HLR2_decrypt1_Output.SB.getter\<cdot>((spf\<cdot>(sb))\<star>)"
    and fin: "#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-i)) < \<infinity>"
    and eq1: "#\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_fst))\<cdot>(\<alpha>\<^sub>-i)) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>i))"
    and length_preserved: "#\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>(i))) = #\<^sub>-(\<alpha>\<^sub>-((smap (map_tsyn Data_Bool_Tuple_get_snd))\<cdot>out))"  
shows "(smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-i))\<^sup>- = (smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>(\<alpha>\<^sub>-out))\<^sup>-"
  using lemma4_raw_pred_whole assms lemma4_pred_whole
  by (smt lemma4_pred_def smap_Data_Bool_Tuple_get_fst_def2 smap_Data_Bool_Tuple_get_snd_def2)


end
