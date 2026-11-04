theory hwl_lemma_util
  imports
    move_to_core.hwl_core_ext

    sps_SecureProtocol_HLR2.def_SecureProtocol_HLR2 
begin

lemma raw_input_type_helper: "spf\<cdot>sb = spf\<cdot>sb" ..


lemma raw_input_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "((sb)\<star>::def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega>)
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Input.channels
                           \<union>def_SecureProtocol_HLR2_alice_Input.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Input.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Input.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Input.channels
                           \<union>def_SecureProtocol_HLR2_bob_Input.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Input.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Input.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Input.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR1_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output1_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "((spf\<cdot>sb\<star> :: def_SecureProtocol_HLR2_alice_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output2_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
  shows "((spf\<cdot>sb\<star> :: def_SecureProtocol_HLR2_eve2_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)


lemma raw_output3_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "((spf\<cdot>sb\<star> :: def_SecureProtocol_HLR2_eve1_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output4_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)


lemma raw_output5_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_decrypt1_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output6_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_decrypt2_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)


lemma raw_output7_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_encrypt1_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

lemma raw_output8_eq:
  assumes "spf\<in>(def_SecureProtocol_HLR2.rawSps ())"
    and "spf\<cdot>sb = spf\<cdot>sb"
    shows "(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_encrypt2_Output.channels sb))
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(def_SecureProtocol_HLR2_connector_SecureProtocol_HLR2_connector_Output.channels
                           \<union>def_SecureProtocol_HLR2_alice_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve1_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt1_Output.channels
                           \<union>def_SecureProtocol_HLR2_bob_Output.channels
                           \<union>def_SecureProtocol_HLR2_encrypt2_Output.channels
                           \<union>def_SecureProtocol_HLR2_eve2_Output.channels
                           \<union>def_SecureProtocol_HLR2_decrypt2_Output.channels)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)


lemma h2: "srcdups\<cdot>(smap Data_Bool_Tuple2tuple\<cdot>(srcdups\<cdot>x)) = smap Data_Bool_Tuple2tuple\<cdot>(srcdups\<cdot>x)"
  apply(induct x, simp_all)
  by (smt Data_Bool_Tuple2tuple_inj injD smap_scons smap_sup srcdups_eq srcdups_neq srcdups_shd2 srcdups_sup sup_conc_eps2 surj_scons)

lemma h1: "srcdups oo smap Data_Bool_Tuple2tuple = smap Data_Bool_Tuple2tuple oo srcdups"
  apply(rule cfun_eqI)
  apply(simp add: oo_def)
  apply(rule srcdups_smap_com)
  by(rule h2)

lemma h3: "tsyn2ustream oo (smap (map_tsyn Data_Bool_Tuple_get_fst)) = smap Data_Bool_Tuple_get_fst oo tsyn2ustream"
  apply(rule cfun_eqI)
  apply(simp add: oo_def)
  by (metis tsynMap_def2 tsynmap_tsynabs)

lemma h4: "srcdups oo tsyn2ustream = tsyn2ustream oo tsynRemDups"
  apply(rule cfun_eqI)
  apply(simp add: oo_def)
  by (simp add: tsynremdups_tsynabs)

lemma h5: "sprojfst oo smap Data_Bool_Tuple2tuple = smap Data_Bool_Tuple_get_fst"
  apply(rule cfun_eqI)
  apply(simp add: oo_def sprojfst_def smaps2smap)
  by (metis Data_Bool_Tuple2tuple.elims Data_Bool_Tuple_get_fst.simps fst_conv)

lemma alice_helper: "sprojfst oo srcdups oo smap Data_Bool_Tuple2tuple oo tsyn2ustream
            = tsyn2ustream oo (smap (map_tsyn Data_Bool_Tuple_get_fst)) oo tsynRemDups"
  by (metis (no_types, opaque_lifting) h1 h3 h4 h5 oo_assoc)


lemma Data_Bool_Tuple_get_fst_def2: "map_tsyn Data_Bool_Tuple_get_fst = tsynFst o map_tsyn Data_Bool_Tuple2tuple"
  by(rule ext, case_tac x, simp, case_tac a, simp)

lemma smap_Data_Bool_Tuple_get_fst_def2: "smap (map_tsyn Data_Bool_Tuple_get_fst)\<cdot>s = \<Pi>\<^sub>1\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s)"
  by(simp add: tsynProjFst_def smaps2smap Data_Bool_Tuple_get_fst_def2 comp_def)

lemma Data_Bool_Tuple_get_snd_def2: "map_tsyn Data_Bool_Tuple_get_snd = tsynSnd o map_tsyn Data_Bool_Tuple2tuple"
  by(rule ext, case_tac x, simp, case_tac a, simp)

lemma smap_Data_Bool_Tuple_get_snd_def2: "smap (map_tsyn Data_Bool_Tuple_get_snd)\<cdot>s = \<Pi>\<^sub>2\<^sub>-(smap (map_tsyn Data_Bool_Tuple2tuple)\<cdot>s)"
  by(simp add: tsynProjSnd_def smaps2smap Data_Bool_Tuple_get_snd_def2 comp_def)

end
