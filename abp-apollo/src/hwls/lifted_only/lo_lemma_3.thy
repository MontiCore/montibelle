theory lo_lemma_3
  imports
    move_to_core.hwl_core_ext

    to_be_generated.hwl_tsynSBlens

    lo_lemma_3_Bob
    lo_lemma_3_Eve1
    lo_lemma_3_Eve2
    lo_lemma_util
begin



lemma livemed_eve1:
  assumes "spf\<in> def_SecureProtocol_HLR2_eve1.Sps ()"
  shows "lo_lemma_3_Eve1.liveMed_sb sb (spf\<cdot>sb)"
  apply(rule eve1_pred_inst2def_sb)
  apply(insert eve1_liveMed_sb)
  apply(simp add: lo_lemma_3_Eve1.liveMed_sb_def)
  apply(simp add: def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter_eq_def_Eve1_HLR_Input_tsynSBlen_setter)
  apply(simp add: def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter_eq_def_Eve1_HLR_Output_tsynSBlen_setter)
  by(rule assms)


lemma livemed_eve1_general:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
    shows "lo_lemma_3_Eve1.liveMed_sb ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Output.channels\<^sup>\<Omega>)"
  apply(rule eve1_pred_general_sb[OF assms])
  by (metis def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter_eq_def_Eve1_HLR_Input_tsynSBlen_setter def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter_eq_def_Eve1_HLR_Output_tsynSBlen_setter eve1_liveMed_sb
      lo_lemma_3_Eve1.liveMed_sb_def)


lemma livemed_eve2:
  assumes "spf\<in> def_SecureProtocol_HLR2_eve2.Sps ()"
  shows "lo_lemma_3_Eve2.liveMed_sb sb (spf\<cdot>sb)"
  apply(rule eve2_pred_inst2def_sb)
  apply(insert eve2_liveMed_sb)
  apply(simp add: lo_lemma_3_Eve2.liveMed_sb_def)
  apply(simp add: def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_eq_def_Eve2_HLR_Input_tsynSBlen_setter)
  apply(simp add: def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter_eq_def_Eve2_HLR_Output_tsynSBlen_setter)
  by(rule assms)


lemma livemed_eve2_general:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
    shows "lo_lemma_3_Eve2.liveMed_sb ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Output.channels\<^sup>\<Omega>)"
  apply(rule eve2_pred_general_sb[OF assms])
  by (metis def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_eq_def_Eve2_HLR_Input_tsynSBlen_setter def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter_eq_def_Eve2_HLR_Output_tsynSBlen_setter eve2_liveMed_sb
      lo_lemma_3_Eve2.liveMed_sb_def)



lemma livemed_bob:
  assumes "spf\<in> def_SecureProtocol_HLR2_bob.Sps ()"
  shows "lo_lemma_3_Bob.liveMed_sb_system sb (spf\<cdot>sb)"
  apply(rule bob_pred_inst2def_sb)
  apply(simp only: lo_lemma_3_Bob.liveMed_sb_system_def)
  apply(subst def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter_eq_def_Bob_HLR_Input_tsynSBlen_setter)
proof-
  fix spf
  fix sb
  assume a: "spf \<in> def_Bob_HLR.Sps ()"
  obtain a b where ab: "def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb) = (a, b)"
    by fastforce
  have eq: "def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>(def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))  \<^enum>  def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val = spf\<cdot>sb  \<^enum>  def_Bob_HLR_Output.channel_control_val"
    apply(simp add: ab def_SecureProtocol_HLR2_bob_Output.buildSB_def)
    by (metis ab def_Bob_HLR_Output.SB.set_get def_Bob_HLR_Output.SB.setter_getch def_Bob_HLR_Output.buildSB_def def_Bob_HLR_Output.channelsChan.simps(1))

  show "tsynSBlen sb = \<infinity> \<longrightarrow>
       tsynLenM\<cdot>(def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>(def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb))  \<^enum>  def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val) = \<infinity>"
    by(simp add: eq bob_liveMed_sb_pred a)
next
  show "spf \<in> def_SecureProtocol_HLR2_bob.Sps ()"
    by (rule assms)
qed

lemma livemed_bob_general:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
    shows "lo_lemma_3_Bob.liveMed_sb_system ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega>)"
  apply(rule bob_pred_general_sb[OF assms])
  apply (simp add: lo_lemma_3_Bob.liveMed_sb_system_def def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter_eq_def_Bob_HLR_Input_tsynSBlen_setter)
proof-
  fix spf
  fix sb
  assume a: "spf \<in> def_Bob_HLR.Sps ()"
  obtain a b where ab: "def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb) = (a, b)"
    by fastforce

  show "tsynSBlen sb = \<infinity> \<longrightarrow>
       tsynLenM\<cdot>(def_SecureProtocol_HLR2_bob_Output.buildSB (def_Bob_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)) def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val) = \<infinity>"
    apply(simp add: ab def_SecureProtocol_HLR2_bob_Output.buildSB_def)
    by (metis a ab bob_liveMed_sb_pred def_Bob_HLR_Output.SB.set_get def_Bob_HLR_Output.SB.setter_getch def_Bob_HLR_Output.buildSB_def
        def_Bob_HLR_Output.channelsChan.simps(1))
qed


lemma
  def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_def_Bob_HLR_Output_tsynSBlen_setter_inf:
  assumes "tsynSBlen (sb :: def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega>) = \<infinity>"
  shows "tsynSBlen (def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(fst (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>sb))) = \<infinity>"
  by (metis assms def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_geq_def_Bob_HLR_Output_tsynSBlen_setter_fst inf_less_eq)

lemma lemma3_alice_eve1:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  assumes "tsynSBlen (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR2_alice_Output.channels\<^sup>\<Omega>) = \<infinity>"
  shows "tsynSBlen ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve1_Input.channels\<^sup>\<Omega>) = \<infinity>"
proof-
  have "#\<^sub>-(def_SecureProtocol_HLR2_alice_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)) = \<infinity>"
    by (metis Min.singleton assms(2) def_SecureProtocol_HLR2_alice_Output.SB.set_get def_SecureProtocol_HLR2_alice_Output_tsynSBlen_setter)
  then have "#\<^sub>-(def_SecureProtocol_HLR2_eve1_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = \<infinity>"
    by (metis alice_out_eve1_in assms(1))
  thus ?thesis
    by (metis Min.singleton def_SecureProtocol_HLR2_eve1_Input.SB.set_get def_SecureProtocol_HLR2_eve1_Input_tsynSBlen_setter)
qed

lemma lemma3_eve1_bob:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  assumes "tsynSBlen (spf\<cdot>(sb)\<star> :: def_SecureProtocol_HLR2_eve1_Output.channels\<^sup>\<Omega>) = \<infinity>"
  shows "tsynSBlen ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Input.channels\<^sup>\<Omega>) = \<infinity>"
proof-
  have "#\<^sub>-(def_SecureProtocol_HLR2_eve1_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>)) = \<infinity>"
    by (metis Min.singleton assms(2) def_SecureProtocol_HLR2_eve1_Output.SB.set_get def_SecureProtocol_HLR2_eve1_Output_tsynSBlen_setter)
  then have "#\<^sub>-(def_SecureProtocol_HLR2_bob_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = \<infinity>"
    by (metis eve1_out_bob_in assms(1))
  thus ?thesis
    by (metis Min.singleton def_SecureProtocol_HLR2_bob_Input.SB.set_get def_SecureProtocol_HLR2_bob_Input_tsynSBlen_setter)
qed

lemma lemma3_bob_eve2:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  assumes "tsynLenM\<cdot>(((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega>)  \<^enum>  def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val) = \<infinity>"
  shows "tsynSBlen ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Input.channels\<^sup>\<Omega>) = \<infinity>"
proof-
  obtain c out where d: "(spf\<cdot>sb)\<star> = def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>(c, out)"
    by (metis def_SecureProtocol_HLR2_bob_Output.SB.set_get prod.collapse)

  have ctrl_unfolded:
    "def_SecureProtocol_HLR2_bob_Output.sbsetter\<cdot>(c, out) \<^enum> def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val
      = smap (Timed \<circ> Tsyn \<circ> map_tsyn boolEVENTConstr)\<cdot>c"
    by(simp add: def_SecureProtocol_HLR2_bob_Output.SB.setter_getch def_SecureProtocol_HLR2_bob_Output.buildSB_def)

  have c_fin_impl_unfolded_fin:
    "#\<^sub>-c \<noteq> \<infinity> \<Longrightarrow> tsynLenM\<cdot>(smap (Timed \<circ> Tsyn \<circ> map_tsyn boolEVENTConstr)\<cdot>c) \<noteq> \<infinity>"
    by (metis cfcomp2 toTsynMsgStream_smap_Timed_Tsyn_f tsynLenM_def tsynLen_smap_map_tsyn)

  have "#\<^sub>-(fst (def_SecureProtocol_HLR2_bob_Output.sbgetter\<cdot>(spf\<cdot>(sb)\<star>))) = \<infinity>"
    apply(simp add: d)
    apply(rule ccontr)
    by (metis c_fin_impl_unfolded_fin ctrl_unfolded assms(2) d)
      then have "#\<^sub>-(def_SecureProtocol_HLR2_eve2_Input.sbgetter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = \<infinity>"
    by (metis bob_ctrl_eve2_in assms(1))
  thus ?thesis
    by (metis Min.singleton def_SecureProtocol_HLR2_eve2_Input.SB.set_get def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter)
qed

lemma lemma3:
  assumes "spf\<in> def_SecureProtocol_HLR2.rawSps ()"
  shows "tsynSBlen ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_alice_Output.channels\<^sup>\<Omega>) = \<infinity> \<Longrightarrow>
    tsynSBlen ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Output.channels\<^sup>\<Omega>) = \<infinity>"
  apply(rule livemed_eve2_general[simplified lo_lemma_3_Eve2.liveMed_sb_def, rule_format, OF assms])
  apply(rule lemma3_bob_eve2[OF assms])
  apply(rule livemed_bob_general[simplified lo_lemma_3_Bob.liveMed_sb_system_def, rule_format, OF assms])
  apply(rule lemma3_eve1_bob[OF assms])
  apply(rule livemed_eve1_general[simplified lo_lemma_3_Eve1.liveMed_sb_def, rule_format, OF assms])
  apply(rule lemma3_alice_eve1[OF assms])
  by(simp)

end
