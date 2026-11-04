theory lo_lemma_0_Eve2
  imports
    lo_sps_Eve2
    lo_lemma_util
begin


definition lemma0_sb :: "'ca::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cb::{tsynchan}\<^sup>\<Omega> \<Rightarrow> bool" where
  "lemma0_sb \<equiv> \<lambda> input output.
                  tsynSBlen (tsynSBRemDups\<cdot>input) \<ge> tsynSBlen (tsynSBRemDups\<cdot>output)"



lemma
  eve2_lemma0_sb:
  assumes "spf \<in> def_Eve2_HLR.Sps ()"
  shows "lemma0_sb sb (spf\<cdot>sb)"
  apply(auto simp add: lemma0_sb_def)
  apply(insert def_Eve2_HLR_sps_def2[OF assms])
  apply (drule_tac x=sb in meta_spec, auto)
  by (smt abs_rep_id assms cfcomp2 chdom_in def_Eve2_HLR_Input.channel_input_val_rep def_Eve2_HLR_Input.channels_chdom def_Eve2_HLR_sps_def2_pred insert_compr mem_Collect_eq singleton_conv2 somechannotempty toTsynMsgStream_tsynMsgToMStream_id
    tsynLenM_def tsynlen_remdups_boolfilter_leq tsynsbremdups_tsynsblen_ex)


lemma eve2_lemma0_general:
  assumes "spf \<in> (def_SecureProtocol_HLR2.rawSps ())"
    shows "lemma0_sb ((sb \<uplus> spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Input.channels\<^sup>\<Omega>)
             ((spf\<cdot>sb)\<star> :: def_SecureProtocol_HLR2_eve2_Output.channels\<^sup>\<Omega>)"
proof(rule eve2_pred_general_sb[OF assms])
  fix spf
  fix sb
  assume a: "spf \<in> def_Eve2_HLR.Sps ()"

  have b: "tsynSBlen (tsynSBRemDups\<cdot>sb) \<ge> tsynSBlen (tsynSBRemDups\<cdot>(spf\<cdot>sb))"
    using a eve2_lemma0_sb lemma0_sb_def by metis

  have c: "tsynSBlen (tsynSBRemDups\<cdot>(def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(def_Eve2_HLR_Input.sbgetter\<cdot>sb))) = Min {#\<^sub>-(\<alpha>\<^sub>-(smap (map_tsyn boolEVENTConstr)\<cdot> (def_Eve2_HLR_Input.sbgetter\<cdot>sb)))}"
    using def_SecureProtocol_HLR2_eve2_Input_tsynSBlen_setter_f tsynSBRemDups_is_lifted by blast

  then show "lemma0_sb
          (def_SecureProtocol_HLR2_eve2_Input.sbsetter\<cdot>(def_Eve2_HLR_Input.sbgetter\<cdot>sb))
          (def_SecureProtocol_HLR2_eve2_Output.sbsetter\<cdot>(def_Eve2_HLR_Output.sbgetter\<cdot>(spf\<cdot>sb)))"
    apply(simp add: lemma0_sb_def)
    by (metis b c def_SecureProtocol_HLR2_eve2_Output_tsynSBlen_setter_f def_Eve2_HLR_Input.SB.set_get def_Eve2_HLR_Input_tsynSBlen_setter_f def_Eve2_HLR_Output.SB.set_get def_Eve2_HLR_Output_tsynSBlen_setter_f tsynSBRemDups_is_lifted)

qed

end
