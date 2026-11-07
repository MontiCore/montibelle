theory lo_lemma_3_Bob
  imports
    lo_sps_Bob
begin

default_sort countable




definition liveMed_sb :: "'ca::{tsynchan}\<^sup>\<Omega> \<Rightarrow> def_Bob_HLR_Output.channels\<^sup>\<Omega> \<Rightarrow> bool" where
  "liveMed_sb \<equiv> \<lambda> input output.
                  (tsynSBlen input = \<infinity> \<longrightarrow> tsynLenM\<cdot>(output  \<^enum>  def_Bob_HLR_Output.channel_control_val) = \<infinity>)"

definition liveMed_sb_system :: "'ca::{tsynchan}\<^sup>\<Omega> \<Rightarrow> def_SecureProtocol_HLR2_bob_Output.channels\<^sup>\<Omega> \<Rightarrow> bool" where
  "liveMed_sb_system \<equiv> \<lambda> input output.
                  (tsynSBlen input = \<infinity> \<longrightarrow> tsynLenM\<cdot>(output  \<^enum>  def_SecureProtocol_HLR2_bob_Output.channel_bob_control_val) = \<infinity>)"


lemma
  bob_liveMed_sb_pred:
  assumes "spf \<in> def_Bob_HLR.Sps ()"
    and "tsynSBlen sb = \<infinity>"
  shows "tsynLenM\<cdot>(spf\<cdot>sb  \<^enum>  def_Bob_HLR_Output.channel_control_val) = \<infinity>"
  apply (auto simp add: assms def_Bob_HLR_sps_def2_pred_1  def_Bob_HLR_sps_def2_pred_2 tsynLenM_def toTsynMsgStream_def tsynMsgToMStream_def tsynProjSnd_def tsynProjFst_def)
  apply(simp add: smaps2smap[of "(inv Tsyn \<circ> inv Timed)" "(Timed \<circ> Tsyn)"] tsynFst_def2 tsynSnd_def2 tsynLen_smap_map_tsyn[symmetric])
  apply(simp add: toTsynMsgStream_def[symmetric] def_Bob_HLR_Input_getter_getch tsynLen_smap_map_tsyn[symmetric])
  by (metis Min.singleton assms(2) def_Bob_HLR_Input.SB.set_get def_Bob_HLR_Input_tsynSBlen_setter)

lemma
  bob_liveMed_sb:
  assumes "spf \<in> def_Bob_HLR.Sps ()"
  shows "liveMed_sb sb (spf\<cdot>sb)"
  by(auto simp add: liveMed_sb_def bob_liveMed_sb_pred[OF assms])

end
