theory lo_lemma_3_Eve2
  imports
    lo_sps_Eve2
begin

default_sort countable



definition liveMed_sb :: "'ca::{tsynchan}\<^sup>\<Omega> \<Rightarrow> 'cb::{tsynchan}\<^sup>\<Omega> \<Rightarrow> bool" where
  "liveMed_sb \<equiv> \<lambda> input output.
                  (tsynSBlen input = \<infinity> \<longrightarrow> tsynSBlen output = \<infinity>)"



lemma rename_well: "ctype (Rep def_Eve2_HLR_Input.channel_input_val) \<subseteq> ctype (Rep (def_Eve2_HLR_Output.channel_output_val))"
  by(simp add: ctype_def)



lemma
  eve2_liveMed_sb:
  assumes "spf \<in> def_Eve2_HLR.Sps ()"
  shows "liveMed_sb sb (spf\<cdot>sb)"
  apply(auto simp add: liveMed_sb_def)
  apply(insert def_Eve2_HLR_sps_def2[OF assms])
  apply (drule_tac x=sb in meta_spec, auto)
  apply(subst tsynsbboolfilter_live_single_rename, simp_all)
  by(case_tac c, simp add: rename_well[simplified])

end
