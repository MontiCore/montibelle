theory lightcontrol_flasher_Ref
  imports
    (* Gen  *) sps_Flasher_HLR1.def_Flasher_HLR1 sps_Flasher_HLR2.def_Flasher_HLR2
               sps_Flasher_HLR2_and1.def_Flasher_HLR2_and1 sps_Flasher_HLR2_not1.def_Flasher_HLR2_not1 
    (* Hwl  *) reference.lightcontrol

begin



lemma tone_to_bool_transfer:
  assumes "out = smap (\<lambda>(a, b). TOneMsg (inverseTOne a \<and> inverseTOne b))\<cdot>(szip\<cdot>in1\<cdot>in2)"
  shows "And_HLR (smap inverseTOne\<cdot>in1, smap inverseTOne\<cdot>in2) (smap inverseTOne\<cdot>out)"
  using assms
  apply (simp add: And_HLR.simps)
  apply (subst smapsmap2smap smap_szip[symmetric])
  apply (auto simp: smapsmap2smap)
  apply (simp add: o_def split_def)
  done

lemma tone_to_bool_and:
  "smap inverseTOne \<cdot>
   (smap (\<lambda>(a,b). TOneMsg (inverseTOne a \<and> inverseTOne b)) \<cdot> (szip\<cdot>x\<cdot>y)) =
   smap (\<lambda>(x,y). x \<and> y) \<cdot> (szip\<cdot>(smap inverseTOne\<cdot>x)\<cdot>(smap inverseTOne\<cdot>y))"
  using split_beta tone_to_bool_transfer by auto

(* comment to check if it makes ci faster
lemma h1[simp]: "smap inverseTOne\<cdot>(smap (TOneMsg o f)\<cdot>s) = smap f \<cdot> s"
  proof (induction s)
    case (step a s)
    then show ?case 
      by (simp add: inverseTOne.simps)
  qed (simp_all)

lemma h2[simp]: "smap inverseTOne\<cdot>(\<up>(TOneMsg m) \<Zcat> s) = \<up>m \<Zcat> (smap inverseTOne\<cdot>s)"
  apply (subst smap_split)
  apply (simp add: inverseTOne.simps)
  done
*)
lemma pred_0:
  assumes "def_And_HLR.wholePredicate ()  (def_Flasher_HLR2_and1_InputMap.connector\<cdot>(channel_and1_input1_val_pattern, channel_and1_input2_val_pattern)) (def_Flasher_HLR2_and1_OutputMap.connector\<cdot>(channel_and1_output_val_pattern))"
  assumes "def_StrongNot_HLR.wholePredicate ()  (def_Flasher_HLR2_not1_InputMap.connector\<cdot>(channel_not1_input_val_pattern)) (def_Flasher_HLR2_not1_OutputMap.connector\<cdot>(channel_not1_output_val_pattern))"
      and "True"
      and "channel_and1_input1_val_pattern = channel_input_val_pattern"
      and "channel_and1_input2_val_pattern = channel_not1_output_val_pattern"
      and "channel_output_val_pattern = channel_and1_output_val_pattern"
      and "channel_not1_input_val_pattern = channel_and1_output_val_pattern"
    shows "def_Flasher_HLR1.predicate_0 () (channel_input_val_pattern) (channel_output_val_pattern)"
proof -
  have and_hlr: "And_HLR (smap inverseTOne\<cdot>channel_input_val_pattern, 
                         smap inverseTOne\<cdot>channel_not1_output_val_pattern) 
                        (smap inverseTOne\<cdot>channel_output_val_pattern)"
    using assms(1,4,6) 
    apply (auto simp: def_And_HLR.wholePredicate_def def_And_HLR.predicate_0_def)
    apply (simp add: def_And_HLR.assumption_0_def)
    by (simp add: assms(5) def_Flasher_HLR2_and1_InputMap.connector.rep_eq def_Flasher_HLR2_and1_OutputMap.connector.rep_eq tone_to_bool_and)

  have snot_hlr: "strongNot_HLR (smap inverseTOne\<cdot>channel_output_val_pattern) 
                               (smap inverseTOne\<cdot>channel_not1_output_val_pattern)"
    using assms(2,6,7) 
    apply (auto simp: def_StrongNot_HLR.wholePredicate_def def_StrongNot_HLR.predicate_0_def)
   apply (auto simp: assms def_StrongNot_HLR.assumption_0_def
      def_Flasher_HLR2_and1_InputMap.connector.rep_eq def_Flasher_HLR2_and1_OutputMap.connector.rep_eq
      def_Flasher_HLR2_and1_OutputMap.connector_def def_Flasher_HLR2_not1_InputMap.connector_def def_Flasher_HLR2_not1_OutputMap.connector_def)
    by (simp add: smaps2smap) 

  define s_in where "s_in = smap inverseTOne \<cdot> channel_input_val_pattern"
  define s_out where "s_out = smap inverseTOne \<cdot> channel_output_val_pattern"
  define s_not where "s_not = smap inverseTOne \<cdot> channel_not1_output_val_pattern"

  have blink: "\<forall>t. Suc t < #s_in \<longrightarrow> snth (Suc t) s_in \<longrightarrow> snth (Suc t) s_out \<noteq> snth t s_out"
    using and_hlr snot_hlr flasher_pred_h unfolding s_in_def s_out_def s_not_def by blast

  have length_eq: "#s_out = #s_in"
    using and_hlr snot_hlr flasherout_len 
    apply (auto simp: s_in_def s_out_def s_not_def len_prod_minl)
    by (metis (no_types, lifting) and_hlr and_len len_prod_def2 min_rek slen_smap snot_hlr strongnot_len)

  have start_val: "shd s_out = shd s_in"
    using and_hlr snot_hlr flasher_pred_shd unfolding s_in_def s_out_def s_not_def by blast

  show ?thesis
    unfolding def_Flasher_HLR1.predicate_0_def
    using blink length_eq start_val
    apply (simp add: s_in_def s_out_def)
    apply (simp add: smap_snth_lemma)
    by (metis Fin_Suc below_shd convert_inductive_asm empty_is_shortest fin_le_inf le2lnle sconc_prefix shd_single smap_hd_rst smap_snth_lemma snths_eq
      sup_noteps)
qed

lemma causality:
  assumes "def_And_HLR.causality  (def_Flasher_HLR2_and1_InputMap.connector\<cdot>(channel_and1_input1_val_pattern, channel_and1_input2_val_pattern)) (def_Flasher_HLR2_and1_OutputMap.connector\<cdot>(channel_and1_output_val_pattern))"
  assumes "def_StrongNot_HLR.causality  (def_Flasher_HLR2_not1_InputMap.connector\<cdot>(channel_not1_input_val_pattern)) (def_Flasher_HLR2_not1_OutputMap.connector\<cdot>(channel_not1_output_val_pattern))"
      and "channel_and1_input1_val_pattern = channel_input_val_pattern"
      and "channel_and1_input2_val_pattern = channel_not1_output_val_pattern"
      and "channel_output_val_pattern = channel_and1_output_val_pattern"
      and "channel_not1_input_val_pattern = channel_and1_output_val_pattern"
    shows "def_Flasher_HLR1.causality (channel_input_val_pattern) (channel_output_val_pattern)"
  apply(insert assms)
  apply(simp add: def_And_HLR.wholePredicate_def def_And_HLR.causality_def def_StrongNot_HLR.wholePredicate_def def_StrongNot_HLR.causality_def
                  def_Flasher_HLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_Flasher_HLR2_and1_InputMap.connector.rep_eq def_Flasher_HLR2_and1_OutputMap.connector.rep_eq def_Flasher_HLR2_not1_InputMap.connector.rep_eq def_Flasher_HLR2_not1_OutputMap.connector.rep_eq)?
  apply(simp add: def_Flasher_HLR1.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  by (metis inf_great lnle_and_gt_inf(1) min_def verit_comp_simplify1(3) len_prod_def2)

end
