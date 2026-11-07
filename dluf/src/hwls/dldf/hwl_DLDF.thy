theory hwl_DLDF
  imports
    sps_DLDF_HLR1.def_DLDF_HLR1
    sps_DLDF_HLR2.def_DLDF_HLR2
    sps_DLDF_HLR2_scheduler1.def_DLDF_HLR2_scheduler1
    sps_DLDF_HLR2_scheduler2.def_DLDF_HLR2_scheduler2
    sps_DLDF_HLR2_scheduler3.def_DLDF_HLR2_scheduler3
    sps_DLDF_HLR2_scheduler4.def_DLDF_HLR2_scheduler4
begin

lemma sg1:
 "((𝕎) channel_input1_data_pattern ∧
     assumption_0 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ∧
     assumption_1 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ∧
     assumption_2 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ⟶
     predicate_0 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern) ∧
    #⇩√ channel_input1_data_pattern <⇧l
    #⇩√ channel_scheduler1_output_data_pattern ⟹
    ((𝕎) channel_input2_data_pattern ∧
     assumption_0 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ∧
     assumption_1 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ∧
     assumption_2 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ⟶
     predicate_0 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern) ∧
    #⇩√ channel_input2_data_pattern <⇧l
    #⇩√ channel_scheduler2_output_data_pattern ⟹
    ((𝕎) channel_input3_data_pattern ∧
     assumption_0 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ∧
     assumption_1 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ∧
     assumption_2 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ⟶
     predicate_0 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern) ∧
    #⇩√ channel_input3_data_pattern <⇧l
    #⇩√ channel_scheduler3_output_data_pattern ⟹
    ((𝕎) channel_input4_data_pattern ∧
     assumption_0 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ∧
     assumption_1 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ∧
     assumption_2 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ⟶
     predicate_0 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern) ∧
    #⇩√ channel_input4_data_pattern <⇧l
    #⇩√ channel_scheduler4_output_data_pattern ⟹
    channel_scheduler1_input_data_pattern = channel_input1_data_pattern ⟹
    channel_scheduler2_input_data_pattern = channel_input2_data_pattern ⟹
    channel_scheduler3_input_data_pattern = channel_input3_data_pattern ⟹
    channel_scheduler4_input_data_pattern = channel_input4_data_pattern ⟹
    channel_output1_data_pattern =
    channel_scheduler1_output_data_pattern ⟹
    channel_output2_data_pattern =
    channel_scheduler2_output_data_pattern ⟹
    channel_output3_data_pattern =
    channel_scheduler3_output_data_pattern ⟹
    channel_output4_data_pattern =
    channel_scheduler4_output_data_pattern ⟹
    min (#⇩√ channel_input1_data_pattern)
     (min (#⇩√ channel_input2_data_pattern)
       (min (#⇩√ channel_input3_data_pattern)
         (#⇩√ channel_input4_data_pattern))) <⇧l
    #⇩√ channel_scheduler1_output_data_pattern"
proof -
  assume a1: "((𝕎) channel_input1_data_pattern ∧ def_Scheduler_HLR2.assumption_0 cap1 channel_input1_data_pattern channel_scheduler1_output_data_pattern ∧ def_Scheduler_HLR2.assumption_1 cap1 channel_input1_data_pattern channel_scheduler1_output_data_pattern ∧ def_Scheduler_HLR2.assumption_2 cap1 channel_input1_data_pattern channel_scheduler1_output_data_pattern ⟶ def_Scheduler_HLR2.predicate_0 cap1 channel_input1_data_pattern channel_scheduler1_output_data_pattern) ∧ #⇩√ channel_input1_data_pattern <⇧l #⇩√ channel_scheduler1_output_data_pattern"
  have "∀l la. min (l::lnat) la ≤ l"
    using min.cobounded1 by blast
  then show ?thesis
    using a1 by (meson dual_order.trans lnsuc_lnle_emb)
qed

lemma sg2:
 "((𝕎) channel_input1_data_pattern ∧
     assumption_0 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ∧
     assumption_1 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ∧
     assumption_2 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern ⟶
     predicate_0 cap1 channel_input1_data_pattern
      channel_scheduler1_output_data_pattern) ∧
    #⇩√ channel_input1_data_pattern <⇧l
    #⇩√ channel_scheduler1_output_data_pattern ⟹
    ((𝕎) channel_input2_data_pattern ∧
     assumption_0 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ∧
     assumption_1 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ∧
     assumption_2 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern ⟶
     predicate_0 cap2 channel_input2_data_pattern
      channel_scheduler2_output_data_pattern) ∧
    #⇩√ channel_input2_data_pattern <⇧l
    #⇩√ channel_scheduler2_output_data_pattern ⟹
    ((𝕎) channel_input3_data_pattern ∧
     assumption_0 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ∧
     assumption_1 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ∧
     assumption_2 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern ⟶
     predicate_0 cap3 channel_input3_data_pattern
      channel_scheduler3_output_data_pattern) ∧
    #⇩√ channel_input3_data_pattern <⇧l
    #⇩√ channel_scheduler3_output_data_pattern ⟹
    ((𝕎) channel_input4_data_pattern ∧
     assumption_0 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ∧
     assumption_1 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ∧
     assumption_2 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern ⟶
     predicate_0 cap4 channel_input4_data_pattern
      channel_scheduler4_output_data_pattern) ∧
    #⇩√ channel_input4_data_pattern <⇧l
    #⇩√ channel_scheduler4_output_data_pattern ⟹
    channel_scheduler1_input_data_pattern = channel_input1_data_pattern ⟹
    channel_scheduler2_input_data_pattern = channel_input2_data_pattern ⟹
    channel_scheduler3_input_data_pattern = channel_input3_data_pattern ⟹
    channel_scheduler4_input_data_pattern = channel_input4_data_pattern ⟹
    channel_output1_data_pattern =
    channel_scheduler1_output_data_pattern ⟹
    channel_output2_data_pattern =
    channel_scheduler2_output_data_pattern ⟹
    channel_output3_data_pattern =
    channel_scheduler3_output_data_pattern ⟹
    channel_output4_data_pattern =
    channel_scheduler4_output_data_pattern ⟹
    min (#⇩√ channel_input1_data_pattern)
     (min (#⇩√ channel_input2_data_pattern)
       (min (#⇩√ channel_input3_data_pattern)
         (#⇩√ channel_input4_data_pattern))) <⇧l
    #⇩√ channel_scheduler2_output_data_pattern ∧
    min (#⇩√ channel_input1_data_pattern)
     (min (#⇩√ channel_input2_data_pattern)
       (min (#⇩√ channel_input3_data_pattern)
         (#⇩√ channel_input4_data_pattern))) <⇧l
    #⇩√ channel_scheduler3_output_data_pattern ∧
    min (#⇩√ channel_input1_data_pattern)
     (min (#⇩√ channel_input2_data_pattern)
       (min (#⇩√ channel_input3_data_pattern)
         (#⇩√ channel_input4_data_pattern))) <⇧l
    #⇩√ channel_scheduler4_output_data_pattern"
  by (metis Lattices.linorder_class.min.absorb2
      Lattices.linorder_class.min.bounded_iff
      Lattices.linorder_class.min.cobounded2
      lnsuc_lnle_emb)

lemma causality:
  assumes "def_Scheduler_HLR2.wholePredicate (cap1)  (def_DLDF_HLR2_scheduler1_InputMap.connector⋅(channel_scheduler1_input_data_pattern)) (def_DLDF_HLR2_scheduler1_OutputMap.connector⋅(channel_scheduler1_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (cap2)  (def_DLDF_HLR2_scheduler2_InputMap.connector⋅(channel_scheduler2_input_data_pattern)) (def_DLDF_HLR2_scheduler2_OutputMap.connector⋅(channel_scheduler2_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (cap3)  (def_DLDF_HLR2_scheduler3_InputMap.connector⋅(channel_scheduler3_input_data_pattern)) (def_DLDF_HLR2_scheduler3_OutputMap.connector⋅(channel_scheduler3_output_data_pattern))"
  assumes "def_Scheduler_HLR2.wholePredicate (cap4)  (def_DLDF_HLR2_scheduler4_InputMap.connector⋅(channel_scheduler4_input_data_pattern)) (def_DLDF_HLR2_scheduler4_OutputMap.connector⋅(channel_scheduler4_output_data_pattern))"
      and "channel_scheduler1_input_data_pattern = channel_input1_data_pattern"
      and "channel_scheduler2_input_data_pattern = channel_input2_data_pattern"
      and "channel_scheduler3_input_data_pattern = channel_input3_data_pattern"
      and "channel_scheduler4_input_data_pattern = channel_input4_data_pattern"
      and "channel_output1_data_pattern = channel_scheduler1_output_data_pattern"
      and "channel_output2_data_pattern = channel_scheduler2_output_data_pattern"
      and "channel_output3_data_pattern = channel_scheduler3_output_data_pattern"
      and "channel_output4_data_pattern = channel_scheduler4_output_data_pattern"
    shows "def_DLDF_HLR1.causality (channel_input1_data_pattern, channel_input2_data_pattern, channel_input3_data_pattern, channel_input4_data_pattern) (channel_output1_data_pattern, channel_output2_data_pattern, channel_output3_data_pattern, channel_output4_data_pattern)"
  apply(insert assms)
  apply(simp add: def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def def_Scheduler_HLR2.wholePredicate_def def_Scheduler_HLR2.causality_def
                  def_DLDF_HLR1.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add: def_DLDF_HLR2_scheduler1_InputMap.connector.rep_eq def_DLDF_HLR2_scheduler1_OutputMap.connector.rep_eq def_DLDF_HLR2_scheduler2_InputMap.connector.rep_eq def_DLDF_HLR2_scheduler2_OutputMap.connector.rep_eq def_DLDF_HLR2_scheduler3_InputMap.connector.rep_eq def_DLDF_HLR2_scheduler3_OutputMap.connector.rep_eq def_DLDF_HLR2_scheduler4_InputMap.connector.rep_eq def_DLDF_HLR2_scheduler4_OutputMap.connector.rep_eq)?
  apply(simp add: def_DLDF_HLR1.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  apply(fact sg1)
  by(fact sg2)
  
  
end
