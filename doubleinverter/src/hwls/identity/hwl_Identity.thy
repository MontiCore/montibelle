theory hwl_Identity
  imports sps_HlrIdentity.def_HlrIdentity sps_HlrDoubleInverter.def_HlrDoubleInverter
          sps_HlrDoubleInverter_inverter1.def_HlrDoubleInverter_inverter1
          sps_HlrDoubleInverter_inverter2.def_HlrDoubleInverter_inverter2
begin

lemma pred_0_hwl:
"(def_HlrInverter.assumption_0 () channel_input_val_pattern
      channel_HlrDoubleInverter_inverter1_output_val_rep_pattern \<longrightarrow>
     def_HlrInverter.predicate_0 () channel_input_val_pattern
      channel_HlrDoubleInverter_inverter1_output_val_rep_pattern) \<and>
    def_HlrInverter.causality channel_input_val_pattern channel_HlrDoubleInverter_inverter1_output_val_rep_pattern \<Longrightarrow>
    (wellformed channel_HlrDoubleInverter_inverter1_output_val_rep_pattern \<and>
     def_HlrInverter.assumption_0 () channel_HlrDoubleInverter_inverter1_output_val_rep_pattern
      channel_HlrDoubleInverter_inverter2_output_val_rep_pattern \<longrightarrow>
     def_HlrInverter.predicate_0 () channel_HlrDoubleInverter_inverter1_output_val_rep_pattern
      channel_HlrDoubleInverter_inverter2_output_val_rep_pattern) \<and>
    def_HlrInverter.causality channel_HlrDoubleInverter_inverter1_output_val_rep_pattern
     channel_HlrDoubleInverter_inverter2_output_val_rep_pattern \<Longrightarrow>
    wellformed channel_input_val_pattern \<Longrightarrow>
    slen\<cdot>channel_input_val_pattern = \<infinity> \<Longrightarrow>
    \<forall>t::nat. snthTs t\<cdot>channel_HlrDoubleInverter_inverter2_output_val_rep_pattern = snthTs t\<cdot>channel_input_val_pattern"
  apply(simp add: def_HlrInverter.assumption_0_def def_HlrInverter.predicate_0_def)
  apply(simp add: def_HlrInverter.causality_def len_stream_def weakpred_def wellformed_stream_def)
  apply(simp add: DefinitionOfNot.Not_def smapsmap2smap)
  by(metis eventlenleqlen inf_less_eq len_stream_def)

end