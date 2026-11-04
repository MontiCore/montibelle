theory def_Encrypt2_HLR
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Encrypt2_HLR.def_Encrypt2_HLR_Input bundle_Encrypt2_HLR.def_Encrypt2_HLR_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    ((channel_output_val_pattern = (smap (map_tsyn Not)\<cdot>channel_input_val_pattern)))"

definition causality :: "(bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Encrypt2_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Encrypt2_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Encrypt2_HLR_Input.SB.getter\<cdot>sb) (def_Encrypt2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
