theory def_Decrypt2_HLR
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Decrypt2_HLR.def_Decrypt2_HLR_Input bundle_Decrypt2_HLR.def_Decrypt2_HLR_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    channel_output_val_pattern = tsynMap Not\<cdot>channel_input_val_pattern"

definition causality :: "(bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    weakpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Decrypt2_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Decrypt2_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Decrypt2_HLR_Input.SB.getter\<cdot>sb) (def_Decrypt2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
