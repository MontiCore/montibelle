theory def_SecureProtocol_HLR1
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_SecureProtocol_HLR1.def_SecureProtocol_HLR1_Input bundle_SecureProtocol_HLR1.def_SecureProtocol_HLR1_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (nat tsyn stream) \<Rightarrow> (nat tsyn stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    (#\<^sub>-channel_input_val_pattern = \<infinity>)"

definition predicate_0 :: "unit \<Rightarrow> (nat tsyn stream) \<Rightarrow> (nat tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    (tsyn2ustream\<cdot> channel_output_val_pattern) = (tsyn2ustream\<cdot> channel_input_val_pattern)"

definition causality :: "(nat tsyn stream) \<Rightarrow> (nat tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (nat tsyn stream) \<Rightarrow> (nat tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_SecureProtocol_HLR1_Input.channels\<^sup>\<Omega> \<rightarrow> def_SecureProtocol_HLR1_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_SecureProtocol_HLR1_Input.SB.getter\<cdot>sb) (def_SecureProtocol_HLR1_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
