theory def_Alice_HLR
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Alice_HLR.def_Alice_HLR_Input bundle_Alice_HLR.def_Alice_HLR_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream \<times> string tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern) .
    (((((sprojfst\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>channel_output_val_pattern)))\<sqsubseteq>(tsyn2ustream\<cdot>channel_input_val_pattern)) \<and> ((srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>channel_output_val_pattern)))) = (sprojsnd\<cdot>(srcdups\<cdot>(tsyn2ustream\<cdot>channel_output_val_pattern))))) \<and> ((slen\<cdot>(srcdups\<cdot>channel_control_val_pattern)) < (slen\<cdot>channel_input_val_pattern))) \<longrightarrow> (((slen\<cdot>channel_output_val_pattern) = \<infinity>) \<and> ((slen\<cdot>(tsynProjFst\<cdot>(srcdups\<cdot>channel_output_val_pattern))) = (min (slen\<cdot>channel_input_val_pattern) (1 + (slen\<cdot>(srcdups\<cdot>channel_control_val_pattern)))))))"

definition causality :: "(bool tsyn stream \<times> string tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream \<times> string tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Alice_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Alice_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Alice_HLR_Input.SB.getter\<cdot>sb) (def_Alice_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
