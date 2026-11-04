theory def_Encrypt1_HLR
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Encrypt1_HLR.def_Encrypt1_HLR_Input bundle_Encrypt1_HLR.def_Encrypt1_HLR_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    ((channel_output_val_pattern = (tsynZipAlt\<cdot>(smap (map_tsyn Encrypt)\<cdot>(tsynProjFst\<cdot>channel_input_val_pattern))\<cdot>(smap (map_tsyn Not)\<cdot>(tsynProjSnd\<cdot>channel_input_val_pattern)))))"

definition causality :: "((nat\<times>bool) tsyn stream) \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> ((nat\<times>bool) tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Encrypt1_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Encrypt1_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Encrypt1_HLR_Input.SB.getter\<cdot>sb) (def_Encrypt1_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
