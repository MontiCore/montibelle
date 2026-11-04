theory def_Eve_HLR
  imports
    (* Core *) sps.SPSComp
    (* Gen  *) bundle_Eve_HLR.def_Eve_HLR_Input bundle_Eve_HLR.def_Eve_HLR_Output
    (* Hwl  *)

begin


definition predicate_0 :: "unit \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    (Bex (UNIV :: bool stream set) (\<lambda> ora. ((channel_output_val_pattern = (tsynBoolFilter\<cdot>channel_input_val_pattern\<cdot>ora)) \<and> ((slen\<cdot>( {True} \<ominus> ora)) = \<infinity>))))"

definition causality :: "((string\<times>bool) tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> ((string\<times>bool) tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Eve_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Eve_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Eve_HLR_Input.SB.getter\<cdot>sb) (def_Eve_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
