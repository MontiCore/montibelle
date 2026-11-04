theory def_Eve2_HLR
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Eve2_HLR.def_Eve2_HLR_Input bundle_Eve2_HLR.def_Eve2_HLR_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    (True)"

definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_input_val_pattern) (channel_output_val_pattern) .
    \<exists>(ora :: bool stream). #({True} \<ominus> ora) = \<infinity> \<and> (channel_output_val_pattern = tsynBoolFilter\<cdot>channel_input_val_pattern\<cdot>ora)"

definition causality :: "(bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_input_val_pattern) (channel_output_val_pattern) .
    weakpred (channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream) \<Rightarrow> (bool tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Eve2_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Eve2_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Eve2_HLR_Input.SB.getter\<cdot>sb) (def_Eve2_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
