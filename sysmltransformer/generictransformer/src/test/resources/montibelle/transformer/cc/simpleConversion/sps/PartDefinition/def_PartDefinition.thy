theory def_PartDefinition
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_PartDefinition.def_PartDefinition_Input bundle_PartDefinition.def_PartDefinition_Output
    (* Hwl  *)

begin


definition causality :: "(bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_i_pattern) (channel_o_pattern) .
    strongpred (channel_i_pattern) (channel_o_pattern)"

lemmas predAndCausality_defs = causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool event stream) \<Rightarrow> (bool event stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input)
      )
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_PartDefinition_Input.channels\<^sup>\<Omega> \<rightarrow> def_PartDefinition_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_PartDefinition_Input.SB.getter\<cdot>sb) (def_PartDefinition_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
