theory def_Alice_HLR
  imports
    (* Core *) sps.SPSComp stream.EventStream
    (* Gen  *) bundle_Alice_HLR.def_Alice_HLR_Input bundle_Alice_HLR.def_Alice_HLR_Output
    (* Hwl  *)

begin


definition assumption_0 :: "unit \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> bool" where
"assumption_0 \<equiv> \<lambda> () (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern) .
    #channel_control_val_pattern = \<infinity> \<and> #channel_input_val_pattern = \<infinity>"

definition predicate_0 :: "unit \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> bool" where
"predicate_0 \<equiv> \<lambda> () (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern) .
    (((sprojfst oo srcdups oo (smap Data_Bool_Tuple2tuple) oo tsyn2ustream)\<cdot>channel_output_val_pattern)
      \<sqsubseteq> tsyn2ustream\<cdot>channel_input_val_pattern)
  \<and> ((srcdups oo sprojsnd oo srcdups oo (smap Data_Bool_Tuple2tuple) oo tsyn2ustream)\<cdot>channel_output_val_pattern
      = (sprojsnd oo srcdups oo (smap Data_Bool_Tuple2tuple) oo tsyn2ustream)\<cdot>channel_output_val_pattern)
  \<and> (#\<^sub>-(\<alpha>\<^sub>-channel_control_val_pattern) < #\<^sub>-channel_input_val_pattern \<longrightarrow> #\<^sub>-(channel_output_val_pattern) = \<infinity>)
  \<and> ((tsynLen oo tsynProjFst oo tsynRemDups oo (smap (map_tsyn Data_Bool_Tuple2tuple)))\<cdot>channel_output_val_pattern
      = min (#\<^sub>-channel_input_val_pattern) (Fin 1 + #\<^sub>-(\<alpha>\<^sub>-channel_control_val_pattern)))
"

definition causality :: "(bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> bool" where
"causality \<equiv> \<lambda> (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern) .
    strongpred (channel_control_val_pattern, channel_input_val_pattern) (channel_output_val_pattern)"

lemmas predAndCausality_defs = predicate_0_def causality_def

definition wholePredicate :: "unit \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream) \<Rightarrow> (Data_Bool_Tuple tsyn stream) \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input\<and> assumption_0 para input output)
      \<longrightarrow> (predicate_0 para input output))
  \<and> (causality input output))"

definition Sps :: "unit \<Rightarrow> (def_Alice_HLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Alice_HLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). {spf | spf. \<forall>sb.
wholePredicate () (def_Alice_HLR_Input.SB.getter\<cdot>sb) (def_Alice_HLR_Output.SB.getter\<cdot>(spf\<cdot>sb))}"


end
