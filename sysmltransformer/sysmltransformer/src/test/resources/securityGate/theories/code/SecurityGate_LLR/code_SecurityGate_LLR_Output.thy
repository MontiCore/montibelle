theory code_SecurityGate_LLR_Output
  imports
    (* Gen  *) bundle_SecurityGate_LLR.def_SecurityGate_LLR_Output
    (* Core *) bundle.SBCodegen
    (* Hwl  *)

begin


lemma [code]:"Enum.enum_ex (P::channels \<Rightarrow> bool) =  (\<exists>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)

lemma [code]:"Enum.enum_all (P::channels \<Rightarrow> bool) =  (\<forall>A\<in> set enum_class.enum. P (A))"
  apply (simp add: enum_channels_def)
  by (metis (full_types) channels.exhaust)


end
