theory ref_Receiver_LLR_rough_Receiver_HLR
  imports
    (* Gen *) Smart_Isabelle.Smart_Isabelle
              sps_Bob_HLR.def_Bob_HLR sps_Bob_LLR.def_Bob_LLR
    (* Hwl  *) hwl_Bob.hwl_ref_Bob_LLR_rough_Bob_HLR

begin



lemma refinement[simp]: "def_Bob_LLR.Sps () \<subseteq> def_Bob_HLR.Sps ()"
unfolding def_Bob_HLR.Sps_def wholePredicate_def def_Bob_LLR.Sps_def
  (* autosledgi *) oops

end

