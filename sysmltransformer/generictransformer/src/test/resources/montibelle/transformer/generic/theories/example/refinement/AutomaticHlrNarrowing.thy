theory AutomaticHlrNarrowing
  imports
    (* Gen *) specification.Specification specification.Specification
    (* Hwl  *)

begin


lemma refinement[simp]: "Specification.Sps () \<subseteq> Specification.Sps ()"
  by(auto simp add: Specification.Sps_def Specification.Sps_def
                    Specification.wholePredicate_def Specification.wholePredicate_def
                    Specification.predAndCausality_defs Specification.predAndCausality_defs)


end
