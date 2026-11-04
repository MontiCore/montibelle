theory ref_RefinedComponent_rough_RoughComponent
  imports
    (* Gen *) sps_RoughComponent.def_RoughComponent sps_RefinedComponent.def_RefinedComponent
    (* Hwl  *)

begin


lemma refinement[simp]: "def_RefinedComponent.Sps () \<subseteq> def_RoughComponent.Sps ()"
  by(auto simp add: def_RefinedComponent.Sps_def def_RoughComponent.Sps_def
                    def_RefinedComponent.wholePredicate_def def_RoughComponent.wholePredicate_def
                    def_RefinedComponent.predAndCausality_defs def_RoughComponent.predAndCausality_defs)


end
