theory ref_Inverter_HLR2_rough_Inverter_HLR1
  imports
    (* Gen *) sps_Inverter_HLR1.def_Inverter_HLR1 sps_Inverter_HLR2.def_Inverter_HLR2
    (* Hwl  *)

begin


lemma refinement[simp]: "def_Inverter_HLR2.Sps () \<subseteq> def_Inverter_HLR1.Sps ()"
  apply(auto simp add: def_Inverter_HLR2.Sps_def def_Inverter_HLR1.Sps_def
                    def_Inverter_HLR2.wholePredicate_def def_Inverter_HLR1.wholePredicate_def
                    def_Inverter_HLR2.predAndCausality_defs def_Inverter_HLR1.predAndCausality_defs)
  (* autosledgi *) sorry


end
