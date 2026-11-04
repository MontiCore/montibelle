theory ref_DLDF_HLR3_rough_DLDF_HLR1
  imports
    (* Gen *) sps_DLDF_HLR1.def_DLDF_HLR1 sps_DLDF_HLR3.def_DLDF_HLR3 ref_DLDF_HLR3_refines_DLDF_HLR2.ref_DLDF_HLR3_rough_DLDF_HLR2 ref_DLDF_HLR2_refines_DLDF_HLR1.ref_DLDF_HLR2_rough_DLDF_HLR1
    (* Hwl  *)

begin


(* General refinement skeleton *)
lemma refinement[simp]: "def_DLDF_HLR3.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLDF_HLR1.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
  (* autosledgi *) oops


end
