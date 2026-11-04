theory ref_DLUF_HLR3_rough_DLUF_HLR1
  imports
    (* Gen *) sps_DLUF_HLR1.def_DLUF_HLR1 sps_DLUF_HLR3.def_DLUF_HLR3 ref_DLUF_HLR3_refines_DLUF_HLR2.ref_DLUF_HLR3_rough_DLUF_HLR2 ref_DLUF_HLR2_refines_DLUF_HLR1.ref_DLUF_HLR2_rough_DLUF_HLR1
    (* Hwl  *)

begin


(* General refinement skeleton *)
lemma refinement[simp]: "def_DLUF_HLR3.Sps (var_cap1, var_cap2, var_cap3, var_cap4) \<subseteq> def_DLUF_HLR1.Sps (var_cap1, var_cap2, var_cap3, var_cap4)"
  (* autosledgi *) oops


end
