theory ref_SecureProtocol_LLR_rough_SecureProtocol_HLR1
  imports
    (* Gen *) sps_SecureProtocol_HLR1.def_SecureProtocol_HLR1 sps_SecureProtocol_LLR.def_SecureProtocol_LLR ref_SecureProtocol_LLR_refines_SecureProtocol_HLR2.ref_SecureProtocol_LLR_rough_SecureProtocol_HLR2 ref_SecureProtocol_HLR2_refines_SecureProtocol_HLR1.ref_SecureProtocol_HLR2_rough_SecureProtocol_HLR1
    (* Hwl  *)

begin


(* General refinement skeleton *)
lemma refinement[simp]: "def_SecureProtocol_LLR.Sps () \<subseteq> def_SecureProtocol_HLR1.Sps ()"
  apply(rule subset_trans[where B="def_SecureProtocol_HLR2.Sps ()"])?
  apply(simp_all)?
  (* autosledgi *) oops


end
