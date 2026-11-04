theory ref_Scheduler_LLR_rough_Scheduler_HLR2
  imports
    (* Gen *) sps_Scheduler_HLR2.def_Scheduler_HLR2 sps_Scheduler_LLR.def_Scheduler_LLR ref_Scheduler_LLR_refines_Scheduler_HLR3.ref_Scheduler_LLR_rough_Scheduler_HLR3 ref_Scheduler_HLR3_refines_Scheduler_HLR2.ref_Scheduler_HLR3_rough_Scheduler_HLR2
    (* Hwl  *)

begin


(* General refinement skeleton *)
lemma refinement[simp]: "def_Scheduler_LLR.Sps (var_capacity) \<subseteq> def_Scheduler_HLR2.Sps (var_capacity)"
  (* autosledgi *) oops


end
