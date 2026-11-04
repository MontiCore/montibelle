theory TwoSubgoals
  imports HOLCF
begin

definition x::nat
  where "x = 1"

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* Inserted automatically *)
apply simp
  (* Inserted automatically *)
by simp
  (* We are done here *)

lemma c: "x = 1"
  (* Inserted automatically *)
by (simp add: x_def)
  (* We are done here *)

end
