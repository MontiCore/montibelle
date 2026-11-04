theory TwoComplexLemmata
  imports HOLCF
begin

definition y::nat
  where "y = 2"

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* Inserted automatically *)
apply simp
  (* Inserted automatically *)
by simp
  (* We are done here *)

lemma d: "(y=2) ∧ (1+1=2)"
  apply (rule)
  (* Inserted automatically *)
apply (simp add: y_def)
  (* Inserted automatically *)
by simp
  (* We are done here *)

end
