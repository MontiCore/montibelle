theory WithoutNames
  imports HOLCF
begin

definition x::nat
  where "x = 1"

definition y::nat
  where "y = 2"

lemma "x = 1"
  (* Inserted automatically *)
by (simp add: x_def)
  (* We are done here *)

theorem "y = 2"
  (* Inserted automatically *)
by (simp add: y_def)
  (* We are done here *)

end
