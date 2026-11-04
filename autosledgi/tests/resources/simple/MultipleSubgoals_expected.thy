theory MultipleSubgoals
  imports Main
begin

lemma twoSubgoals:
  assumes "a"
  assumes "b"
    shows "a \<and> b"
  apply rule
  (* Inserted automatically *)
apply (simp add: assms(1))
  (* Inserted automatically *)
by (simp add: assms(2))
  (* We are done here *)

end
