theory MultipleSubgoals
  imports Main
begin

lemma twoSubgoals:
  assumes "a"
  assumes "b"
    shows "a \<and> b"
  apply rule
  (* autosledgi *) sorry

end