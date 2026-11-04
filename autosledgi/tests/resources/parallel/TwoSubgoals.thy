theory TwoSubgoals
  imports HOLCF
begin

definition x::nat
  where "x = 1"

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* autosledgi *) sorry

lemma c: "x = 1"
  (* autosledgi *) sorry

end
