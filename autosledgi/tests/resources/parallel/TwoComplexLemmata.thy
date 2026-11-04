theory TwoComplexLemmata
  imports HOLCF
begin

definition y::nat
  where "y = 2"

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* autosledgi *) sorry

lemma d: "(y=2) ∧ (1+1=2)"
  apply (rule)
  (* autosledgi *) sorry

end
