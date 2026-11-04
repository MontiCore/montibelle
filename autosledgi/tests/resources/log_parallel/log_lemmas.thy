theory log_lemmas
  imports HOLCF
begin

definition x::nat
  where "x = 1"

definition y::nat
  where "y = 2"

definition z::nat
  where "z = 3"

lemma a: "1 = 1"
  (* autosledgi *) sorry

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* autosledgi *) sorry

lemma c: "x = 1"
  (* autosledgi *) sorry

lemma d: "(y=2) ∧ (1+1=2)"
  apply (rule)
  (* autosledgi *) sorry

lemma e: "1 = 1"
  (* autosledgi *) sorry

lemma f: "z = 3"
  (* autosledgi *) sorry

end
