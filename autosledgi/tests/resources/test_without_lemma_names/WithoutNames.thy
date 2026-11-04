theory WithoutNames
  imports HOLCF
begin

definition x::nat
  where "x = 1"

definition y::nat
  where "y = 2"

lemma "x = 1"
  (* autosledgi *) sorry

theorem "y = 2"
  (* autosledgi *) sorry

end
