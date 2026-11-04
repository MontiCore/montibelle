theory MultipleSledgehammer
  imports HOLCF
begin

lemma test: "1 = 1"
  apply simp
sledgehammer [isar_proofs=true] nitpick
sledgehammer [isar_proofs=true] nitpick
  (* autosledgi *) sorry

end
