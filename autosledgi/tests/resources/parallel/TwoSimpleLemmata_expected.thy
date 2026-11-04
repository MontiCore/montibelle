theory TwoSimpleLemmata
  imports HOLCF
begin

lemma a: "1 = 1"
  apply simp
  (* Inserted automatically *)
  done
  (* We are done here *)

lemma c: "1 = 1"
  (* Inserted automatically *)
by simp
  (* We are done here *)

end
