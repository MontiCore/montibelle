theory false_lemma
  imports HOLCF
begin

lemma progress: "1 = 1"
  apply simp
  (* Inserted automatically *)
  done
  (* We are done here *)

lemma test: "False"
  (* Sorry, could not find a proof automatically *)
  sorry

end
