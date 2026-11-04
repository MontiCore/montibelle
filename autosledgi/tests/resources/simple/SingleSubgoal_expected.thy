theory SingleSubgoal
  imports HOLCF
begin

lemma test3: "1 = 1"
  apply simp
  (* Inserted automatically *)
  done
  (* We are done here *)

end
