theory Complex
  imports HOLCF
begin

definition x::nat
  where "x = 1"

definition y::nat
  where "y = 2"

definition z::nat
  where "z = 3"

lemma a: "1 = 1"
  (* Inserted automatically *)
by simp
  (* We are done here *)

lemma b: "(1=1) ∧ (2=2)"
  apply (rule)
  (* Inserted automatically *)
apply simp
  (* Inserted automatically *)
by simp
  (* We are done here *)

lemma c: "x = 1"
  (* Inserted automatically *)
by (simp add: x_def)
  (* We are done here *)

lemma d: "((y=2) ∧ (1+1=2)) ∧ (x=1)"
  apply (rule)
  apply (rule)
  (* Inserted automatically *)
apply (simp add: y_def)
  (* Inserted automatically *)
apply simp
  (* Inserted automatically *)
by (simp add: x_def)
  (* We are done here *)

lemma e: "z = 3"
  (* Inserted automatically *)
by (simp add: z_def)
  (* We are done here *)
