theory TryTac

imports Main

begin
default_sort type


ML\<open> 
(* SOLVE_TIMEOUT takes:
    * timeout in second
    * name for debug output 
    * context for debug output 
    * and a tactic
  and returns a tactic, which runs for <timeout> second and fails on a timeout
*)
fun SOLVE_TIMEOUT (seconds:int) (name:string) (cxt:Proof.context) (tac:tactic) (st:thm): thm Seq.seq =
  let
    val _ = writeln ("running " ^ name ^ " for " ^ (string_of_int seconds) ^ "s  on " ^ (Thm.string_of_thm cxt st))
    val result =
      Timeout.apply (Time.fromSeconds seconds) (fn () => SINGLE (SOLVE tac) st) ()
      handle Timeout.TIMEOUT _ => NONE | ERROR _ => NONE
  in
    (case result of
      NONE => (writeln ("TIMEOUT FAILURE: " ^ name); Seq.empty)
    | SOME st' => (writeln ("SUCCESS: " ^ name); Seq.single st'))
  end


fun trymethods (ctxt:Proof.context)  :  (string*tactic) list = [
      ("force", Clasimp.force_tac ctxt 1),
      ("blast", Blast.blast_tac ctxt 1), 
      ("presburger", Cooper.tac true [] [] ctxt  1),
      ("simp", (asm_full_simp_tac ctxt 1 )), 
      ("metis", Metis_Tactic.metis_tac [] "" ctxt [] 1)
    ]

(* tries different proof methods with a timeout. Fails if no method can be applied *)
fun myTac (ctxt:Proof.context) (timeout:int)  : tactic  = 
  trymethods ctxt                   (* list with all methods *)
  |> map (fn (msg:string,tac:tactic) => SOLVE_TIMEOUT timeout msg ctxt tac) (* for each method, set the timeout *)
  |> FIRST            (* combine tactics, try all tactics until the first suceeds *)
  |> SELECT_GOAL      (* SOMEHOW! MAGIC! That's the reason why in "trymethods" i write "1"*)
  |> PARALLEL_ALLGOALS 
\<close>

method_setup trytac = \<open>
  (* timeout: *) Scan.optional (Scan.lift Parse.nat) (* default timeout=*) 1 >>
    (fn n => fn ctxt => Method.SIMPLE_METHOD (myTac ctxt n))
      \<close> "try multiple proof methods with a timeout"



lemma "False \<longrightarrow> True" and "(1::nat) < 2"
  apply trytac
  done

lemma "\<exists>i::nat. 0<i \<and> i<5"
  apply (rule exI)
  apply trytac
  oops

lemma "\<exists>i::nat. 0<i \<and> i<5" and "False"
   apply (rule exI)
   apply(trytac)?
  oops

lemma "False" and "True"
   apply trytac?
  oops

end