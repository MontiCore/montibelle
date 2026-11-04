theory AREC

imports Main

begin
default_sort type



ML \<open>
(* Basically this tactic does:
    apply(cases guard1; simp; cases guard2; simp; [...])
*)
fun doIT [] cxt = 
  ALLGOALS (asm_full_simp_tac cxt) |

doIT (l::ls) cxt = 
(*print_tac cxt "Beginning" THEN*)
(* (Induct_Tacs.case_tac cxt "" [] (SOME l) 1) THEN *)
(ALLGOALS (Induct.cases_tac cxt false [[SOME l ]] NONE [] )  )
(* THEN print_tac cxt "End"  *)
  THEN ((TRYALL (asm_full_simp_tac cxt))) 
  (* THEN (ALLGOALS (Blast.blast_tac cxt))  ==> Timeouts *)
  (*THEN (TRYALL ((fast_force_tac cxt)))  (* fastforce *)*)
   THEN (doIT ls cxt ) 

fun realGuards3 param state        = map (fn (_,y,_,_) => y $ param $ state) 
fun realGuards4 param state input  = map (fn (_,y,_,_) => y $ param $ state $ input) 

signature AUTOMATON = sig
  val transitionList : (string * term * term * term) list
end
\<close>



ML \<open>
(* STUPID! *)
(* I don't know how the automatic type-interference works! For example here:
         type_of ((@{term "id"}) $ @{term "1::nat"})
  this throws an error. So my solution is to replace the types for "id" with "dummyT", and 
  then let an automatic type-interferer run:
      \<open> type_of (Syntax.check_term @{context} ((removeTermType(@{term "id"})) $ @{term "1::nat"}))\<close>*)

fun removeType (Type (s,ls)) = (Type (s, map removeType ls)) |
    removeType (TFree _) = dummyT |
    removeType (TVar _) =dummyT

fun removeTermType (Const (s,T)) = Const (s, removeType T)
  | removeTermType (Free  (s,T)) = Free (s,removeType T)
  | removeTermType (Bound i) = (Bound i)
  | removeTermType (Var (s,T)) = (Var (s,removeType T))
  | removeTermType (Abs (s,T,body)) = Abs (s,removeType T, removeTermType body)
  | removeTermType (f$u) = (removeTermType f) $ (removeTermType u)

(* Takes a Term and returns "True" iff Nitpick finds a genuine counterxample *)
fun isWrong ctxt term = 
let
  val (result,_) = Nitpick.pick_nits_in_term 
    (Proof.init ctxt) (*state*)
    (Nitpick_Commands.default_params @{theory} 
      [ ("timeout", "10"), ("user_axioms", "true"), ("assms", "true"), ("mono", "true"), ("max_potential","0")]) (* Parameter = default *)
    Nitpick.Normal (* mode *) 
    1  1  5 (* ?? *)
    []
    []
    []
    term;
in
 (result = "genuine") end;


(* check given term is correct*)
fun hasCounterexample (ctxt:Proof.context) (term:term):bool = 
  (@{term Trueprop} $ term) 
    |> removeTermType
    |> Syntax.check_term ctxt                   (* Add Types to term (for nitpick) *)
    |> isWrong ctxt                             (* check if counterexample can be found *)


(* check if the predicate holds for every transition. Otherwise output a warning *)
fun semco (ctxt:Proof.context) (reaction:('a->bool->unit)) (predicate:term) (transitions:('a*term*term*term) list): bool = 
    fold (fn x => fn y => x andalso y)  
      (map (fn (line,guard,expression,transition) => 
                   tap (reaction line)  (* Directly react to result (e.g. print warning in output) *)
                   (hasCounterexample ctxt  (predicate $ guard $ expression $ transition))) 
        transitions)
    true

fun onCounterexample   (msg:string) (line:string) true = warning (msg ^ line) |
    onCounterexample _ _ _ = ()

fun onNoCounterexample (msg:string) (line:string) false = warning (msg ^ line) |
    onNoCounterexample _ _ _ = ()

fun onResultCounterexample (msgCounter:string) _ (line:string) true = warning (msgCounter ^ line) |
    onResultCounterexample _ (msgNoCounter:string) (line:string) false = warning (msgNoCounter ^ line) 
\<close>

definition guardSat::"'param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"guardSat p s i   guard _ _ \<equiv> \<not>guard p s i"


definition invariantHolds::"('param \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow>
  'param \<Rightarrow> 'input \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"invariantHolds P param input currentState nextState   _ _ transition' \<equiv>   
    P param currentState \<longrightarrow> nextState \<in> (fst` (transition' param currentState input)) 
                      \<longrightarrow> P param nextState"


definition isRefinement::
 "('paramOld \<Rightarrow> 'stateOld \<Rightarrow> 'input \<Rightarrow> ('stateOld \<times> 'output) set) \<Rightarrow>
  ('param \<Rightarrow> 'paramOld) \<Rightarrow>
  ('state \<Rightarrow> 'stateOld) \<Rightarrow>
  'state \<Rightarrow> 'input \<Rightarrow> 'param \<Rightarrow> 'state \<Rightarrow> 'output \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"isRefinement originalTrans mapParam mapState currentState currentInput p nextState nextOut 
              _ _ refTrans \<equiv> 
  ((nextState, nextOut) \<in> refTrans p currentState currentInput \<longrightarrow>
       ((mapState nextState,nextOut) \<in>   originalTrans (mapParam p) (mapState currentState) currentInput 
          \<or>  originalTrans (mapParam p) (mapState currentState) currentInput = {}))
  \<and> (refTrans p currentState currentInput = {} \<longrightarrow> originalTrans (mapParam p) (mapState currentState) currentInput = {})"

definition isRefinement_tick::
 "('paramOld \<Rightarrow> 'stateOld \<Rightarrow> ('stateOld \<times> 'output) set) \<Rightarrow>
  ('param \<Rightarrow> 'paramOld) \<Rightarrow>
  ('state \<Rightarrow> 'stateOld) \<Rightarrow>
  'state \<Rightarrow> 'param \<Rightarrow> 'state \<Rightarrow> 'output \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"isRefinement_tick originalTrans mapParam mapState currentState p nextState nextOut 
              _ _ refTrans \<equiv> 
  ((nextState, nextOut) \<in> refTrans p currentState \<longrightarrow>
       ((mapState nextState,nextOut) \<in>   originalTrans (mapParam p) (mapState currentState) 
          \<or>  originalTrans (mapParam p) (mapState currentState) = {}))
  \<and> (refTrans p currentState = {} \<longrightarrow> originalTrans (mapParam p) (mapState currentState) = {})"



ML \<open>
fun checkStateRefinement ctxt originalTrans mapParam mapState  = 
  semco ctxt (onCounterexample "Refinement Error: " )
  (@{term "isRefinement"}
      $originalTrans
      $mapParam
      $mapState
      $(@{term "currentState"})
      $(@{term "currentInput"}) 
      $(@{term "param"})
      $(@{term "nextState"})
      $(@{term "nextOut"})
  )

fun checkStateRefinement_tick ctxt originalTrans mapParam mapState  = 
  semco ctxt (onCounterexample "Refinement Error: " )
  (@{term "isRefinement_tick"}
      $originalTrans
      $mapParam
      $mapState
      $(@{term "currentState"})
      $(@{term "param"})
      $(@{term "nextState"})
      $(@{term "nextOut"})
  )

fun checkRefinement ctxt originalTrans  = 
  checkStateRefinement ctxt originalTrans @{term id} @{term id}


fun checkInvariant ctxt (predicate:term)  = 
  semco ctxt (onCounterexample "Invariant Error: ") 
  (@{term "invariantHolds"}
    $predicate
    $(@{term "param"})
    $(@{term "currentInput"}) 
    $(@{term "currentState"})
    $(@{term "nextState"})
  )


fun checkGuardSat ctxt  = 
  semco ctxt (onNoCounterexample "Guard not satisfiable: ") 
  (@{term "guardSat param state input"})







fun foldTermOr (terms:term list): term = 
  fold (fn x => fn y => @{term disj} $ x $ y) terms @{term False}

fun foldTermAnd (terms:term list): term =
  fold (fn x => fn y => @{term conj} $ x $ y) terms @{term True}


(* Only check if for every situation a guard is true.
  It is possible, that the expression returns {} *)
fun checkPartiality_fast (ctxt:Proof.context) (transitions:(string * term * term * term) list) = 
  transitions 
    |> map #2   (* Get only the guards *)
    |> map (fn t => t $ @{term param} $ @{term state} $ @{term input})  (* fill with free variables*)
    |> foldTermOr (* collaps into one large term *)
    |> hasCounterexample ctxt
    |> tap (onCounterexample "Guards are partial" "")
    


fun checkPartiality (ctxt:Proof.context) (transitions:(string * term * term * term) list):bool = 
  transitions 
    |> map #4   (* Get only the transitions *)
    |> map (fn t => t $ @{term param} $ @{term state} $ @{term input})  (* fill with free variables*)
    |> map (fn t => @{term "(\<noteq>) {}"} $ t)  (* check if transitions is empty *)
    |> foldTermOr (* collaps into one large term *)
    |> hasCounterexample ctxt
    |> tap (onCounterexample "Transition is partial" "")


fun disj_pairs ((x::xs):'a list): ('a* 'a) list = map (fn y => (x,y)) xs @ disj_pairs xs |
    disj_pairs (([]):'a list): ('a*'a) list = []



fun outerToInnerPair ((a:string,b,c,d),(a':string,b',c',d')) = 
  ((a ^ " " ^ a'),(@{term Pair} $b $b'), (@{term Pair} $ c $ c'), (@{term Pair} $ d $ d'))

fun semco_pairwise (ctxt:Proof.context) (reaction:(string->bool->unit)) (predicate:term)
                 (transitions:(string * term * term * term) list) =
  transitions 
    |> disj_pairs
    |> map outerToInnerPair
    |> semco ctxt reaction predicate


fun checkEverything (ctxt:Proof.context) (transitions:(string * term * term * term) list) = 
  [checkPartiality_fast, checkPartiality, checkGuardSat]
    |> map (fn f => ((f ctxt transitions); ()))
\<close>


definition guardOverlap::"'param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow>
  (('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<times> ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool)) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<times> ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<times> ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set)
     \<Rightarrow> bool" where
"guardOverlap p s i  guards  _ _ = (\<not>((fst guards) p s i \<and> (snd guards) p s i))"

ML\<open>
fun checkOverlappingGuards ctxt  = 
  semco_pairwise ctxt (onCounterexample "Overlapping guards: ") 
    @{term "guardOverlap p s i"}
\<close>

end