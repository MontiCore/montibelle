theory AREC_test
  imports automaton.AREC
begin

definition "toTransition guard expression param state input 
  = (if (guard param state input) then (expression param state input) else {})"

ML \<open>val addTrans = map (fn (id:string,guard:term,expression:term) =>
       (id, guard, expression, @{term toTransition} $ guard $ expression))

  fun assert_eq a b = if (a=b) then () else error("Assertion error. Not equal!")
\<close>


definition "stateInv paramMax currentState = (currentState < (paramMax+50))"

definition "guard_1 (paramMax::nat) currentState currentInput = (currentInput > 0)"
definition "expression_1 paramMax currentState currentInput = {(currentState +1, 0)}"

ML \<open>
let
  val transitions = addTrans [("1", @{term guard_1}, @{term expression_1})];
  val result = checkInvariant @{context} @{term stateInv} (transitions)
in
  (checkEverything @{context} transitions)
end
\<close>





definition "guard_2 (paramMax::nat) currentState currentInput = (False)"
definition "expression_2 paramMax currentState currentInput = {(currentState +1, 0)}"

ML \<open>
let
  val transitions = addTrans [("1", @{term guard_2}, @{term expression_2})];
  val result = checkInvariant @{context} @{term stateInv} (transitions)
in
()
end
\<close>



definition "guard_11 (paramMax::nat) (currentState::bool) (currentInput::int)
   = (False)"

definition "guard_12 (paramMax::nat) (currentState::bool) (currentInput::int)
   = (currentInput < 11)"

definition "guard_13 (paramMax::nat) (currentState::bool) (currentInput::int)
   = (currentInput > 9)"

definition "expression_1x (paramMax::nat) (currentState::bool) (currentInput::int)
   = {(currentState, currentInput)}"



ML \<open>
fun disj_pairs ((x::xs):'a list): ('a* 'a) list = map (fn y => (x,y)) xs @ disj_pairs xs |
    disj_pairs (([]):'a list): ('a*'a) list = []
\<close>

ML_val\<open>
let 
  val transitions = addTrans [("1", @{term guard_11}, @{term expression_1x}), 
    ("2", @{term guard_12}, @{term expression_1x}), 
    ("3", @{term guard_13}, @{term expression_1x})];
in
 checkOverlappingGuards @{context} transitions
end
\<close>


definition hasMandatoryEffect::
 "('input \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  'param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> 'input \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"hasMandatoryEffect eq_on param state input1 input2 
              guard _ transition \<equiv> ((eq_on input1 input2) \<longrightarrow> input1 \<noteq> input2 \<longrightarrow>  guard param state input1 \<longrightarrow>
                  guard param state input2 \<longrightarrow>
                        transition param state input1 \<inter> transition param state input2 = {})"

definition hasGuaranteedNoEffect::
 "(('state \<times> 'input) \<Rightarrow> ('state \<times> 'input) \<Rightarrow> bool) \<Rightarrow>
  (('state \<times> 'output) \<Rightarrow> ('state \<times> 'output) \<Rightarrow> bool) \<Rightarrow>
  'param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow>
   ('state \<times> 'output) \<Rightarrow> ('state \<times> 'output) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> bool) \<Rightarrow>
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> 
  ('param \<Rightarrow> 'state \<Rightarrow> 'input \<Rightarrow> ('state \<times> 'output) set) \<Rightarrow> bool" where
"hasGuaranteedNoEffect eq_on_input eq_on_output param state1 input1 state2 input2 p p' 
              guard _ transition \<equiv> ((eq_on_input (state1,input1) (state2,input2))

                \<longrightarrow>  guard param state1 input1 
                \<longrightarrow>  guard param state2 input2 \<longrightarrow>
                       p \<in> transition param state1 input1 \<longrightarrow>  p'\<in> transition param state2 input2
                            \<longrightarrow> eq_on_output p p')"

definition "guard_31 (paramMax::nat) (currentState::nat) currentInput = (True)"
definition "expression_31 paramMax (currentState::nat) (currentInput::(nat\<times>nat)) = 
      {(currentState +1, fst currentInput + snd currentInput), (currentState +1, snd currentInput)}"

definition "all__no_effect_on__fst paramMax (currentState::nat) (currentInput::(nat\<times>nat)) = 
      {(1,2),(1,3),(1,currentState),(1,fst currentInput), (1,snd currentInput)}"

definition "all__maybe_effect_on__fst paramMax (currentState::nat) (currentInput::(nat\<times>nat)) = 
      {(1,2),(1,3),(2,currentState),(1,fst currentInput), (1,snd currentInput)}"


ML \<open>
let
  val transitions = addTrans [
    ("all__no_effect_on__fst", @{term guard_31}, @{term all__no_effect_on__fst}),
    ("all__maybe_effect_on__fst", @{term guard_31}, @{term all__maybe_effect_on__fst})
  ]
  val _ =  semco @{context} (onResultCounterexample "Might have an effect?" "hasGuaranteedNoEffect! "  )
  (@{term "hasGuaranteedNoEffect (\<lambda>_ _. True) (\<lambda>(o11,o12) (o21,o22). o11 = o21) param state1 input1 state2 input2
        output1 output2"} ) transitions
in 
  ()
end
\<close>



definition "eq_on_fst a b  = (fst a = fst b)"
definition "eq_on_snd a b  = (snd a = snd b)"

ML \<open>
let
  val transitions = addTrans [("1", @{term guard_31}, @{term expression_31})]
  val _ =  semco @{context} (onResultCounterexample "Found Not Mandatory Effect of SND : " "Found Mandatory Effect of SND : " )
  (@{term "hasMandatoryEffect eq_on_fst param state input1 input2"} ) transitions
  val _ =  semco @{context} (onResultCounterexample "Found Not Mandatory Effect of FST: " "Found Mandatory Effect of FST : ")
  (@{term "hasMandatoryEffect eq_on_snd param state input1 input2"} ) transitions

  val _ =  semco @{context} (onResultCounterexample "Found POTENTIAL Effect of SND : " "Found NO Effect of SND:" )
  (@{term "hasNoEffect eq_on_fst param state input1 input2"} ) transitions
  val _ =  semco @{context} (onResultCounterexample "Found POTENTIAL Effect of FST: "  "Found NO Effect of FST:" )
  (@{term "hasNoEffect eq_on_snd param state input1 input2"} ) transitions
in
  ()
end
\<close>


end