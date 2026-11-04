theory def_Alice_LLR
  imports
    (* Core *) tscomponent.TsLocale tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) bundle_Alice_LLR.def_Alice_LLR_Input bundle_Alice_LLR.def_Alice_LLR_Output def_Alice_LLR_States
    (* Hwl  *)

begin

fun liftedPair :: "('a::type tsyn \<times> 'b::type tsyn) \<Rightarrow> ('a \<times> 'b) tsyn" where
"liftedPair (TSynMsg a, TSynMsg b) = TSynMsg (a, b)" |
"liftedPair _                      = Eps"

fun liftedList :: "'a::type tsyn list \<Rightarrow> 'a list tsyn" where
"liftedList []                = TSynMsg []" |
"liftedList (Eps # _)         = Eps" |
"liftedList (TSynMsg a # as)  = liftedApplyTwo Cons (TSynMsg a) (liftedList as)"


fun guard_0 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__EmptyBuf \<and> (True))"

fun expression_0 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__SingleBuf ((unlift (lift var_ctrl))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift var_ctrl)))))
}"

fun transitionH_0 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_1 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__EmptyBuf \<and> (True))"

fun expression_1 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__EmptyBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), (Eps))
}"

fun transitionH_1 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_2 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__SingleBuf \<and> ((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl))))))"

fun expression_2 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__EmptyBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
}"

fun transitionH_2 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_3 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__SingleBuf \<and> ((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl))))))"

fun expression_3 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift (Not var_ctrl))))))
}"

fun transitionH_3 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_4 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__SingleBuf \<and> ((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl))))))"

fun expression_4 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift (Not var_ctrl))))))
}"

fun transitionH_4 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_5 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__SingleBuf \<and> (True))"

fun expression_5 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__SingleBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
}"

fun transitionH_5 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_6 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__SingleBuf \<and> (True))"

fun expression_6 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (liftedApplyTwo append (lift var_buffer) (liftedList [channel_input_val_pattern])))), ((liftedPair (channel_input_val_pattern, (lift var_ctrl)))))
}"

fun transitionH_6 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_7 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> (True))"

fun expression_7 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
}"

fun transitionH_7 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_8 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> (((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl)))) \<and> (toBool (liftedApplyTwo (<) ((lift 2)) ((liftedApplyOne length (lift var_buffer))))))))"

fun expression_8 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
}"

fun transitionH_8 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_9 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> (((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl)))) \<and> (toBool (liftedEq ((liftedApplyOne length (lift var_buffer))) ((lift 2)))))))"

fun expression_9 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
}"

fun transitionH_9 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_10 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> (True))"

fun expression_10 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (liftedApplyTwo append (lift var_buffer) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
}"

fun transitionH_10 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_11 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> ((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl))))))"

fun expression_11 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyTwo append (liftedApplyOne tl (lift var_buffer)) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (liftedApplyOne tl (lift var_buffer))), (lift (Not var_ctrl))))))
}"

fun transitionH_11 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"

fun guard_12 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> bool" where
"guard_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = (s = Substate.state__MultiBuf \<and> ((toBool (liftedEq (channel_control_val_pattern) ((lift var_ctrl))))))"

fun expression_12 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"expression_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = {
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyTwo append (liftedApplyOne tl (lift var_buffer)) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (liftedApplyOne tl (lift var_buffer))), (lift (Not var_ctrl))))))
}"

fun transitionH_12 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transitionH_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (expression_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else {})"



definition transition :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"transition para state input =
    transitionH_0 para state input \<union>
    transitionH_1 para state input \<union>
    transitionH_2 para state input \<union>
    transitionH_3 para state input \<union>
    transitionH_4 para state input \<union>
    transitionH_5 para state input \<union>
    transitionH_6 para state input \<union>
    transitionH_7 para state input \<union>
    transitionH_8 para state input \<union>
    transitionH_9 para state input \<union>
    transitionH_10 para state input \<union>
    transitionH_11 para state input \<union>
    transitionH_12 para state input"

definition initialConfigs :: "(bool) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) set" where
"initialConfigs  \<equiv> \<lambda> (var_init_ctrl) .  {}"

interpretation behavior:
    tsStrongGen
      transition
      initialConfigs
      def_Alice_LLR_Input.buildSBE
      def_Alice_LLR_Output.buildSBE
  by%visible(unfold_locales; simp_all add: def_Alice_LLR_Input.SBE.c_empty def_Alice_LLR_Output.SBE.c_empty)

ML \<open>structure def_Alice_LLR = struct
  val transitionList  = [
    ("line 26 to 34", @{term guard_0}, @{term expression_0}, @{term transitionH_0}),
    ("line 36 to 44", @{term guard_1}, @{term expression_1}, @{term transitionH_1}),
    ("line 46 to 55", @{term guard_2}, @{term expression_2}, @{term transitionH_2}),
    ("line 58 to 67", @{term guard_3}, @{term expression_3}, @{term transitionH_3}),
    ("line 69 to 78", @{term guard_4}, @{term expression_4}, @{term transitionH_4}),
    ("line 80 to 88", @{term guard_5}, @{term expression_5}, @{term transitionH_5}),
    ("line 90 to 98", @{term guard_6}, @{term expression_6}, @{term transitionH_6}),
    ("line 100 to 108", @{term guard_7}, @{term expression_7}, @{term transitionH_7}),
    ("line 110 to 119", @{term guard_8}, @{term expression_8}, @{term transitionH_8}),
    ("line 121 to 130", @{term guard_9}, @{term expression_9}, @{term transitionH_9}),
    ("line 133 to 141", @{term guard_10}, @{term expression_10}, @{term transitionH_10}),
    ("line 143 to 152", @{term guard_11}, @{term expression_11}, @{term transitionH_11}),
    ("line 154 to 163", @{term guard_12}, @{term expression_12}, @{term transitionH_12})]
end\<close>

definition Sps :: "(bool) \<Rightarrow> (def_Alice_LLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Alice_LLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_init_ctrl). behavior.Sem (var_init_ctrl)"

end
