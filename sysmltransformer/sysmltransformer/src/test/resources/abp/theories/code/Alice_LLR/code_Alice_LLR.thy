theory code_Alice_LLR
  imports
    (* Core *) tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) sps_Alice_LLR.def_Alice_LLR sps_Alice_LLR.def_Alice_LLR_States code_Alice_LLR_Input code_Alice_LLR_Output bundle_Alice_LLR.def_Alice_LLR_Input bundle_Alice_LLR.def_Alice_LLR_Output
    (* Hwl  *)

begin


fun executableExpression_0 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__SingleBuf ((unlift (lift var_ctrl))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift var_ctrl)))))
]"

fun executableTransitionH_0 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_0 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_1 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__EmptyBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), (Eps))
]"

fun executableTransitionH_1 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_1 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_2 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__EmptyBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
]"

fun executableTransitionH_2 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_2 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_3 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift (Not var_ctrl))))))
]"

fun executableTransitionH_3 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_3 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_4 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedList [channel_input_val_pattern]))), ((liftedPair (channel_input_val_pattern, (lift (Not var_ctrl))))))
]"

fun executableTransitionH_4 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_4 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_5 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__SingleBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
]"

fun executableTransitionH_5 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_5 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_6 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (liftedApplyTwo append (lift var_buffer) (liftedList [channel_input_val_pattern])))), ((liftedPair (channel_input_val_pattern, (lift var_ctrl)))))
]"

fun executableTransitionH_6 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_6 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_7 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (lift var_buffer))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
]"

fun executableTransitionH_7 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_7 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_8 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
]"

fun executableTransitionH_8 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_8 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_9 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__SingleBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyOne tl (lift var_buffer)))), (Eps))
]"

fun executableTransitionH_9 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_9 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_10 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift var_ctrl))) ((unlift (liftedApplyTwo append (lift var_buffer) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (lift var_buffer)), (lift var_ctrl)))))
]"

fun executableTransitionH_10 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_10 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_11 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyTwo append (liftedApplyOne tl (lift var_buffer)) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (liftedApplyOne tl (lift var_buffer))), (lift (Not var_ctrl))))))
]"

fun executableTransitionH_11 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_11 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

fun executableExpression_12 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableExpression_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) = [
    (StateConstr Substate.state__MultiBuf ((unlift (lift (Not var_ctrl)))) ((unlift (liftedApplyTwo append (liftedApplyOne tl (lift var_buffer)) (liftedList [channel_input_val_pattern])))), ((liftedPair ((liftedApplyOne hd (liftedApplyOne tl (lift var_buffer))), (lift (Not var_ctrl))))))
]"

fun executableTransitionH_12 :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransitionH_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern) =
(if (guard_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) then (executableExpression_12 (var_init_ctrl) (StateConstr s var_ctrl var_buffer) (channel_control_val_pattern, channel_input_val_pattern)) else [])"

definition executableTransition :: "(bool) \<Rightarrow> State \<Rightarrow> (bool tsyn \<times> string tsyn) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableTransition para state input =
    executableTransitionH_0 para state input @
    executableTransitionH_1 para state input @
    executableTransitionH_2 para state input @
    executableTransitionH_3 para state input @
    executableTransitionH_4 para state input @
    executableTransitionH_5 para state input @
    executableTransitionH_6 para state input @
    executableTransitionH_7 para state input @
    executableTransitionH_8 para state input @
    executableTransitionH_9 para state input @
    executableTransitionH_10 para state input @
    executableTransitionH_11 para state input @
    executableTransitionH_12 para state input    "

definition executableInitialConfigs :: "(bool) \<Rightarrow> (State \<times> ((string\<times>bool) tsyn)) list" where
"executableInitialConfigs  \<equiv> \<lambda> (var_init_ctrl) .  []
        "

global_interpretation executableBehavior:
    tsExecStrongGen
      executableTransition
      executableInitialConfigs
      def_Alice_LLR_Input.buildSBE
      def_Alice_LLR_Output.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: def_Alice_LLR_Input.SBE.c_empty def_Alice_LLR_Output.SBE.c_empty)


end
