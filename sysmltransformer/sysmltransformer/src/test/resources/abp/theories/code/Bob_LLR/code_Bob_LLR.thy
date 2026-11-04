theory code_Bob_LLR
  imports
    (* Core *) tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) sps_Bob_LLR.def_Bob_LLR sps_Bob_LLR.def_Bob_LLR_States code_Bob_LLR_Input code_Bob_LLR_Output bundle_Bob_LLR.def_Bob_LLR_Input bundle_Bob_LLR.def_Bob_LLR_Output
    (* Hwl  *)

begin


fun executableExpression_0 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableExpression_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = [
    (StateConstr Substate.state__S ((unlift (lift var_ctrl))), (Eps, Eps))
]"

fun executableTransitionH_0 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableTransitionH_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (executableExpression_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else [])"

fun executableExpression_1 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableExpression_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = [
    (StateConstr Substate.state__S ((unlift (tsynSnd channel_input_val_pattern))), ((tsynSnd channel_input_val_pattern), (tsynFst channel_input_val_pattern)))
]"

fun executableTransitionH_1 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableTransitionH_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (executableExpression_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else [])"

fun executableExpression_2 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableExpression_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = [
    (StateConstr Substate.state__S ((unlift (lift var_ctrl))), ((tsynSnd channel_input_val_pattern), Eps))
]"

fun executableTransitionH_2 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableTransitionH_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (executableExpression_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else [])"

definition executableTransition :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableTransition para state input =
    executableTransitionH_0 para state input @
    executableTransitionH_1 para state input @
    executableTransitionH_2 para state input    "

definition executableInitialConfigs :: "(bool) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) list" where
"executableInitialConfigs  \<equiv> \<lambda> (var_init_ctrl) .  []
        "

global_interpretation executableBehavior:
    tsExecStrongGen
      executableTransition
      executableInitialConfigs
      def_Bob_LLR_Input.buildSBE
      def_Bob_LLR_Output.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: def_Bob_LLR_Input.SBE.c_empty def_Bob_LLR_Output.SBE.c_empty)


end
