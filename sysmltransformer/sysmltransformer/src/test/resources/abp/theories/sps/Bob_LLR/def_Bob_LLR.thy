theory def_Bob_LLR
  imports
    (* Core *) tscomponent.TsLocale tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) bundle_Bob_LLR.def_Bob_LLR_Input bundle_Bob_LLR.def_Bob_LLR_Output def_Bob_LLR_States
    (* Hwl  *)

begin

fun liftedPair :: "('a::type tsyn \<times> 'b::type tsyn) \<Rightarrow> ('a \<times> 'b) tsyn" where
"liftedPair (TSynMsg a, TSynMsg b) = TSynMsg (a, b)" |
"liftedPair _                      = Eps"

fun liftedList :: "'a::type tsyn list \<Rightarrow> 'a list tsyn" where
"liftedList []                = TSynMsg []" |
"liftedList (Eps # _)         = Eps" |
"liftedList (TSynMsg a # as)  = liftedApplyTwo Cons (TSynMsg a) (liftedList as)"


fun guard_0 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> bool" where
"guard_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = (s = Substate.state__S \<and> ((toBool (liftedEq (channel_input_val_pattern) (Eps)))))"

fun expression_0 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"expression_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = {
    (StateConstr Substate.state__S ((unlift (lift var_ctrl))), (Eps, Eps))
}"

fun transitionH_0 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"transitionH_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (expression_0 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else {})"

fun guard_1 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> bool" where
"guard_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = (s = Substate.state__S \<and> ((toBool (liftedEq ((tsynSnd channel_input_val_pattern)) ((lift var_ctrl))))))"

fun expression_1 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"expression_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = {
    (StateConstr Substate.state__S ((unlift (tsynSnd channel_input_val_pattern))), ((tsynSnd channel_input_val_pattern), (tsynFst channel_input_val_pattern)))
}"

fun transitionH_1 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"transitionH_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (expression_1 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else {})"

fun guard_2 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> bool" where
"guard_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = (s = Substate.state__S \<and> ((toBool (liftedNot (liftedEq ((tsynSnd channel_input_val_pattern)) ((lift var_ctrl)))))))"

fun expression_2 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"expression_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) = {
    (StateConstr Substate.state__S ((unlift (lift var_ctrl))), ((tsynSnd channel_input_val_pattern), Eps))
}"

fun transitionH_2 :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"transitionH_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern) =
(if (guard_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) then (expression_2 (var_init_ctrl) (StateConstr s var_ctrl) (channel_input_val_pattern)) else {})"



definition transition :: "(bool) \<Rightarrow> State \<Rightarrow> ((string\<times>bool) tsyn) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"transition para state input =
    transitionH_0 para state input \<union>
    transitionH_1 para state input \<union>
    transitionH_2 para state input"

definition initialConfigs :: "(bool) \<Rightarrow> (State \<times> (bool tsyn \<times> string tsyn)) set" where
"initialConfigs  \<equiv> \<lambda> (var_init_ctrl) .  {}"

interpretation behavior:
    tsStrongGen
      transition
      initialConfigs
      def_Bob_LLR_Input.buildSBE
      def_Bob_LLR_Output.buildSBE
  by%visible(unfold_locales; simp_all add: def_Bob_LLR_Input.SBE.c_empty def_Bob_LLR_Output.SBE.c_empty)

ML \<open>structure def_Bob_LLR = struct
  val transitionList  = [
    ("line 19 to 27", @{term guard_0}, @{term expression_0}, @{term transitionH_0}),
    ("line 29 to 37", @{term guard_1}, @{term expression_1}, @{term transitionH_1}),
    ("line 39 to 47", @{term guard_2}, @{term expression_2}, @{term transitionH_2})]
end\<close>

definition Sps :: "(bool) \<Rightarrow> (def_Bob_LLR_Input.channels\<^sup>\<Omega> \<rightarrow> def_Bob_LLR_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (var_init_ctrl). behavior.Sem (var_init_ctrl)"

end
