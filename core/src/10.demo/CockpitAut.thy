theory CockpitAut
imports stream.StreamCodegen
begin


datatype substate = P1_P2 | 
                    P1 | 
                    P2 | 
                    Eve_threat_deny_entry_call_police | 
                    Eve_in_cockpit

type_synonym eve_threat = bool

datatype state = S substate eve_threat


datatype action = deny_P1_wants_to_enter_cockpit | 
                  deny_P2_wants_to_enter_cockpit |
                  accept_P1_wants_to_enter_cockpit |
                  accept_P2_wants_to_enter_cockpit |
                  P1_wants_to_exit_cockpit |
                  P2_wants_to_exit_cockpit

instance action::countable
  by(countable_datatype)


fun secure_t::"state \<Rightarrow> action \<Rightarrow> state set"where
"secure_t (S P1_P2 b) P1_wants_to_exit_cockpit = {(S P2 b),(S P2 (\<not>b))}"|
"secure_t (S P1_P2 b) P2_wants_to_exit_cockpit = {(S P1 b),(S P2 (\<not>b))}"|
"secure_t (S P1_P2 b) _ = {(S P1_P2 b)}"|

"secure_t (S P1 False) accept_P2_wants_to_enter_cockpit = {(S P1_P2 False)}"|
"secure_t (S P1 True) accept_P2_wants_to_enter_cockpit = {(S Eve_in_cockpit True)}"|
"secure_t (S P1 True) deny_P2_wants_to_enter_cockpit = {(S Eve_threat_deny_entry_call_police True)}"|
"secure_t (S P1 b) _ = {(S P1 b)}"|

"secure_t (S P2 False) accept_P1_wants_to_enter_cockpit = {(S P1_P2 False)}"|
"secure_t (S P2 True) accept_P1_wants_to_enter_cockpit = {(S Eve_in_cockpit True)}"|
"secure_t (S P2 True) deny_P1_wants_to_enter_cockpit = {(S Eve_threat_deny_entry_call_police True)}"|
"secure_t (S P2 b) _ = {(S P2 b)}"|
"secure_t (S Eve_threat_deny_entry_call_police b) _ = {(S Eve_threat_deny_entry_call_police True)}" |
"secure_t (S Eve_in_cockpit b) _ = {(S Eve_in_cockpit True)}"


lift_definition cockpit_aut::"(state, action, unit)automaton" is
"((\<lambda> s e. (\<lambda>s. (s,())) ` secure_t s e), {(S P1_P2 False, ())})"
  apply auto
  by(case_tac state; case_tac sbe;case_tac x1; case_tac x2;simp)

lemma eve_not_reachable_helper:
  assumes "{accept_P1_wants_to_enter_cockpit,accept_P2_wants_to_enter_cockpit} \<inter> sValues\<cdot>input = {}"
  and "\<And>b. S Eve_in_cockpit b \<notin>States"
  shows "(S Eve_in_cockpit b) \<notin> sreachable_nda_all secure_t\<cdot> States\<cdot> input"
  using assms
proof(induction input arbitrary: States)
  case adm
  then show ?case
    apply(rule adm_imp,simp)
    apply(rule adm_all)
    apply(rule adm_imp,simp)
    by simp
next
  case bottom
  then show ?case
    by simp
next
  case (step a input)
  then show ?case
    apply (simp add: sreachable_nda_all_unfold)
    apply(subst step.IH,simp_all)
    apply auto
    by(cases a; case_tac x; case_tac x1; case_tac x2;simp)
qed

theorem eve_not_reachable:
  assumes "{accept_P1_wants_to_enter_cockpit,accept_P2_wants_to_enter_cockpit} \<inter> sValues\<cdot>input = {}"
  shows "(S Eve_in_cockpit b) \<notin> sreachableStates cockpit_aut\<cdot>input"
  apply(simp add: sreachableStates_def autInitConfig.rep_eq cockpit_aut.rep_eq autTransition.rep_eq)
  by(rule eve_not_reachable_helper,simp_all add: assms)

end