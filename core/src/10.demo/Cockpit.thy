theory Cockpit

imports stream.EventStream inc.LNat inc.Codegen inc.LNatcodegen stream.StreamCodegen


begin
datatype substate = P1_P2 | P1 | P2 | Eve_threat_deny_entry_call_police | Eve_in_cockpit

instance substate::countable
  by(countable_datatype)


type_synonym eve_threat = bool

datatype state = S substate eve_threat

instance state::countable
  by(countable_datatype)

definition enum_state_def :: "state list" where
"enum_state_def = [S P1_P2 True, S P1_P2 False, S P1 True, S P1 False, S P2 True, S P2 False,
               S Eve_threat_deny_entry_call_police True,  S Eve_threat_deny_entry_call_police False,
               S Eve_in_cockpit True, S Eve_in_cockpit False]"



instantiation state::enum
begin
definition enum_state: "enum_state = enum_state_def"

definition enum_all_state:: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_state P  = list_all P enum_state_def"

definition enum_ex_state:: "(state \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_state P = list_ex P enum_state_def"

instance
  apply (intro_classes)
  unfolding enum_state enum_state_def_def enum_all_state_def enum_ex_state_def
  apply (rule UNIV_eq_I)
     apply simp
     apply (case_tac x; case_tac x1; case_tac x2; simp)
    apply simp
  apply simp
   apply (smt state.exhaust substate.exhaust)
  apply simp
  apply (smt state.exhaust substate.exhaust)
  done
end

datatype action = deny_P1_wants_to_enter_cockpit | 
                  deny_P2_wants_to_enter_cockpit |
                  accept_P1_wants_to_enter_cockpit |
                  accept_P2_wants_to_enter_cockpit |
                  P1_wants_to_exit_cockpit |
                  P2_wants_to_exit_cockpit

instance action::countable
  by(countable_datatype)

definition enum_action_def :: "action list" where
"enum_action_def = [deny_P1_wants_to_enter_cockpit, deny_P2_wants_to_enter_cockpit,
                    accept_P1_wants_to_enter_cockpit, accept_P2_wants_to_enter_cockpit,
                    P1_wants_to_exit_cockpit, P2_wants_to_exit_cockpit]"


instantiation action::enum
begin
definition enum_action: "enum_action = enum_action_def"

definition enum_all_action:: "(action \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_action P  = list_all P enum_action_def"

definition enum_ex_action:: "(action \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_action P = list_ex P enum_action_def"
instance
  apply (intro_classes)
  unfolding enum_action enum_action_def_def enum_all_action_def enum_ex_action_def
     apply (metis (full_types) UNIV_eq_I action.exhaust
      enum_action_def_def list.set_intros(1,2))
  apply simp
  apply (metis (full_types) UNIV_I action.exhaust list_all_simps(1,2))
  by (metis (full_types) UNIV_I action.exhaust list_ex_simps(1,2))
end

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


value "sreachable_nda secure_t ({(S P1_P2 False)}) (<[P1_wants_to_exit_cockpit, accept_P1_wants_to_enter_cockpit]>) "

value "sreachable_nda_all secure_t \<cdot>({(S P1_P2 False)})\<cdot>(<[P1_wants_to_exit_cockpit, accept_P1_wants_to_enter_cockpit]>) "

lemma "S Eve_in_cockpit b \<notin> sreachableStates cockpit_aut\<cdot>input"
  oops

lemma "sreachable_nda secure_t ({(S P1_P2 False)}) (<[P1_wants_to_exit_cockpit, accept_P1_wants_to_enter_cockpit]>) = {state.S Eve_in_cockpit True, state.S P1_P2 False}"
  apply(simp)
  by(subst sreachable_nda_unfold,simp)

lemma step_h[simp]:"(\<And>b. state.S Eve_in_cockpit b \<notin> init) \<Longrightarrow>
       x \<in> init \<Longrightarrow>
       a \<noteq> accept_P1_wants_to_enter_cockpit \<Longrightarrow>
       a \<noteq> accept_P2_wants_to_enter_cockpit \<Longrightarrow>
        state.S Eve_in_cockpit ba \<in> secure_t x a \<Longrightarrow> False"
  apply (cases a; cases x; case_tac x1; case_tac x2;simp)
  done

lemma eve_not_reach_secure:
  assumes "{accept_P1_wants_to_enter_cockpit,accept_P2_wants_to_enter_cockpit} \<inter> sValues\<cdot>input = {}"
  and "\<And>b. S Eve_in_cockpit b \<notin>init"
  shows "S Eve_in_cockpit b \<notin> sreachable_nda_all secure_t\<cdot> init\<cdot> input"
  using assms
proof(induction input arbitrary: init)
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
    by(rule step_h,simp_all)
qed

theorem  assumes "{accept_P1_wants_to_enter_cockpit,accept_P2_wants_to_enter_cockpit} \<inter> sValues\<cdot>input = {}"
  shows "S Eve_in_cockpit b \<notin> sreachableStates cockpit_aut\<cdot>input"
  apply(simp add: sreachableStates_def autInitConfig.rep_eq cockpit_aut.rep_eq autTransition.rep_eq)
  by(rule eve_not_reach_secure,simp_all add: assms)


end