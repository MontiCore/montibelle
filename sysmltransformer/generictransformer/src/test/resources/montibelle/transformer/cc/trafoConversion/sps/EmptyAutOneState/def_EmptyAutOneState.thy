theory def_EmptyAutOneState
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) bundle_EmptyAutOneState.def_EmptyAutOneState_Input bundle_EmptyAutOneState.def_EmptyAutOneState_Output def_EmptyAutOneState_States
    (* Hwl  *)

begin





fun eventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_EmptyAutOneState_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_EmptyAutOneState_Output.channels msgWithChan) list) set" where
"eventTransition _ _ _ = {}"

fun tickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_EmptyAutOneState_Output.channels msgWithChan) list) set" where
"tickTransition para state =
 {}"

definition initialConfigs :: "unit \<Rightarrow> (State \<times> (def_EmptyAutOneState_Output.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> () . {}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      False
  apply(unfold_locales)
  done

ML \<open>structure def_EmptyAutOneState = struct
end\<close>

definition Sps :: "unit \<Rightarrow> (def_EmptyAutOneState_Input.channels\<^sup>\<Omega> \<rightarrow> def_EmptyAutOneState_Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). behavior.Sem ()"


end
