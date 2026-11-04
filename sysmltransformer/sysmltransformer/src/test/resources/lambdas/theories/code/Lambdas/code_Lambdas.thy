theory code_Lambdas
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Lambdas.def_Lambdas code_Lambdas_Input code_Lambdas_Output bundle_Lambdas.def_Lambdas_Input bundle_Lambdas.def_Lambdas_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s var_Map) channel_i_val_pattern = [(StateConstr Substate.state__S ((\<lambda> var_b. (Not var_b))), [])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> bool \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s var_Map) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_Map) channel_i_val_pattern) then (executableExpression_00 () (StateConstr s var_Map) channel_i_val_pattern) else [])"


fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Lambdas_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_i_val, boolEVENTConstr channel_i_val_pattern) =
    executableTransitionH_00 para state channel_i_val_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_Lambdas_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . []"

global_interpretation executableBehavior:
    eventExecGen
      executableEventTransition
      executableTickTransition
      executableInitialConfigs
      True
      defines execsem = executableBehavior.rndSem
    and laut = executableBehavior.lsaut
    and transition = executableBehavior.transition
    and ndatransition = executableBehavior.ndaTransition
    and eventtransition = executableBehavior.ndaTransition_eventC
    and ticktransition = executableBehavior.ndaTransition_tickC
    and config = executableBehavior.config
    and configC = executableBehavior.ndaInitConfigC
  done



fun sb2stream::"def_Lambdas_Output.channels\<^sup>\<Omega> \<Rightarrow> (bool event stream)" where
"sb2stream a = def_Lambdas_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Lambdas_Input.sbsetter" "sb2stream" in Scala module_name def_Lambdas_scalaExec file_prefix "def_Lambdas_scalaExec" (case_insensitive)


end
