theory code_LambdasAddition
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_LambdasAddition.def_LambdasAddition code_LambdasAddition_Input code_LambdasAddition_Output bundle_LambdasAddition.def_LambdasAddition_Input bundle_LambdasAddition.def_LambdasAddition_Output
    (* Hwl  *)

begin




fun executableExpression_00 :: "unit \<Rightarrow> State \<Rightarrow> nat \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) list" where
"executableExpression_00 () (StateConstr s var_Map) channel_i_val_pattern = [(StateConstr Substate.state__S ((\<lambda> var_i var_j. (var_i + var_j))), [])]"

fun executableTransitionH_00 :: "unit \<Rightarrow> State \<Rightarrow> nat \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) list" where
"executableTransitionH_00 () (StateConstr s var_Map) channel_i_val_pattern =
    (if (guard_00 () (StateConstr s var_Map) channel_i_val_pattern) then (executableExpression_00 () (StateConstr s var_Map) channel_i_val_pattern) else [])"


fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_LambdasAddition_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) list" where
"executableEventTransition para state (channel_i_val, natEVENTConstr channel_i_val_pattern) =
    executableTransitionH_00 para state channel_i_val_pattern"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_LambdasAddition_Output.channels msgWithChan) list) list" where
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



fun sb2stream::"def_LambdasAddition_Output.channels\<^sup>\<Omega> \<Rightarrow> (nat event stream)" where
"sb2stream a = def_LambdasAddition_Output.sbgetter\<cdot>a"

export_code "execsem" "def_LambdasAddition_Input.sbsetter" "sb2stream" in Scala module_name def_LambdasAddition_scalaExec file_prefix "def_LambdasAddition_scalaExec" (case_insensitive)


end
