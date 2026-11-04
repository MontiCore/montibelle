theory code_Bob_LLR
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) sps_Bob_LLR.def_Bob_LLR code_Bob_HLR.code_Bob_HLR_Input code_Bob_HLR.code_Bob_HLR_Output bundle_Bob_HLR.def_Bob_HLR_Input bundle_Bob_HLR.def_Bob_HLR_Output
    (* Hwl  *)

begin





fun executableEventTransition :: "unit \<Rightarrow> State \<Rightarrow> (def_Bob_HLR_Input.channels \<times> msg) \<Rightarrow> (State \<times> (def_Bob_HLR_Output.channels msgWithChan) list) list" where
"executableEventTransition _ _ _ = []"

fun executableTickTransition :: "unit \<Rightarrow> State \<Rightarrow> (State \<times> (def_Bob_HLR_Output.channels msgWithChan) list) list" where
"executableTickTransition para state =
 []"

definition executableInitialConfigs :: "unit \<Rightarrow> (State \<times> (def_Bob_HLR_Output.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> () . [(StateConstr Substate.state__Send (var_init_ctrl), [])]"

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



fun sb2stream::"def_Bob_HLR_Output.channels\<^sup>\<Omega> \<Rightarrow> (bool tsyn stream \<times> nat tsyn stream)" where
"sb2stream a = def_Bob_HLR_Output.sbgetter\<cdot>a"

export_code "execsem" "def_Bob_HLR_Input.sbsetter" "sb2stream" in Scala module_name def_Bob_LLR_scalaExec file_prefix "def_Bob_LLR_scalaExec" (case_insensitive)


end
