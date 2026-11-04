theory def_automaton_Event_gen
  imports def_automaton_Event

begin

fun sb2stream::"EventOutput.channels\<^sup>\<Omega> \<Rightarrow> (bool event stream)" where
"sb2stream a = EventOutput.sbgetter\<cdot>a"

export_code "execsem" "EventInput.sbsetter" "sb2stream" in Scala module_name def_automaton_Event_scalaExec file_prefix "def_automaton_Event_scalaExec" (case_insensitive)

end
