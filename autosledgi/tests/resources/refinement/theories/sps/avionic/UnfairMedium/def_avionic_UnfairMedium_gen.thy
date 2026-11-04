theory def_avionic_UnfairMedium_gen
  imports def_avionic_UnfairMedium

begin

fun sb2stream::"def_avionic_UnfairMedium_Output.channels\<^sup>\<Omega> \<Rightarrow> (bool event stream)" where
"sb2stream a = def_avionic_UnfairMedium_Output.sbgetter\<cdot>a"

export_code "execsem" "def_avionic_UnfairMedium_Input.sbsetter" "sb2stream" in Scala module_name def_avionic_UnfairMedium_scalaExec file_prefix "def_avionic_UnfairMedium_scalaExec" (case_insensitive)

end
