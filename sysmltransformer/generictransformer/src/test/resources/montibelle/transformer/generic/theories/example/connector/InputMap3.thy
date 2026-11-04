theory InputMap3
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance3Input io.Input
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3). (natInChannel_pattern_instantiated_3, bInChannel_pattern_instantiated_3, sInChannel_pattern_instantiated_3)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Instance3Input.channels\<^sup>\<Omega> \<rightarrow> Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Input.SB.setter oo connector oo Instance3Input.SB.getter }"


end
