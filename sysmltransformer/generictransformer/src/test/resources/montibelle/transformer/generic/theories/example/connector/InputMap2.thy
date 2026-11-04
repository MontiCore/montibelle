theory InputMap2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance2Input io.Input
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2). (natInChannel_pattern_instantiated_2, bInChannel_pattern_instantiated_2, sInChannel_pattern_instantiated_2)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Instance2Input.channels\<^sup>\<Omega> \<rightarrow> Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Input.SB.setter oo connector oo Instance2Input.SB.getter }"


end
