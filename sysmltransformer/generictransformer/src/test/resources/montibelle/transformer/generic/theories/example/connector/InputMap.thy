theory InputMap
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Instance1Input io.Input
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1). (natInChannel_pattern_instantiated_1, bInChannel_pattern_instantiated_1, sInChannel_pattern_instantiated_1)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Instance1Input.channels\<^sup>\<Omega> \<rightarrow> Input.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Input.SB.setter oo connector oo Instance1Input.SB.getter }"


end
