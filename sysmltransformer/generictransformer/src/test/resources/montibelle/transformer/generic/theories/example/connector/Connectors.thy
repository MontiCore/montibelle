theory Connectors
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Connector1Input io.Connector1Output
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1). (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Connector1Input.channels\<^sup>\<Omega> \<rightarrow> Connector1Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Connector1Output.SB.setter oo connector oo Connector1Input.SB.getter }"


end
