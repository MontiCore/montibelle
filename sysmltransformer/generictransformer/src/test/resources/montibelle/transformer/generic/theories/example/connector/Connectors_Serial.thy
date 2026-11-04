theory Connectors_Serial
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Connector2Input io.Connector2Output
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2). (natInChannel_pattern, bInChannel_pattern, sInChannel_pattern, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Connector2Input.channels\<^sup>\<Omega> \<rightarrow> Connector2Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Connector2Output.SB.setter oo connector oo Connector2Input.SB.getter }"


end
