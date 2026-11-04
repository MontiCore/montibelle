theory Connectors_Feedback
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Connector3Input io.Connector3Output
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream \<times> nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3). (natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3, natOutChannel_pattern_instantiated_1, bOutChannel_pattern_instantiated_1, sOutChannel_pattern_instantiated_1, natOutChannel_pattern_instantiated_2, bOutChannel_pattern_instantiated_2, sOutChannel_pattern_instantiated_2, natOutChannel_pattern_instantiated_3, bOutChannel_pattern_instantiated_3, sOutChannel_pattern_instantiated_3)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Connector3Input.channels\<^sup>\<Omega> \<rightarrow> Connector3Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Connector3Output.SB.setter oo connector oo Connector3Input.SB.getter }"


end
