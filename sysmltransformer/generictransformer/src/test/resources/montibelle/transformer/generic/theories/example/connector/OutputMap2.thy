theory OutputMap2
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) io.Output io.Instance2Output
    (* Hwl  *)

begin


lift_definition connector :: "(nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream) \<rightarrow> (nat tsyn stream \<times> bool tsyn stream \<times> string tsyn stream)" is
"\<lambda> (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern). (natOutChannel_pattern, bOutChannel_pattern, sOutChannel_pattern)"
  by(intro cont2cont)

definition Sps :: "unit \<Rightarrow> (Output.channels\<^sup>\<Omega> \<rightarrow> Instance2Output.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> (). { Instance2Output.SB.setter oo connector oo Output.SB.getter }"


end
