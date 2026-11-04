theory ndaListLocale

imports ndAutomaton ndaRefine ExecutableAut

begin


locale ndaGenList =
  fixes ndaTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable) list"
      and ndaInitConfig:: "'param \<Rightarrow> ('state \<times> 'out::{chan,finite}\<^sup>\<Omega>) list"
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenin:"sbeGen fin"
      and sbegenout:"sbeGen fout"
begin

definition transitionH::"'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>) list" where
"transitionH p state sbe = map (\<lambda>(s,out). (s,sbeGen.setter fout out))
                              (ndaTransition p state (sbeGen.getter fin sbe))"

definition transition::"'param \<Rightarrow> 'state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) list)" where
"transition param state sbe = map (apsnd sbe2sb) (transitionH param state sbe)"


end


locale ndaWeakGenList =
  fixes ndaTransition::"'param::type \<Rightarrow> 'state::type \<Rightarrow> 'a::countable 
                        \<Rightarrow> ('state\<times>'b::countable) list"
      and ndaInitConfig:: "'param \<Rightarrow> 'state list"
  and fin::"'a::countable \<Rightarrow> 'in::{chan,finite} \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out::{chan,finite} \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

definition initConfig::"'param \<Rightarrow> ('state \<times> 'out::{chan,finite}\<^sup>\<Omega>) list" where
"initConfig param = map (\<lambda>out. (out,\<bottom>)) (ndaInitConfig param)"
end


sublocale ndaWeakGenList \<subseteq> ndaGenList ndaTransition initConfig fin fout
  by (simp add: ndaGenList_def sbegenfin sbegenfout)

context ndaWeakGenList begin


end

end