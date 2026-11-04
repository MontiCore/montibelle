theory AddInputChannelToEmptyComponent

imports bundle.SB automaton_testing.AddChannel

begin

typedef emptyChan = "{CH undefined undefined {}}"
  by simp

typedef addedChan = "{CH ''c1'' TUntimed (range NAT)}"
  by simp

typedef outputChan = "{CH ''cOut'' TUntimed (range COLOR)}"
  by simp

instantiation outputChan :: chan
begin
instance
  apply(intro_classes)
    sorry
end
definition "outputChan msg = undefined"

fun transitionEmptyInputAut::"colors \<Rightarrow> unit \<Rightarrow> (colors \<times> outputChan\<^sup>\<Omega>) set" where
"transitionEmptyInputAut ColRed _     = {(ColRed, outputChan ColRed), (ColYellow, outputChan ColYellow)}" |
"transitionEmptyInputAut ColYellow _  = {(ColRed, outputChan ColRed), (ColYellow, outputChan ColYellow), (ColGreen, outputChan ColGreen)}"|
"transitionEmptyInputAut ColGreen _   = {(ColYellow, outputChan ColYellow), (ColGreen, outputChan ColGreen)}"

lift_definition emptyInputAut::"(colors, unit, outputChan\<^sup>\<Omega>) automaton" is
"(transitionEmptyInputAut, {(ColRed, \<bottom>)})"
  apply simp
  sorry



fun transitionAddInputAut::"colors \<Rightarrow> bool \<Rightarrow> (colors \<times> outputChan\<^sup>\<Omega>) set" where
"transitionAddInputAut ColRed False     = {(ColRed, outputChan ColRed)}" |
"transitionAddInputAut ColRed True     = {(ColYellow, outputChan ColYellow)}" |
"transitionAddInputAut ColYellow _  = {(ColRed, outputChan ColRed), (ColYellow, outputChan ColYellow), (ColGreen, outputChan ColGreen)}"|
"transitionAddInputAut ColGreen _   = {(ColYellow, outputChan ColYellow), (ColGreen, outputChan ColGreen)}"

lift_definition boolInputAut::"(colors, bool, outputChan\<^sup>\<Omega>) automaton" is
"(transitionAddInputAut, {(ColRed, \<bottom>)})"
  apply simp
  sorry


end