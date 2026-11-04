theory DocTable
  imports dAutomaton dAutomaton_comp dAutomaton_causal 
          ndAutomaton "HOL-Library.OptionalSugar" "HOL-Library.LaTeXsugar"

begin

type_notation %invisible nat ("\<nat>")
type_notation %invisible lnat ("\<nat>\<^sub>\<infinity>")
type_notation %invisible bool ("\<bool>")
type_notation %invisible stream ("(_\<^sup>\<omega>)"[1000] 999)

   


text\<open>
\begin{tabular}{c|c|p{5cm}|p{6cm}}
\hline
% \toprule
  \multicolumn{1}{c|} {Notation} & \multicolumn{1}{c|} {Abbreviation} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule

@{const[source] daTransition} &  & @{typeof daTransition} & transition function of automaton \\
\cline{1-3}
 & @{const daNextState} & @{typeof daNextState}& \\
\cline{1-3}
 & @{const daNextOut} & @{typeof daNextOut}& \\
\hline
@{const daInitState} &  & @{typeof daInitState} & initial state of automaton \\
\hline
@{const daInitOut} &  & @{typeof daInitOut} & initial output of automaton \\
\hline
\hline
@{const daStateSem} &  & @{typeof daStateSem} & state semantic of automaton \\
\hline
@{const daSem} & @{term[show_types=false] "\<lbrakk>aut\<rbrakk>\<^sup>d"} & @{typeof daSem} & semantic of automaton \\
\hline
\hline
@{const daComp} &  & @{typeof daComp} & composition of automatons \\
\hline
\hline
@{const daw2das} &  & @{typeof daw2das} & weak automaton to strong automaton \\
\hline
@{const daw2da} &  & @{typeof daw2da} & weak automaton to general automaton \\
\hline
@{const das2da} &  & @{typeof das2da} & strong automaton to general automaton \\
\hline
\hline
@{const dawStateSem} &  & @{typeof dawStateSem} & state semantic of weak automaton \\
\hline
@{const dawSem} &  & @{typeof dawSem} & semantic of weak automaton \\
\hline
@{const dasSem} &  & @{typeof dasSem} & semantic of strong automaton \\

\end{tabular}\<close>


text\<open>
\begin{tabular}{c|c|p{4cm}|p{5cm}}
\hline
% \toprule
  \multicolumn{1}{c|} {Notation} & \multicolumn{1}{c|} {Abbreviation} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule

@{const[source] ndaTransition} &  & @{typeof ndaTransition} & transition function of automaton \\
\hline
@{const ndaInitConfig} &  & @{typeof ndaInitConfig} & initial configuration of automaton \\
\hline
\hline
@{const ndaStateSem} & @{term[show_types=false] "(\<lbrakk>aut\<rbrakk>\<^sup>p) s"} & @{typeof ndaStateSem} & state semantic of automaton \\
\hline
@{const ndaSem} & @{term[show_types=false] "\<lbrakk>aut\<rbrakk>\<^sup>c"} & @{typeof ndaSem} & semantic of automaton \\

\end{tabular}\<close>

end
