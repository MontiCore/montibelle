theory DocTable
imports SPS SPSComp SPSIO "HOL-Library.OptionalSugar" "HOL-Library.LaTeXsugar"

begin

type_notation %invisible nat ("\<nat>")
type_notation %invisible lnat ("\<nat>\<^sub>\<infinity>")
type_notation %invisible bool ("\<bool>")
type_notation %invisible stream ("(_\<^sup>\<omega>)"[1000] 999)

text\<open>
\begin{table}
\small
\begin{tabular}{c|c|p{5cm}|p{4.5cm}}
\hline
% \toprule
  \multicolumn{1}{c|} {Notation} & \multicolumn{1}{c|} {Abbrev} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule

@{const[source] empty} & \<open>{}\<close> & @{typeof empty} & Empty Component\\
\hline
@{const[source] UNIV} & \<open>\<close> & @{typeof UNIV} & Greatest Component\\
\hline

\<open>member\<close> & \<open>\<in>\<close> & @{typeof Set.member} & check if SPF is member\\
\hline
@{const[source] union} & \<open>\<union>\<close> & @{typeof union} & Union over Sets\\
\hline
@{const[source] inter} & \<open>\<inter>\<close> & @{typeof inter} & Intersection over Sets\\
\hline
@{const[source] image} & \<open>`\<close> & @{typeof image} & Apply function to every element\\
\hline

@{const spsIO} & & \<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set\<close> & Behaviour Relation \\
\hline
@{const spsIOtoSet} & & \<open>('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set\<close> & Get complete SPS from I/O behaviour \\
\hline
@{const spsComplete} & & @{typeof spsComplete} & Greatest SPS with same behaviour (\ref{sec:spscomplete}) \\
\hline
@{const[source] spsComp} & \<open>\<Otimes>\<close> & 
\<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> ((('I1\<union>'I2)-('O1\<union>'O2))\<^sup>\<Omega> \<rightarrow>('O1\<union>'O2)\<^sup>\<Omega>) set\<close> &  
  \shortstack{General Composition \\(\ref{sec:spscomp})}\\
\hline
@{const spsCompSeq} & & \<open>('In\<^sup>\<Omega> \<rightarrow> 'Intern\<^sup>\<Omega>) set \<Rightarrow> ('Intern\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set 
    \<Rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>) set\<close> & Sequential Composition (\ref{sec:spscompseq})\\
\hline
@{const spsCompPar} & & \<open>('In1\<^sup>\<Omega> \<rightarrow> 'Out1\<^sup>\<Omega>)set \<Rightarrow> ('In2\<^sup>\<Omega> \<rightarrow> 'Out2\<^sup>\<Omega>)set \<Rightarrow> 
  (('In1 \<union> 'In2)\<^sup>\<Omega> \<rightarrow> ('Out1 \<union> 'Out2)\<^sup>\<Omega>) set\<close> & Parallel Composition\\
\hline
@{const spsCompFeed} & & \<open>('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set \<Rightarrow> (('In-'Out)\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)set\<close> & Feedback Composition\\
\hline

@{const spsIsConsistent} & & \<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> \<B>\<close> & Set is not empty\\
\hline
@{const spsIsComplete} & & \<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> \<B>\<close> & Component is complete (\ref{sec:spscomplete})\\
\end{tabular}
\caption{Functions for \glspl{sps}}
\label{table:spsFunctions}
\end{table}\<close>


end
