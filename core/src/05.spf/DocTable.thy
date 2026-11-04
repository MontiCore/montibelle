theory DocTable
imports SPF SPFComp "HOL-Library.OptionalSugar" "HOL-Library.LaTeXsugar"

begin

type_notation %invisible nat ("\<nat>")
type_notation %invisible lnat ("\<nat>\<^sub>\<infinity>")
type_notation %invisible bool ("\<bool>")
type_notation %invisible stream ("(_\<^sup>\<omega>)"[1000] 999)

   
text \<open>In \cref{table:spfFunctions} the functions over \glspl{spf} are
shown. Notice that these are not all functions. Many functions from
\cref{table:sbFunctions} are also \glspl{spf}. Take for example @{const sbRt}.
It is an continuous function from input bundle to output bundle. Hence it can
be used as a component, especially in combination with the sequential composition
operator.\<close>

text\<open>
\begin{table}
\small
\begin{tabular}{c|c|p{6cm}|l}
\hline
% \toprule
  \multicolumn{1}{c|} {Def} & \multicolumn{1}{c|} {Abbrev} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule
@{const spfType} & & \<open>('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> (channel set\<times>channel set)\<close> & 
  Signature of Component (\ref{sec:spf})\\
\hline
@{const spfDom} & & \<open>('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> channel set\<close> & Input Channels (\ref{sec:spf})\\
\hline
@{const spfRan} & & \<open>('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) itself \<Rightarrow> channel set\<close> & Output Channels (\ref{sec:spf})\\
\hline
@{const spfIO} & & \<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set\<close> & Input/Output behaviour (\ref{sec:spf})\\
\hline
@{const[source] spfEq} & @{const[names_short] SPF.spfeq_abbr} & \<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> bool\<close> & 
Equality of \gls{spf} (\ref{par:spfeq})\\
\hline
@{const spfConvert} & & @{typeof spfConvert} & Type Conversion \\
\hline

@{const spfComp} & @{const spfComp_abbr}& 
\shortstack{\<open>('I1\<^sup>\<Omega>\<rightarrow>'O1\<^sup>\<Omega>)\<rightarrow>('I2\<^sup>\<Omega>\<rightarrow>'O2\<^sup>\<Omega>)\<close>\\
\<open> \<rightarrow>(('I1\<union>'I2)-('O1\<union>'O2))\<^sup>\<Omega>\<close>\\
\<open> \<rightarrow>('O1\<union>'O2)\<^sup>\<Omega>\<close>} & General Composition (\ref{sec:spfcomp}) \\
\cline{2-3}

& @{const spfCompm_abbr}& \shortstack{\<open>('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>)\<close>\\ \<open> \<rightarrow>('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)\<close>\\
\<open> \<rightarrow>('I3\<^sup>\<Omega> \<rightarrow> 'O3\<^sup>\<Omega>)\<close>} & 
\shortstack{Composition with Typecast\\ (\ref{sec:spfcomp})}\\
\hline
@{const spfCompSeq}& & \<open>('In\<^sup>\<Omega>\<rightarrow>'Intern\<^sup>\<Omega>) \<rightarrow> ('Intern\<^sup>\<Omega>\<rightarrow>'Out\<^sup>\<Omega>)
  \<rightarrow> ('In\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>)\<close>& Sequential Composition (\ref{sec:spfcomp})\\
\hline

@{const spfCompPar}& & \<open>('In1\<^sup>\<Omega>\<rightarrow>'Out1\<^sup>\<Omega>) \<rightarrow> ('In2\<^sup>\<Omega>\<rightarrow>'Out2\<^sup>\<Omega>) \<rightarrow> 
  ('In1 \<union> 'In2)\<^sup>\<Omega> \<rightarrow> ('Out1 \<union> 'Out2)\<^sup>\<Omega>\<close>& Parallel Composition\\
\hline

@{const spfCompFeed}& & \<open>('In\<^sup>\<Omega>\<rightarrow>'Out\<^sup>\<Omega>) \<rightarrow> ('In-'Out)\<^sup>\<Omega> \<rightarrow> 'Out\<^sup>\<Omega>\<close>& Feedback Composition\\

\end{tabular}
\caption{Functions for \glspl{spf}}
\label{table:spfFunctions}
\end{table}
\<close>



end
