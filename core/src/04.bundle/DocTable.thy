theory DocTable
imports SB SBExtend SBFin "HOL-Library.OptionalSugar" "HOL-Library.LaTeXsugar"

begin

type_notation %invisible nat ("\<nat>")
type_notation %invisible bool ("\<bool>")
type_notation %invisible stream ("(_\<^sup>\<omega>)"[1000] 999)
   

text\<open>
\begin{table}[p]
\small
\begin{tabular}{c|c|p{5cm}|l}
\hline
% \toprule
  \multicolumn{1}{c|} {Def} & \multicolumn{1}{c|} {Abbrev} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule

@{const Abs_lsb}& & \<open>('cs \<Rightarrow> M\<^sup>\<omega>) \<Rightarrow> 'cs\<^sup>\<Omega>\<close> & Lift a function to a \Gls{sb} 
  (\ref{ssec:cpo-subtypes}) \\
\hline
@{const Rep_lsb}& & \<open>'cs\<^sup>\<Omega> \<Rightarrow> 'cs \<Rightarrow> M\<^sup>\<omega>\<close> & Inverse Function of \<open>Abs_lsb\<close> \\
\hline
\<open>bottom\<close>&\<open>\<bottom>\<close>&\<open>'cs\<^sup>\<Omega>\<close>& Least stream bundle\\
\hline
@{const chDom}&&\<open>'cs itself \<Rightarrow> channel set\<close>& Domain of the bundle 
  (\ref{par:chan_functions})\\

\hline
@{const sbe2sb}& & \<open>'cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<Omega>\<close> & conversion of @{type sbElem}s 
                                    to \Gls{sb} (\ref{subsub:sbe2sb}) \\

\hline
@{const sbGetCh}& @{const sbgetch_magic_abbr} &  \<open>'cs1 \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> M\<^sup>\<omega>\<close> & Get the stream on a channel \\
\cline{2-3}
 & @{const sbgetch_abbr}&  \<open>'cs \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> M\<^sup>\<omega>\<close> & (\ref{subsub:sbgetch})\\
\hline
@{const sbIsLeast}& & \<open>'cs\<^sup>\<Omega> \<Rightarrow> \<B>\<close> & True iff an empty stream exists\\
\hline
\<open>sbEQ\<close>&@{const sbeq_abbr} &\<open>'cs1\<^sup>\<Omega> \<Rightarrow> 'cs2\<^sup>\<Omega> \<Rightarrow> bool\<close> & Equality of bundles (\cref{par:bundleeq}) \\
\hline
@{const sbConc}&@{const sbConc_abbr} &\<open>'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & 
Concatenation of bundles (\ref{subsub:sbconc})\\
\hline
@{const sbECons}&@{const sbECons} &\<open>'cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & 
  Concatenation with @{type sbElem} (\ref{subsub:sbeconc})\\

\hline
@{const sbDrop}& &\<open>\<nat> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & drops the first \<open>n\<close> elements (\ref{subsub:sbdrop})\\
\hline
 @{const sbRt} && \<open>'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> &  drops the first element\\
\hline
@{const sbTake}& &\<open>\<nat> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & takes the first \<open>n\<close> elements (\ref{subsub:sbtake})\\
\hline
@{const sbHd} & & \<open>'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> &  takes the first element\\
\hline
@{const[show_abbrevs=false] sbHdElem}& @{term[show_types=false] "sbHdElem_abbr sb"} &\<open>'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<surd>\<close> & 
                      first element as a @{type sbElem}\\
\hline
@{const sbTypeCast}&@{term[show_types=false] "sbTypeCast_abbr sb"} &\<open>'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>\<close> & 
                                              Type Conversion \\
\cline{2-3}
 & @{term[show_types=false] "sbrestrict_abbr_fst sb"}& \<open>('cs1 \<union> 'cs2)\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>\<close> & 
  (\ref{subsub:sbtypecast})\\
\cline{2-3}
 & @{term[show_types=false] "sbrestrict_abbr_snd sb"}& \<open>('cs1 \<union> 'cs2)\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>\<close> &  \\
\cline{2-3}
 & @{term[show_types=false] "sbrestrict_abbr_commu sb"}& \shortstack{\<open>('cs1 \<union> 'cs2)\<^sup>\<Omega>\<close>\\ \<open>\<rightarrow> ('cs2 \<union> 'cs1)\<^sup>\<Omega>\<close>} &  \\
\cline{2-3}
 & @{term[show_types=false] "sbrestrict_abbr_minus sb"}& \<open>'cs1\<^sup>\<Omega> \<rightarrow> ('cs1 - 'cs2)\<^sup>\<Omega>\<close> &  \\
\cline{2-3}
 & @{theory_text "sb \<bar> _"}& \<open>'cs1\<^sup>\<Omega> \<Rightarrow> 'cs3 itself \<Rightarrow> 'cs3\<^sup>\<Omega>\<close> & \\

\hline
@{const sbUnion}& @{const sbUnion_abbr} &\shortstack{\<open>'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega>\<close>\\\<open> \<rightarrow> ('cs1 \<union> 'cs2)\<^sup>\<Omega>\<close>} 
  & merges two \gls{sb} together\\
\cline{2-3}
 & @{const sbUnion_magic_abbr}& \<open>'cs1\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs3\<^sup>\<Omega>\<close>  &  
  (\ref{subsub:sbunion})\\
\cline{2-3}
 & @{const sbUnion_minus_abbr}& \<open>('cs1-'cs2)\<^sup>\<Omega> \<rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>\<close>  &  \\
\hline
@{const sbRenameCh}& &\<open>('cs1 \<Rightarrow> 'cs2) \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>\<close> & 
  renaming channels of a \gls{sb} (\ref{subsub:sbrenamech})\\
\hline
@{const sbRename_part}& &\<open>('cs1 \<rightharpoonup> 'cs2) \<Rightarrow> 'cs2\<^sup>\<Omega> \<rightarrow> 'cs1\<^sup>\<Omega>\<close> & 
  renaming channels of a \gls{sb} (\ref{subsub:sbrenamech})\\

\hline
@{const sbSetCh}& &\<open>'cs \<Rightarrow> M\<^sup>\<omega> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & Overwrite channel \\

\hline
@{const sbNTimes}& &\<open>\<nat> \<Rightarrow> 'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>\<close> & Iterate each stream n-times \\

\hline
@{const sbInfTimes}& &\<open>'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>\<close> & Iterate each stream \<open>\<infinity>\<close>-times \\

\hline
@{const sbFilter}& &\<open>M set \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & Apply filter to each stream \\

\hline
@{const sbTakeWhile}& &\<open>(M \<Rightarrow> bool) \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & Prefix while predicate holds \\

\hline
@{const sbDropWhile}& &\<open>(M \<Rightarrow> bool) \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & Drop while predicate holds \\

\hline
@{const sbRcdups}& &\<open>'cs\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>\<close> & Remove successive duplicates \\
\end{tabular}
\caption{Functions for \glspl{sb}}
\label{table:sbFunctions}
\end{table}\<close>



end
