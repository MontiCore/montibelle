theory DocTable
imports StreamOther "HOL-Library.OptionalSugar" "HOL-Library.LaTeXsugar"

begin

type_notation %invisible nat ("\<nat>")
type_notation %invisible lnat ("\<nat>\<^sub>\<infinity>")
type_notation %invisible bool ("\<bool>")
type_notation %invisible stream ("(_\<^sup>\<omega>)"[1000] 999)

   


text\<open>
\begin{tabular}{c|c|p{4cm}|p{5cm}}
\hline
% \toprule
  \multicolumn{1}{c|} {Notation} & \multicolumn{1}{c|} {Abbreviation} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule

@{const[source]sbot}& @{const[show_abbrevs] sbot} & @{typeof sbot} & empty stream \\
\hline
\hline
@{const[source]lscons}& @{text "m&&s"} & @{typeof lscons} & append first element \\
\hline
\hline
@{const[source] below}& @{const below} & @{typeof Stream.below_stream_inst.below_stream} & prefix relation \\
\hline
\hline
@{const sup'}& @{text "\<up>m"} & @{typeof sup'} & Construct a stream by a single element \\
\hline
\hline
@{const sconc}& @{term[show_types=false] "sconc_abbr s s'"} & @{typeof sconc} & Concatenation of streams \\
\hline
\hline
@{const shd}&  & @{typeof shd} & Retrieve the first element of a stream\\
\hline
@{const srt}&  & @{typeof srt} & stream without its first element \\
\hline
\hline
@{const slookahd}&  & @{typeof slookahd} &  Apply function to head of stream \\
\hline
\hline
@{const[source] list2s}&@{term[show_types=false] "list2s s"} &@{typeof list2s} & Conversion of lists to streams \\
\hline
@{const s2list}& & @{typeof list2s} & Conversion of a stream to a list \\
\hline
\hline
@{const stake}& &@{typeof stake} & retrieves the first \<open>n\<close> elements of a stream \\
\hline
@{const sdrop}& &@{typeof sdrop} & removes the first \<open>n\<close> elements of a stream \\
\hline
\hline
@{const snth} & &@{typeof snth} & element of a stream at position \<open>n\<close> \\
\hline
\hline
@{const sfoot} & &@{typeof sfoot} & last element of a not empty, finite stream \\
\hline
\hline
@{const sValues} & &@{typeof sValues} & values of a stream as a set of messages of type \<open>'a\<close> \\
\hline
\hline
@{const[source] sntimes} & @{term[show_types=false] "sntimes_abbr n s"} &@{typeof sntimes} & Repeat the given stream \<open>n\<close> times \\
\hline
\hline
@{const sinftimes} & @{text "s\<^sup>\<infinity>"} &@{typeof sinftimes} & Concatenate a stream infinitely often to itself \\
\hline
\hline
@{const smap} & &@{typeof smap} & element-wise function application \\
\hline
\hline
@{const sfilter} & @{term[show_types=false] "sfilter_abbr A s"} &@{typeof sfilter} & filtering function \\
\hline
\hline
@{const stakewhile} & &@{typeof stakewhile} & prefix where predicate holds \\
\hline
@{const sdropwhile} & &@{typeof sdropwhile} & drop prefix where predicate holds \\
\hline
\hline
@{const szip} & &@{typeof szip} &zip two streams into one stream \\
\hline
\hline

\end{tabular}\<close>

text\<open>
\begin{tabular}{c|c|p{4cm}|p{5cm}}
\hline
% \toprule
  \multicolumn{1}{c|} {Notation} & \multicolumn{1}{c|} {Abbreviation} & 
  \multicolumn{1}{c|} {Signature} & \multicolumn{1}{c} {Description} \\
\hline
%  \midrule


@{const sprojfst} & &@{typeof sprojfst} & first stream of two zipped streams \\
\hline
@{const sprojsnd} & &@{typeof sprojsnd} & second stream of two zipped streams \\
\hline
\hline
@{const stwbl} & &@{typeof stwbl} & @{const stakewhile} and first violating element \\
\hline
\hline
@{const srtdw} & &@{typeof srtdw} & @{const sdropwhile} and then remove head \\
\hline
\hline
@{const srcdups} & &@{typeof srcdups} & Remove successive duplicate values from stream \\
\hline
\hline
@{const sscanl} & &@{typeof sscanl} & similar to maps, but but also takes the previously generated
output element as additional input \\
\hline
@{const siterate} & &@{typeof siterate} & infinite iteration of function \\
\hline
@{const siterateBlock} & &@{typeof siterateBlock} & alternative definition similar to @{const siterate} \\



\end{tabular}\<close>



end
