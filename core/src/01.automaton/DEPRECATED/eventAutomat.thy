theory eventAutomat

imports ndAutomaton
begin

datatype ('state::type,'csIn) eventState = EventState 'state "'csIn \<Rightarrow> msg list"


fun getMessages :: "M_timed \<Rightarrow> msg list" where
"getMessages (TOne msg) = [msg]" |

"getMessages (TFin msgs) = msgs" |

"getMessages (Tsyn (Some msg)) = [msg]" |
"getMessages (Tsyn None) = []"




fun eventProcessOne:: "('cs \<Rightarrow>  'msg::type  \<Rightarrow> 'o::type set) \<Rightarrow> ('cs \<Rightarrow> 'msg list)  \<Rightarrow> (('cs \<Rightarrow> 'msg list) \<times> 'o) set" where
"eventProcessOne eventTrans buffers = 
    (let possibleActions = { c | c. buffers c \<noteq> []}
    in
    (if (\<forall>c. buffers c = []) then {(buffers, undefined)} else \<comment> \<open>TODO: undefined = tick... oder dummy message\<close>
  ({ ((\<lambda>cc. if(c=cc) then tl (buffers cc) else buffers cc), userNext) | c userNext. buffers c \<noteq> [] \<and> userNext \<in> eventTrans c (hd (buffers c))})))"


definition sbeGetMsgs:: "'cs sbElem \<Rightarrow> 'cs \<Rightarrow> msg list" where
"sbeGetMsgs sbe c \<equiv> if(chDom (TYPE ('cs)) = {}) then [] else getMessages (the (Rep_sbElem sbe) c)"

definition eventAddToBuf::"'cs sbElem \<Rightarrow> ('cs \<Rightarrow> msg list) \<Rightarrow> 'cs \<Rightarrow> msg list" where
"eventAddToBuf sbe buf c = (buf c) @ (sbeGetMsgs sbe c)"  


fun eventAutomatTransition:: "('state \<Rightarrow> 'in \<Rightarrow> msg \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) 
  \<Rightarrow> (('state::type,'in) eventState \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (((('state::type,'in) eventState) \<times> 'out\<^sup>\<Omega>) set))" where
"eventAutomatTransition eventTrans (EventState s buffers) input = 
   {(EventState nextS nextList, nextOut) | nextS nextList nextOut. 
        (nextList, nextS, nextOut)\<in>(eventProcessOne (eventTrans s) (eventAddToBuf input buffers))
      } "

fun eventAutomatInitConfig::"('state \<times> 'out\<^sup>\<Omega>)set \<Rightarrow>  (('state::type,'in) eventState \<times> 'out\<^sup>\<Omega>) set"where
"eventAutomatInitConfig  S = {(EventState Sub (\<lambda>c. []),out) | Sub out. (Sub,out)\<in>S}"


setup_lifting type_definition_ndAutomaton

lift_definition eventAut :: "('state \<Rightarrow> 'in \<Rightarrow> msg \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>)set \<Rightarrow>
  (('state::type,'in) eventState, 'in::{chan, finite}, 'out::chan) ndAutomaton" is
"\<lambda> eventTrans eventInit. (eventAutomatTransition eventTrans,eventAutomatInitConfig eventInit)"
  oops



(*

(* Begin Framework: *)
datatype timeType = TUntimed | TTimed | TTsyn
(* End Framework *)


(* Begin Generated *)
datatype channel = c1 | c2 | c3

datatype msg = \<N> nat | \<B> bool


fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg c1 = range \<N>"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime c1 = TUntimed" |
"cTime c3 = TTimed"
(* End Generated *)


(* Begin Framework eg Channel/sbElem/SB *)

datatype M_timed = Untimed "msg" | Timed "msg list" | Tsyn "msg option"  (* option = tsyn *)

definition ctype::"channel \<Rightarrow> M_timed set" where
"ctype c \<equiv> if (cMsg c) = {} then {} else 
  case (cTime c) of TUntimed   \<Rightarrow> Untimed ` (cMsg c) | 
                   TTimed     \<Rightarrow>  Timed ` {ls. set ls \<subseteq> (cMsg c)} |
                   TTsyn      \<Rightarrow> Tsyn ` (insert None (Some ` cMsg c))"

lemma ctype_empty_gdw: "ctype c = {} \<longleftrightarrow> cMsg c = {}"
  apply(cases "(cTime c)")
  apply (auto simp add: ctype_def)
  by (metis bot.extremum empty_set)

type_synonym inAnd = bool

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) True = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) False = Cc2 port_c2"

abbreviation "buildAndinSBE \<equiv> inAndChan (Timed o map \<B>) (Untimed o \<N>)" 

abbreviation "buildAndinSBs \<equiv> inAndChan (Tsyn o (map_option \<B>)) (Untimed o \<N>)"

interpretation andInSBE: sbeGen "buildAndinSBE"
  oops



subsection \<open>Merge\<close>

fun eventMT :: "state \<Rightarrow> inMerge \<Rightarrow> ('m\<times>'m)  \<Rightarrow> (state \<times> 'cs\<^sup>\<Omega>) set" where
"eventMT (True, _) cin2 m  = { (s,sendMessageAway (Msg m))}"


definition "eventMerge = eventAut eventMergeTransition"
*)

end
