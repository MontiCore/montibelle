theory Channel

imports HOLCF user.Datatypes inc.TSynDatatype inc.EventDatatype inc.TOneDatatype
begin

default_sort type
                                    text\<open>\label{sec:prelim}\<close>

text\<open>Building on the case-study specific datatypes and the 
@{type timeType}, this section introduces the global message and 
domain types used in the framework. In the end two possibilities 
for connecting domain types are introduced.\<close>

                                              text\<open>\label{sub:gmt}\<close>

text\<open>Depending on the time model, we allow to transmit slightly 
different versions of @{type msg} messages. In every time slot of 
the synchronous time model, every channel transmits at most one 
message. But in every time slot of the general timed model, it is 
possible to transmit an arbitrary high, but finite number of 
messages. To allow the usage of both models and also the untimed
model, we introduce the M datatype:\<close>

datatype M_timed = Tsyn  "msg tsyn"  | 
                   TOne  "msg tone"  |
                   TLive "msg event" |
                   TFin  "msg list"

datatype M = Untimed "msg" | 
             Timed   "M_timed"
                   
instantiation M_timed:: discrete_cpo 
begin

definition "((\<sqsubseteq>) :: M_timed \<Rightarrow> M_timed \<Rightarrow> bool) = (=)"
                       
instance
  by standard (simp add: below_M_timed_def)
end

instantiation M_timed:: tlen
begin
  fun tlen_M_timed::"M_timed \<Rightarrow> lnat" where
  "tlen_M_timed (TLive m) = #\<^sub>\<surd> m" |
  "tlen_M_timed _         = 1" 

instance 
  apply(intro_classes)
   apply (simp add: cont2mono)
  apply(rule exI[where x="TFin []"], simp add: lnzero_def one_def)
  done
end

instantiation M:: discrete_cpo 
begin

definition "((\<sqsubseteq>) :: M \<Rightarrow> M \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_M_def)
end

instantiation M::tlen
begin
fun tlen_M::"M \<Rightarrow> lnat" where
"tlen_M (Untimed x) = undefined"|
"tlen_M (Timed x) = #\<^sub>\<surd>x"

instance
  apply(intro_classes)
  apply(simp add: cont2mono)
  by (metis tlen_M.simps(2) tlent)
end

datatype 'a myself = DUMMY

text\<open>We interpret the messages in a time slot of a time model as:
  \<^item> exactly one message, for the untimed model
  \<^item> either one message or no message at all, for the synchronous 
    time model
  \<^item> a finite list of messages, for the timed model



Assuming a the pure message type would be \<open>nat\<close>, a slot in the 
different time models could look like:
 \<^item> \<open>Untimed 3\<close> in the untimed case 
 \<^item> \<open>Tsyn None\<close> or \<open>Tsyn Some 3\<close> in the time synchronous case
 \<^item> \<open>Timed [1,2,3,\<dots>]\<close> or \<open>Timed []\<close> and in the timed case\<close>




lemma inj_timed[simp]: "inj Timed"
  by (simp add: inj_def)

lemma inj_tsyn[simp]: "inj Tsyn"
  by (simp add: inj_def)

lemma inj_event[simp]: "inj EventMsg"
  by (simp add: inj_def)

lemma inj_tlive[simp]: "inj TLive"
  by (simp add: inj_def)

lemma inj_tsyncons[simp]:"inj f \<Longrightarrow> inj ((Timed o Tsyn) o (map_tsyn) f)"
  apply(rule inj_compose)+
  by (auto simp add: tsyn.inj_map)

lemma inj_eventcons[simp]:"inj f \<Longrightarrow> inj ((Timed o TLive) o (map_event) f)"
  apply(rule inj_compose)+
  by (auto simp add: event.inj_map)

lemma inj_tone[simp]: "inj TOne"
  by (simp add: inj_def)

lemma inj_tonetimed[simp]:"inj (Timed o TOne)"
  by(simp add: inj_def)

lemma inj_tonecons[simp]:"inj f \<Longrightarrow> inj ((Timed o TOne) o f)"
  by (simp add: inj_def)

lemma inj_tfin[simp]: "inj TFin"
  by (simp add: inj_def)

lemma inj_tfincons[simp]:"inj f \<Longrightarrow> inj ((Timed o TFin) o map f)"
  by (simp add: inj_def)

lemma inj_untimed[simp]: "inj Untimed"
  by (simp add: inj_def)

lemma inj_untimedcons[simp]:"inj f \<Longrightarrow> inj (Untimed o f)"
  by(simp add: inj_compose)

instance M_timed::countable
  by(countable_datatype)

instance M::countable
  by(countable_datatype)

definition ctype::"channel \<Rightarrow> M set" where
"ctype c \<equiv> if cMsg c = {} then {} else case cTime c of 
                 TUntimed  \<Rightarrow> Untimed ` (cMsg c) |
                 TTOne     \<Rightarrow> (Timed o TOne) ` (TOneMsg ` cMsg  c) | 
                 TTFin     \<Rightarrow> (Timed o TFin) ` {ls. set ls \<subseteq> (cMsg c)} |
                 TTLive    \<Rightarrow> (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg c)) ) |
                 TTsyn     \<Rightarrow> (Timed o Tsyn) ` ({Eps} \<union> (TSynMsg ` (cMsg c)) ) "       
               

text\<open>This is exactly what @{const ctype} does. It then checks the 
timing of a channel and then returns the respectively correct set of 
timeslot messages, where the pure messages depend on @{const cMsg}.
  \<^item> Untimed channels can send any message from @{const cMsg}
  \<^item> Time synchronous channels can send one message from 
    @{const cMsg} or "no message", represented by @{const None}
  \<^item> Timed channels can send finite lists, where every list element 
    is in @{const cMsg}


Because channels without any allowed transmitted messages are 
interpreted as no channel at all, their @{const ctype} is defined as 
empty. Hence, the following theorem holds.\<close>

theorem ctype_empty_iff: "ctype c = {} \<longleftrightarrow> cMsg c = {}"
  apply(cases "(cTime c)")
  apply (auto simp add: ctype_def)[5]
  by (metis bot.extremum empty_set)

text\<open>And in conclusion there always exists a channel with an empty
@{const ctype}.\<close>

theorem ctypeempty_ex: "\<exists>c. ctype c = {}"
  by (simp add: cmsgempty_ex ctype_empty_iff)



                                        text\<open>\label{sub:chan}\<close>

text\<open>In this section we restrict the possible domains of components
through the usage of classes. The main idea is to never construct a 
component which has channels with an empty @{const ctype} and 
channels with non-empty @{const ctype} simultaneously \cref{fig:componentex}.
The domain of such a component would be equivalent to all its 
channels with non-empty @{const ctype}. This restriction is easily 
achievable by introducing a class which only allows specific subsets
of the global channel type. Furthermore, all types for this class 
will have a domain which excludes all channels with an empty 
@{const ctype}.\<close>



paragraph \<open>Preliminaries for Domain Classes \\\<close>

text\<open>For understandable assumptions in our classes we first define 
the channel set, that contains all channels with an empty 
@{const ctype}.\<close>

definition cEmpty :: "channel set" where
"cEmpty = {c. ctype c = {}}"

text \<open>@{const cEmpty} contains all channels on which no message is 
allowed to be transmitted.\<close> 

lemma cempty_exists: "cEmpty \<noteq> {}"
  by(simp add: cEmpty_def ctypeempty_ex)

paragraph\<open>Classes \\\<close>


class rep =
  fixes Rep :: "'a::type \<Rightarrow> channel"
  fixes Abs :: "channel \<Rightarrow> 'a"
  fixes chanDom::"'a myself \<Rightarrow> channel set"
  assumes abs_rep_id[simp]:"Abs (Rep a) = a"
begin end

text\<open>The following class restricts the mapping from the 
@{class rep} class to be injective and to also comply with our main
idea. Through its injectivity, the type is isomorphic to a subset of
our @{type channel} type.\<close>

class chan = rep +
  assumes chanDom :"chanDom (a::'a::type myself) = range (Rep::'a \<Rightarrow> channel) - cEmpty"
  assumes chan_botsingle:
      "range Rep \<subseteq> cEmpty \<or>
       range Rep \<inter> cEmpty = {}" 
 
begin
 
end

text\<open> With @{const Rep} we require a representation function, that 
maps a type of @{class chan} to the @{type channel} type. The first 
class assumption ensures our channel separation and the second the 
injectivity. Furthermore, our abstraction function @{const Abs} is 
the inverse of @{const Rep}. An overview for possible types from 
class @{class chan} is in \cref{fig:chan}. Domain types \<open>'cs1\<close> and
\<open>'cs2\<close> are in class @{class chan} but \<open>'cs3\<close> is not, because it 
contains channels with an empty and non-empty @{const ctype}.\<close>


paragraph \<open>Class Functions \\\<close>
text\<open>We will now define a function for types of @{class chan}. It 
returns the Domain of the type. As a result of our class assumptions 
and of interpreting empty channels as non existing, our domain is 
empty, if and only if the input type contains channel(s) from 
@{const cEmpty}. A type can be defined as the input of a function by
using \<open>itself\<close> type in the signature. Then, input 
\<open>chDom TYPE ('cs)\<close> results in the domain of \<open>'cs\<close>.\<close>

definition chDom::"'cs::chan itself \<Rightarrow> channel set" where
"chDom a \<equiv> range (Rep::'cs \<Rightarrow> channel) - cEmpty"

lemma chandomchdomeq:
  "chanDom (DUMMY::'a myself)= chDom TYPE('a::chan)"
  by(simp add: chDom_def chanDom)

text\<open>The following abbreviation checks, if a type of @{class chan} 
is empty.\<close>

abbreviation chDomEmpty ::"'cs::chan itself \<Rightarrow> bool" where
"chDomEmpty cs \<equiv> chDom cs = {}"

lemma rEpsubsetcemtpy: 
  assumes"chDom TYPE ('cs::chan) = {}"
  shows "range (Rep::'cs \<Rightarrow> channel) \<subseteq> cEmpty"
  using chDom_def assms cEmpty_def by auto

lemma inchdom[simp]:"\<not>chDomEmpty TYPE('cs) 
                     \<Longrightarrow> Rep (c::'cs::chan) \<in> chDom TYPE('cs)"
  apply(simp add: chDom_def)
  using chan_botsingle by blast

lemma dom2ctypeempty[simp]:"chDomEmpty TYPE('cs) 
                     \<Longrightarrow> ctype (Rep (c::'cs::chan)) = {}"
  by(auto simp add: chDom_def cEmpty_def) 

lemma dom2ctypenempty[simp]:"\<not>chDomEmpty TYPE('cs) 
                     \<Longrightarrow> ctype (Rep (c::'cs::chan)) \<noteq> {}"
  apply(auto simp add: chDom_def)[1]
  using chan_botsingle by (auto simp add: cEmpty_def)

lemma empty_msg[simp]: 
"chDom TYPE('chan::{chan, countable}) \<noteq> {} \<Longrightarrow> cMsg (Rep (c::'chan)) \<noteq> {}"
  by (metis ctype_empty_iff dom2ctypenempty)

text \<open>As mentioned before, types of @{class chan} can be interpreted 
as a subset of @{type channel}s, where on every channel either no 
message can be transmitted, or on every channel some message is 
allowed to be transmitted. The properties provided by the framework
do use domain assumptions for some properties. The @{class chan} 
class can also be divided in two sub classes that automatically 
fulfill domain assumptions. Then, many properties of the framework 
hold immediately without proofing assumptions.
This is useful for case-studies because the automatic prover tools 
can find and use applicable properties easier. Thus, two classes 
dividing the @{class chan} class are defined.\<close>

paragraph\<open>Class somechan \\\<close>


class somechan = rep +
  assumes chandom :"chanDom (a::'a myself) = range (Rep::'a \<Rightarrow> channel) - cEmpty"
  assumes chan_notempty: "(range Rep) \<inter> cEmpty = {}"
begin end

text\<open>The class @{class somechan} is a subclass of class 
@{class chan}.\<close>

subclass (in somechan) chan
  apply(standard)
  by (simp_all add:local.chandom local.chan_notempty)

lemma somechannotempty[simp]:"\<not>chDomEmpty TYPE('c::somechan)"
  using chDom_def somechan_class.chan_notempty by fastforce

lemma somechandom:"chDom(TYPE('c::somechan)) 
                   = range(Rep::'c\<Rightarrow>channel)"
  by(simp add: chDom_def somechan_class.chan_notempty Diff_triv)

lemma [code_abbrev]: "chanDom (DUMMY::('a::chan) myself) = chDom TYPE('a)"
  by(simp add: chDom_def chanDom)
  
text\<open> Hence, we know @{thm somechannotempty} and 
@{thm somechandom}.\<close>

paragraph\<open>Class emptychan \\\<close>


class emptychan = rep +
  assumes chandom :"chanDom (a::'a myself) = range (Rep::'a \<Rightarrow> channel) - cEmpty"
  assumes chan_empty:"(range Rep) \<subseteq> cEmpty" 
begin end

text\<open>Analogous to class @{class somechan}, also class 
@{class emptychan} is a subclass of class @{class chan}.\<close>

subclass (in emptychan) chan
  apply(standard)
  by (simp_all add: local.chandom local.chan_empty)


theorem emptychanempty[simp]:"chDomEmpty TYPE('cs::emptychan)"
  by (simp add: chDom_def emptychan_class.chan_empty)

text\<open>In the following chapters, a "domain" is defined by 
@{const chDom} of a type and domain types are types of class 
@{class chan}, because each type of class @{class chan} corresponds
to a specific domain.\<close>

lemma emptychan_type[simp]: "ctype (Rep (c::('cs::emptychan))) = {}"
  using chan_empty cEmpty_def by auto

class tchan = chan +
  assumes tchan_ctime:"\<And>c. Rep c \<in>chDom TYPE('a::chan) \<Longrightarrow> cTime (Rep c) \<noteq> TUntimed"
begin

lemma sometschan[simp]:assumes"chDom TYPE('a) \<noteq> {}"
  shows"cTime (Rep c) \<noteq> TUntimed"
  by (simp add: assms local.tchan_ctime)

end

class tschan = chan +
  assumes tschan_ctime:"\<And>c. Rep c \<in>chDom TYPE('a::chan) \<Longrightarrow> (cTime (Rep c) = TTOne \<or> cTime (Rep c) = TTsyn \<or> 
               cTime (Rep c) = TTFin)"
begin

lemma sometschan[simp]:assumes"chDom TYPE('a) \<noteq> {}"
  shows"(cTime (Rep c) = TTOne \<or> cTime (Rep c) = TTsyn \<or> 
               cTime (Rep c) = TTFin)"
  by (simp add: assms local.tschan_ctime)

end

subclass (in tschan) tchan
  apply(standard)
  by (metis local.tschan_ctime timeType.distinct(1,3,7))

class echan = chan +
  assumes echan_ctime[simp]:"\<And>c. Rep c \<in>chDom TYPE('a::chan) \<Longrightarrow> cTime (Rep c) = TTLive"
begin

lemma sometschan[simp]:assumes"chDom TYPE('a) \<noteq> {}"
  shows"cTime (Rep (c::'a)) = TTLive"
  by (simp add: assms)

end

subclass (in echan) tchan
  apply(standard)
  by (simp)


class uchan = chan +
  assumes uchan_ctime:"\<And>c. Rep c \<in> chDom TYPE('a::chan) \<Longrightarrow> cTime (Rep c) = TUntimed"
begin

lemma someuchan[simp]:assumes "chDom TYPE('a) \<noteq> {}"
  shows "cTime (Rep c) = TUntimed"
  by(simp add: assms local.uchan_ctime)

end

class mult_msg_chan = chan +
  assumes mult_msg_chan_ctime[simp]:"\<And>c. Rep c \<in>chDom TYPE('a::chan) \<Longrightarrow> cTime (Rep c) \<in> {TUntimed, TTFin, TTLive}"
begin
  lemma mult_msg_chan_ctime2[simp]:
    "chDom TYPE('a::chan) \<noteq> {} \<Longrightarrow> cTime (Rep c) \<in> {TUntimed, TTFin, TTLive}"
    using local.mult_msg_chan_ctime by auto
end

subclass (in echan) mult_msg_chan
  apply(standard)
  by (simp)
subclass (in uchan) mult_msg_chan
  apply(standard)
  by (simp add: local.uchan_ctime)


class tsynchan = chan +
  assumes tsynchan_ctime[simp]:"\<And>c. Rep c \<in> chDom TYPE('a::chan) \<Longrightarrow> cTime (Rep c) = TTsyn"
begin

lemma sometsynchan[simp]:
  assumes"chDom TYPE('a) \<noteq> {}"
  shows"cTime (Rep (c::'a)) = TTsyn"
  by (simp add: assms)
end

subclass (in tsynchan) tchan
  apply(standard)
  by (simp)

subsubsection %invisible\<open> rep abs chan lemmata \<close>
default_sort %invisible chan

lemma repinrange[simp]:"Rep (c::'c) = x 
                        \<Longrightarrow> x\<in> range(Rep::'c \<Rightarrow> channel)"
  by blast

lemma chan_eq[simp]:"Rep (c::'c) = x \<Longrightarrow> x\<in> range(Rep::'d\<Rightarrow>channel) 
                        \<Longrightarrow> Rep((Abs::channel \<Rightarrow> 'd)(Rep c)) = x"
  by auto

lemma cempty_rule[simp]:assumes"chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<in> cEmpty"
  using assms chan_botsingle chDom_def by blast

lemma cnotempty_rule[simp]:assumes"\<not>chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<notin> cEmpty"
  using assms chan_botsingle chDom_def by blast

lemma cnotempty_cdom[simp]:assumes"\<not>chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<in> chDom(TYPE('c))"
  using assms by (simp add: chDom_def)

lemma cdom_notempty[simp]:assumes"c \<in>chDom TYPE('c)"
  shows" c \<notin> cEmpty"
  using assms by (simp add: chDom_def)

lemma notcdom_empty[simp]:assumes"Rep (c::'c) \<notin>chDom TYPE('c)"
  shows" Rep c \<in> cEmpty"
  using assms by (simp add: chDom_def)

lemma cdom2cdom:assumes "Rep c \<in> chDom TYPE('cs1)"
  shows "Rep (c::'cs2) \<in> chDom TYPE('cs2)"
  using assms cdom_notempty notcdom_empty by blast

lemma chdom_in: fixes c::"'cs::chan"
  assumes "chDom TYPE('cs) \<noteq> {}"
    shows "Rep c \<in> chDom TYPE('cs)"
  by (metis Diff_eq_empty_iff Diff_triv assms chDom_def 
      chan_botsingle rangeI)

lemma abs_reduction[simp]:
  fixes c::"'cs1::chan" 
  assumes"Rep c\<in>chDom TYPE('cs1)"
  and "Rep c \<in> chDom TYPE('cs2)"
  shows "Rep ((Abs::channel\<Rightarrow> 'cs2) (Rep c)) = Rep c"
  by (metis DiffD1 assms(2) chDom_def chan_eq)

lemma abs_fail:
  fixes c::"'cs1" 
  assumes"Rep c\<in>chDom TYPE('cs1)"
  and "Rep ((Abs::channel\<Rightarrow>'cs2) (Rep c)) \<noteq> Rep c"
  shows "Rep c \<notin> chDom TYPE('cs2)"
  using assms(1) assms(2) by auto

lemma dom_ref:
  fixes c::"'cs1" 
  assumes"Rep c\<in>chDom TYPE('cs1)"
  and "Rep ((Abs::channel\<Rightarrow>'cs2) (Rep c)) = Rep c"
  shows "Rep c \<in> chDom TYPE('cs2)"
  using assms(1) assms(2) chDom_def by fastforce

lemma rep_reduction[simp]: 
  assumes " c \<in> chDom TYPE('cs2)"
  shows "Rep ((Abs::channel\<Rightarrow> 'cs2) c) = c"
  by (metis (no_types, lifting) DiffE abs_reduction assms chDom_def image_iff)

lemma rep_reduction_alt[simp]: 
  assumes " Rep c \<in> chDom TYPE('cs2)"
  shows "Rep ((Abs::channel\<Rightarrow> 'cs2) (Rep c)) = Rep c"
  by (simp add: assms)

lemma rep_reduction2[simp]:
  assumes "Rep c \<in> chDom TYPE('c)"
  shows"Abs (Rep ((Abs::channel \<Rightarrow> 'c) (Rep c))) = Abs (Rep c)"
  using assms rep_reduction by force

lemma abs_eqI:
  fixes c::"channel"
  and c1::"'cs1"
  and c2::"'cs2"
  assumes "Rep c1 = Rep c2"
  and "Rep c1 = c"
  shows "Abs c = c1"
  and "Abs c = c2"
  using assms(2) apply auto[1]
  using assms(1) assms(2) by auto

lemma chan_single_eq:
  fixes c1 c2::"'cs"
  assumes "is_singleton(chDom TYPE('cs))"
  shows "c1 = c2"
proof - 
  have "\<And>c::'cs. Rep c\<in>chDom TYPE('cs)"
    apply(rule inchdom)
    by (metis assms insert_not_empty is_singleton_def)
  hence "\<And>c1::'cs. \<And> c2::'cs. Rep c1 = Rep c2"
    using assms(1)
    by (metis is_singleton_the_elem singletonD)
   thus ?thesis 
     using abs_eqI(2) by fastforce
 qed

declare %invisible[[show_types]]
declare %invisible[[show_consts]]

                                                       text\<open>\label{sec:interdom}\<close>

text\<open>There are three interesting interconnections between domains. 
Intuitively, the union operator takes all channels from both domains 
and the minus operator only channels that are in the first, but not 
the second domain. Since we also have to check for channels from 
@{const cEmpty}, its not that trivial. This would not be necessary,
if the type-system of Isabelle would allow empty types.\<close>



text\<open>The union of two domains should contain every channel of each 
domain. So the union of two empty domains should also be empty. But 
because the type itself can never be empty, we again have to use 
channels in @{const cEmpty} to define the union.\<close> 
typedef ('cs1,'cs2) union (infixr "\<union>" 20) = 
        "if chDomEmpty TYPE ('cs1) \<and> chDomEmpty TYPE ('cs2) 
            then {c | c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) }
            else chDom TYPE('cs1) \<union> chDom TYPE('cs2)" 
  by(auto)

text\<open>Because channels in @{const cEmpty} are interpreted as no real 
channels, the union of two empty domains is defined as the 
channel set @{const cEmpty}. The next step is to instantiate the 
union of two members of class @{class chan} as a member of class 
@{class chan}. This is rather easy, because either the union results
in @{const cEmpty}, so there are no channels where a message can 
be transmitted, or it results in the union of the domains without 
channels from @{const cEmpty}. Hence, the representation function 
@{const Rep} is defined as the representation function @{const Rep_union}
generated from the \<open>typedef\<close>-keyword. The output type union 
type of two input @{class chan} types is always a member of 
@{class chan} as shown in following instantiation.\<close>

instantiation union :: (chan, chan) chan 
begin
definition "Rep == Rep_union"
definition "Abs == Abs_union"
definition chandom_union_def:"chanDom_union (a::('a \<union> 'b) myself) = range (Rep::'a \<union> 'b \<Rightarrow> channel) - cEmpty"
lemma union_range_notempty:
"\<not> chDomEmpty TYPE ('cs1) \<or> \<not>chDomEmpty TYPE ('cs2) \<Longrightarrow> range (Rep:: 'cs1 \<union> 'cs2 \<Rightarrow> channel) =  chDom TYPE('cs1) \<union> chDom TYPE('cs2)" 
  apply(simp add: Channel.Rep_union_def)
  apply(case_tac "chDomEmpty TYPE('cs1)")
  apply (metis (mono_tags, lifting) chDom_def type_definition.Rep_range type_definition_union)
  by (metis (mono_tags, lifting) type_definition.Rep_range type_definition_union)

lemma union_range_empty:"chDomEmpty TYPE ('cs1) \<and> chDomEmpty TYPE ('cs2) \<Longrightarrow>
     range (Rep:: 'cs1 \<union> 'cs2 \<Rightarrow> channel) = {c | c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) } "
proof -
  assume "chDomEmpty (TYPE('cs1)::'cs1 itself) \<and> chDomEmpty (TYPE('cs2)::'cs2 itself)"
  then have "(if chDomEmpty (TYPE('cs1)::'cs1 itself) \<and> chDomEmpty (TYPE('cs2)::'cs2 itself) then {c |c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel)} else chDom (TYPE('cs1)::'cs1 itself) \<union> chDom (TYPE('cs2)::'cs2 itself)) = {c |c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel)}"
    by meson
  then have "type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union {c |c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel)}"
    by (metis (mono_tags, lifting) type_definition_union)
      then show ?thesis
  by (simp add: Channel.Rep_union_def type_definition.Rep_range)
qed
instance
  apply(intro_classes)
  apply(simp add: Abs_union_def Rep_union_def Rep_union_inverse)
  apply(simp add: chandom_union_def )
  apply(case_tac "chDomEmpty TYPE ('a) \<and> chDomEmpty TYPE ('b)",simp_all)
  apply(simp add: union_range_empty)
  apply(simp add: cEmpty_def chDom_def subset_iff)
  by(simp add: union_range_notempty chDom_def inf_commute inf_sup_distrib1)
end

lemma union_range_empty2:"chDomEmpty TYPE ('cs1) \<and> chDomEmpty TYPE ('cs2) \<Longrightarrow>
     {c | c. c \<in> range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) } \<subseteq> cEmpty "
  using image_iff by auto

lemma union_range_union:"\<not>(chDomEmpty TYPE ('cs1) 
                         \<and>  chDomEmpty TYPE ('cs2)) \<Longrightarrow> 
                   range (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) = 
                   chDom TYPE ('cs1) \<union> chDom TYPE('cs2)" 
  apply(subst Rep_union_def chDom_def)
  apply(case_tac "chDomEmpty TYPE('cs1)")
  apply (metis Rep_union_def chDom_def union_range_notempty)
  by (metis Rep_union_def chDom_def union_range_notempty)

text\<open>After the instantiation, class definition like the 
@{const chDom} function can be used. To verify the correctness of 
our definition we obtain the domain of the union type and prove, 
that it is indeed the union of the two sub domains.\<close>
           
theorem chdom_union[simp]:"chDom TYPE('cs1 \<union> 'cs2) = 
                           chDom TYPE ('cs1) \<union> chDom TYPE('cs2)"
  apply(subst chDom_def)
  apply(simp_all add: Rep_union_def)
  apply(case_tac "chDomEmpty TYPE ('cs1) \<and> chDomEmpty TYPE ('cs2)")
  apply (metis Collect_mem_eq Diff_iff Rep_union Rep_union_def Un_iff chDom_def cnotempty_rule sup_bot_left)
  by (simp add: Un_Diff chDom_def union_range_union)

lemma uniondom_fstempty: "chDom TYPE('fst) = {} \<Longrightarrow> chDom TYPE('fst \<union> 'snd) = chDom TYPE('snd)"
  by auto

lemma uniondom_sndempty: "chDom TYPE('snd) = {} \<Longrightarrow> chDom TYPE('fst \<union> 'snd) = chDom TYPE('fst)"
  by auto

lemma union_empty:"Rep (c::'fst\<union>'snd) \<notin> chDom TYPE('fst) \<Longrightarrow> Rep c \<notin> chDom TYPE('snd) \<Longrightarrow> chDom TYPE ('fst \<union> 'snd) = {}"
proof -
  assume a1: "Rep c \<notin> chDom (TYPE('fst)::'fst itself)"
  assume "Rep c \<notin> chDom (TYPE('snd)::'snd itself)"
  then have "\<exists>u. Rep (u::'fst \<union> 'snd) \<notin> chDom (TYPE('fst \<union> 'snd)::('fst \<union> 'snd) itself)"
    using a1 by auto
  then show ?thesis
    by (metis cnotempty_cdom)
qed

instantiation union::("{equal,chan}"," {equal,chan}") equal
begin
definition equal_union::"('a \<union> 'b) \<Rightarrow> ('a \<union> 'b) \<Rightarrow> bool" where                   
"equal_union a b \<equiv> Rep_union a = Rep_union b"
instance
  apply intro_classes
  by (simp add: equal_union_def Rep_union_inject)
end 

lemma chdomnotempty_rangeeq:"\<not> chDomEmpty TYPE ('cs1) \<Longrightarrow> 
         range (Rep:: 'cs1 \<Rightarrow> channel) = chDom TYPE ('cs1)"
  by (metis Diff_eq_empty_iff Diff_triv chDom_def chan_botsingle)

lemma rangeeq_chdom_union2:"\<not> chDomEmpty TYPE ('cs2) \<and> chDomEmpty TYPE ('cs1) \<Longrightarrow>
         range (Rep:: 'cs1 \<union> 'cs2 \<Rightarrow> channel) =  chDom TYPE('cs2)" 
  by (simp add: Channel.Rep_union_def union_range_union)

lemma rangeeq_chdom_union1:"\<not> chDomEmpty TYPE ('cs1) \<and> chDomEmpty TYPE ('cs2) \<Longrightarrow> 
         range (Rep:: 'cs1 \<union> 'cs2 \<Rightarrow> channel) =  chDom TYPE('cs1)" 
  by (simp add: Channel.Rep_union_def union_range_union)

lemma chdomnotempty_repunion_inrange:"\<not> chDom TYPE('a) \<noteq> {} \<Longrightarrow> \<not> chDom TYPE('b) \<noteq> {} \<Longrightarrow> 
     (Rep_union (x::'a \<union> 'b) \<in> (range (Rep::'a \<Rightarrow> channel)) \<or> (Rep_union x \<in> range (Rep::'b \<Rightarrow> channel)))"
  apply(induction x,simp)
  by (simp add: Abs_union_inverse)

lemma absunion_inrange1:"chDom TYPE('a) \<noteq> {} \<Longrightarrow>\<not>chDom TYPE('b) \<noteq> {} \<Longrightarrow> 
     (x::'a \<union> 'b) \<in> Abs_union ` range (Rep::'a \<Rightarrow> channel) "
  apply(subst chdomnotempty_rangeeq,simp)
  using rangeeq_chdom_union1 
  by (metis Rep_union_inverse UNIV_I union_range_notempty image_iff union_range_union)

lemma absunion_inrange2:"chDom TYPE('b) \<noteq> {} \<Longrightarrow>\<not> chDom TYPE('a) \<noteq> {} \<Longrightarrow>
     (x::'a \<union> 'b) \<in> Abs_union ` range (Rep::'b \<Rightarrow> channel) "
  apply(subst chdomnotempty_rangeeq,simp)
  using rangeeq_chdom_union2 
  by (metis Rep_union_inverse UNIV_I union_range_notempty image_iff union_range_union)

lemma chdomnotempty_absunion_inrange:"chDom TYPE('a) \<noteq> {} \<Longrightarrow>
       (x::'a \<union> 'b) \<in> Abs_union ` chDom TYPE('a) \<or> x \<in> Abs_union ` chDom TYPE('b)"
proof -
  fix x :: "'a \<union> 'b"
  assume "chDom (TYPE('a)::'a itself) \<noteq> {}"
  then have "\<forall>u. Rep_union (u::'a \<union> 'b) \<in> chDom (TYPE('b)::'b itself) \<or> Rep_union u \<in> chDom (TYPE('a)::'a itself)"
    using union_range_union by blast
  then show "x \<in> Abs_union ` chDom (TYPE('a)::'a itself) \<or> x \<in> Abs_union ` chDom (TYPE('b)::'b itself)"
    by (metis (full_types) Rep_union_inverse imageI)
qed

lemma union_inrange:"(x::'a \<union> 'b) \<in> range (\<lambda>a::'a. Abs_union (Rep a)) \<or> x \<in> range (\<lambda>a::'b. Abs_union (Rep a))"
  apply(simp add: range_composition)
  apply(case_tac "\<not> chDomEmpty TYPE ('a)")
  apply(case_tac "\<not> chDomEmpty TYPE ('b)")
  apply(subst chdomnotempty_rangeeq,simp)+
  apply (meson chdomnotempty_absunion_inrange)
  using absunion_inrange1 apply blast
  apply(case_tac "\<not> chDomEmpty TYPE ('b)")
  using absunion_inrange2 apply blast
  apply(induct_tac x) by auto

lemma chandom_chdom_eq:"chanDom(DUMMY::('a::chan) myself) = chDom (TYPE('a))"
  by (simp add: chanDom chDom_def)

lemma [code]: "chanDom (DUMMY::('a::chan \<union> 'b) myself) = chanDom (DUMMY::('a::chan) myself) \<union>  chanDom (DUMMY::('b::chan) myself) "
  by (simp add:chandom_chdom_eq)

instantiation union ::("{enum,chan}"," {enum,chan}") enum
begin
definition enum_u :"(enum_u :: ('a \<union> 'b) list) = 
remdups  (((map (Abs o Rep) (Enum.enum::'a list)) @(map (Abs o Rep)  (Enum.enum::'b list))))"
definition enum_union_def :"(enum_union :: ('a \<union> 'b) list) =   enum_u "
definition enum_all_union[code]:"enum_all_union P \<longleftrightarrow> (\<forall>x\<in> set enum_u. P x )"
definition enum_ex_union [code]:"enum_ex_union P \<longleftrightarrow>  (\<exists>A\<in> set enum_u. P A)"
instance
  apply intro_classes
  apply(rule UNIV_eq_I)
  apply(simp add: enum_union_def enum_u)
  apply(simp add: enum_UNIV )
  apply(simp add: Abs_union_def)
  using union_inrange apply fastforce
  apply(simp add: enum_union_def enum_u)
  apply(simp add: Abs_union_def enum_all_union enum_u enum_UNIV )
  using union_inrange apply fastforce
  apply(simp add: Abs_union_def enum_ex_union enum_u enum_UNIV)
  using union_inrange by fastforce
end

instantiation union :: (tchan, tchan) tchan 
begin
instance
  apply intro_classes
  apply simp
  by (metis(full_types) rep_reduction tchan_ctime)
end

instance union :: (tsynchan, tsynchan) tsynchan
  apply(intro_classes)
  apply(simp)
  by (metis rep_reduction tsynchan_ctime)



text\<open>Subtracting one domain from another results in the empty 
domain. But analogous to the union, our resulting type always 
contains channels. Subtracting a set from one of its subsets would 
result in an empty type. Hence, our result for this case is again 
@{const cEmpty}.\<close>

typedef ('cs1,'cs2) minus (infixr "-" 20) = 
        "if chDom TYPE('cs1) \<subseteq> chDom TYPE('cs2) 
             then {SOME c. ctype ( c) = {} }
             else chDom TYPE('cs1) - chDom TYPE('cs2)" 
  by(cases "range Rep \<subseteq> range Rep", auto)

lemma ctype_empty_seq_cempty:"{SOME c. ctype c = {}} \<subseteq> cEmpty"
  by (metis (no_types, lifting) cEmpty_def cempty_exists empty_Collect_eq empty_subsetI insert_subset mem_Collect_eq some_eq_ex)


text\<open>The result from the subtraction of two @{class chan} types
is also in the class. The proof is, like above, straightforward.\<close>

instantiation minus :: (chan, chan) chan
begin
definition "Rep == Rep_minus"
definition "Abs == Abs_minus"
  definition chandom_minus_def:"chanDom_minus (a::('a - 'b) myself) = range (Rep::'a - 'b \<Rightarrow> channel) - cEmpty"
lemma minus_range_empty:"chDom TYPE('a) \<subseteq> chDom TYPE('b) \<Longrightarrow> range (Rep_minus::('a - 'b) \<Rightarrow> channel) =  {SOME c. ctype ( c) = {} } "
  by (metis (mono_tags, lifting) type_definition.Rep_range type_definition_minus)
lemma minus_range_minus:"\<not>chDom TYPE('a) \<subseteq> chDom TYPE('b) \<Longrightarrow> range (Rep_minus::('a - 'b) \<Rightarrow> channel) = chDom TYPE('a) - chDom TYPE('b) "
  by (metis (mono_tags, lifting)  type_definition.Rep_range type_definition_minus)
instance
  apply intro_classes
  apply (simp add: Abs_minus_def Rep_minus_def Rep_minus_inverse)
  apply (simp add: chandom_minus_def)
  apply(simp add: Rep_minus_def)
  apply(case_tac "chDom TYPE('a) \<subseteq> chDom TYPE('b)")
  using Rep_minus_def minus_range_empty apply auto[1] 
  apply (simp add: minus_range_minus)
  by auto
end

instantiation minus :: (tchan, tchan) tchan
begin
instance
  apply intro_classes
  apply (case_tac "chDom TYPE('a) \<subseteq> chDom TYPE('b)")
  apply (metis Rep_minus_def ctype_empty_seq_cempty Diff_eq_empty_iff chDom_def ex_in_conv minus_range_empty)
  by (metis DiffD1 Rep_minus Rep_minus_def ex_in_conv rep_reduction tchan_class.sometschan)
end



theorem chdom_minus[simp]:"chDom TYPE('cs1 - 'cs2) = 
                           chDom TYPE ('cs1) - chDom TYPE('cs2)"
  apply(subst chDom_def)
  apply(simp_all add: Rep_minus_def)
  apply(case_tac "chDom TYPE('cs1) \<subseteq> chDom TYPE('cs2)")
  apply(simp add: minus_range_empty)
  apply (metis (no_types, lifting) Diff_eq_empty_iff cEmpty_def cempty_exists empty_Collect_eq empty_Diff insert_Diff1 mem_Collect_eq some_eq_ex)
  using Diff_Int_distrib2 minus_range_empty minus_range_minus 
  by auto
 

theorem chdom_minus_empty[simp]:"chDom TYPE('cs1 - 'cs2) \<inter> chDom TYPE ('cs2) = {}"
  by auto

lemma minus_empty: "Rep (c::'cs1 - 'cs2) \<notin> chDom TYPE('cs1) \<Longrightarrow> chDomEmpty TYPE ('cs1 - 'cs2)"
  by (metis Diff_iff chdom_in chdom_minus)

lemma minus_empty2:"Rep (c::'cs1 - 'cs2) \<in> chDom TYPE('cs1) \<Longrightarrow> Rep c \<in> chDom TYPE('cs2) \<Longrightarrow> chDomEmpty TYPE ('cs1 - 'cs2)"
  using chdom_minus_empty chdomnotempty_rangeeq by blast

lemma minus_notempty: "\<not>chDomEmpty TYPE('cs1 - 'cs2) \<Longrightarrow> Rep (c::'cs1) \<in> chDom TYPE('cs1)"
  using chdom_in chdom_minus by blast

lemma union_minus_notempty_left: "\<not>chDomEmpty TYPE(('cs1 \<union> 'cs2) - 'cs3) \<Longrightarrow> Rep (c::('cs1 \<union> 'cs2) - 'cs3) \<in> chDom TYPE('cs1) \<Longrightarrow> \<not>chDomEmpty TYPE('cs1 - 'cs3)"
  by (metis Diff_iff chdom_in chdom_minus)

lemma union_minus_notempty_right: "\<not>chDomEmpty TYPE(('cs1 \<union> 'cs2) - 'cs3) \<Longrightarrow> Rep (c::('cs1 \<union> 'cs2) - 'cs3) \<in> chDom TYPE('cs2) \<Longrightarrow> \<not>chDomEmpty TYPE('cs2 - 'cs3)"
  by (metis Diff_iff chdom_in chdom_minus)

instantiation minus::("{equal,chan}"," {equal,chan}") equal
begin
definition equal_minus::"('a - 'b) \<Rightarrow> ('a - 'b) \<Rightarrow> bool" where                   
"equal_minus a b \<equiv> Rep_minus a = Rep_minus b"
instance
  apply intro_classes
  by (simp add: Rep_minus_inject equal_minus_def)
end 

primrec removeAllList::"'a::type list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"removeAllList [] ys = []"|
"removeAllList (x#xs) ys = (if x \<in> set ys then removeAllList xs ys else x#removeAllList xs ys)"

lemma set_removealllist:"set(removeAllList a b) = set a - set b"
  by (induct a,auto)

lemma repminus_inrange:"\<not> chDom TYPE('a) \<subseteq> chDom TYPE('b) \<Longrightarrow> 
    Rep_minus (x::'a - 'b) \<in> (range (Rep:: 'a \<Rightarrow> channel) - range (Rep:: 'b \<Rightarrow> channel))"
  proof -
    fix x :: "'a - 'b"
    assume a1: "\<not> chDom (TYPE('a)::'a itself) \<subseteq> chDom (TYPE('b)::'b itself)"
    then have f2: "range (Rep_minus::'a - 'b \<Rightarrow> channel) = chDom (TYPE('a)::'a itself) - chDom (TYPE('b)::'b itself)"
      by (metis minus_range_minus)
    have f3: "chDomEmpty (TYPE('a)::'a itself) \<or> range (Rep::'a \<Rightarrow> channel) = chDom (TYPE('a)::'a itself)"
      by (meson chdomnotempty_rangeeq)
    then have f4: "range (Rep::'a \<Rightarrow> channel) - cEmpty = range (Rep::'a \<Rightarrow> channel)"
      using a1 by (metis chDom_def equals0D subsetI)
    have f5: "chDom (TYPE('a)::'a itself) \<noteq> {}"
      using a1 by blast
    have "Rep_minus x \<in> range (Rep::'a - 'b \<Rightarrow> channel)"
      by (metis Rep_minus_def repinrange)
    then show "Rep_minus x \<in> range (Rep::'a \<Rightarrow> channel) - range (Rep::'b \<Rightarrow> channel)"
      using f5 f4 f3 f2 by (metis Diff_Un Diff_subset Rep_minus_def Un_Diff_cancel2 chDom_def inf.orderE)
  qed
  
lemma [code]: "chanDom (DUMMY::('a::chan - 'b) myself) = chanDom (DUMMY::('a::chan) myself) - chanDom (DUMMY::('b::chan) myself) "
  by (simp add:chandom_chdom_eq)

instantiation minus ::("{enum,chan}"," {enum,chan}") enum
begin
definition enummin:"(enummin::('a - 'b) list) = (if chDom TYPE('a) \<subseteq> chDom TYPE('b) 
   then map Abs [SOME c. ctype ( c) = {}] 
   else remdups (map Abs (removeAllList (map Rep (Enum.enum::'a list)) (map Rep (Enum.enum::'b list)))))"
definition enum_minus_def:"enum_minus = enummin"
definition enum_all_minus[code]:"enum_all_minus P \<longleftrightarrow> (\<forall>x\<in> set enummin. P x )"
definition enum_ex_minus [code]:"enum_ex_minus P \<longleftrightarrow>  (\<exists>A\<in> set enummin. P A)"
instance
  apply intro_classes
  apply(rule UNIV_eq_I)
  apply(simp add: enum_minus_def enummin Abs_minus_def)
  apply(case_tac "chDom TYPE('a) \<subseteq> chDom TYPE('b)",simp_all)
  apply(metis Abs_minus_cases empty_iff insert_iff)
  apply(simp add: set_removealllist enum_UNIV)
  apply(metis Rep_minus_inverse image_iff repminus_inrange)
  apply(simp add: enum_minus_def enummin Abs_minus_def)
  apply(simp add: Abs_minus_def enum_all_minus enummin enum_UNIV)
  apply(case_tac "chDom TYPE('a) \<subseteq> chDom TYPE('b)",simp_all)
  apply(metis Abs_minus_induct singletonD)
  apply(simp add: set_removealllist enum_UNIV)
  apply(metis Rep_minus_inverse repminus_inrange)
  apply(simp add: Abs_minus_def enum_ex_minus enummin enum_UNIV)
  apply(case_tac "chDom TYPE('a) \<subseteq> chDom TYPE('b)",simp_all)
  apply(metis (mono_tags) Abs_minus_cases mem_Collect_eq singleton_conv2)
  apply(simp add: set_removealllist enum_UNIV)
  by (metis Rep_minus_inverse repminus_inrange)
end

instance minus :: (tsynchan, tsynchan) tsynchan
  apply(intro_classes)
  apply(simp)
  by (metis rep_reduction tsynchan_ctime)

lemma ttone_ex:"cTime (Rep c) = TTOne \<Longrightarrow> a \<in> ctype (Rep c) \<Longrightarrow> \<exists>b. a = Timed (TOne b)"
proof -
  assume a1: "cTime (Rep c) = TTOne"
  assume a2: "a \<in> ctype (Rep c)"
  then have "cMsg (Rep c) \<noteq> {}"
    using ctype_def by force
  then show ?thesis
    using a2 a1 ctype_def by auto
qed

lemma ttfin_ex:"cTime (Rep c) = TTFin \<Longrightarrow> a \<in> ctype (Rep c) \<Longrightarrow> \<exists>b. a = Timed (TFin b)"
proof -
  assume a1: "cTime (Rep c) = TTFin"
  assume a2: "a \<in> ctype (Rep c)"
  then have "cMsg (Rep c) \<noteq> {}"
    using ctype_def by force
  then show ?thesis
    using a2 a1 ctype_def by auto
qed

lemma ttsyn_ex:"cTime (Rep c) = TTsyn \<Longrightarrow> a \<in> ctype (Rep c) \<Longrightarrow> \<exists>b. a = Timed (Tsyn b)"
proof -
  assume a1: "cTime (Rep c) = TTsyn"
  assume a2: "a \<in> ctype (Rep c)"
  then have "cMsg (Rep c) \<noteq> {}"
    using ctype_def by force
  then show ?thesis
    using a2 a1 ctype_def by auto
qed

lemma ctime_echan[simp]:
  assumes "Rep c\<in> chDom TYPE('cs)"
  shows"cTime (Rep (c::'cs::echan)) = TTLive"
  using assms echan_ctime by blast

lemma 
  ctype_echan_def:
  assumes "chDom TYPE('cs::echan) \<noteq> {}"
  shows"ctype (Rep (c::'cs)) = (Timed o TLive) ` ({Tick} \<union> (EventMsg ` (cMsg (Rep c))))"           
  apply(simp add: ctype_def assms)
  apply(rule ccontr)
  using assms ctype_empty_iff dom2ctypenempty by blast

lemma channel_noteqI:"Rep c1 \<noteq> Rep c2 \<Longrightarrow> c1 \<noteq> c2"
  by auto



fun m2list::"M \<Rightarrow> msg list" where
"m2list (Timed (TFin ls))= ls"|
"m2list (Timed (TLive (EventMsg e))) = [e]"|
"m2list (Timed (TLive (Tick))) = []"|
"m2list (Untimed e) = [e]"|
"m2list (Timed (Tsyn (TSynMsg m))) = [m]"|
"m2list (Timed (Tsyn (Eps))) = []"|
"m2list (Timed (TOne (TOneMsg va))) = [va]" 

end
