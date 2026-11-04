theory EventStreamMore
imports EventStream StreamAutomaton

begin
default_sort countable

definition elenMsg::"'msg event stream \<rightarrow> lnat" where
"elenMsg = (\<Lambda> s. #(e2ustream\<cdot>s))"

definition escanlMsg::"('state::type \<Rightarrow> 'msg \<Rightarrow> ('state \<times> 'out stream)) \<Rightarrow> 'state \<Rightarrow> 'msg event stream \<rightarrow> 'out event stream" where
"escanlMsg f start = sscanlA (\<lambda>state msg. case msg of Tick \<Rightarrow> (state,\<up>Tick) | 
                                                      EventMsg e \<Rightarrow> apsnd (Rep_cfun (smap EventMsg)) (f state e)) start"

lemma escanlmsg_bot [simp]: "escanlMsg f s\<cdot>\<epsilon> = \<epsilon>"
    and escanlmsg_tick [simp]: "escanlMsg f s\<cdot>(\<up>\<surd> \<Zcat> stream) = \<up>\<surd> \<Zcat> escanlMsg f s\<cdot>stream"
  by(simp add: escanlMsg_def)+

lemma "e2ustream\<cdot>(escanlMsg f s\<cdot>estream) = sscanlA f s\<cdot>(e2ustream\<cdot>estream)"
  apply(induction estream rule: eind)
     apply auto[4]
  apply(simp add: escanlMsg_def )
  oops

definition escanlTick::"('state::type \<Rightarrow> ('state \<times> 'msg event stream)) \<Rightarrow> 'state \<Rightarrow> 'msg event stream \<rightarrow> 'msg event stream" where
"escanlTick f start = sscanlA (\<lambda>state msg. case msg of Tick \<Rightarrow> f state | 
                                                      EventMsg e \<Rightarrow> (state,\<up>(EventMsg e))) start"

definition e2rougherTime::"nat \<Rightarrow> 'msg event stream \<rightarrow> 'msg event stream" where
"e2rougherTime n = escanlTick (\<lambda>m. case m of (Suc k) \<Rightarrow> (k,  \<epsilon>) | 
                                                0    \<Rightarrow> (n,\<up>Tick)) n"

definition e2finerTime::"nat \<Rightarrow> 'msg event stream \<Rightarrow> 'msg event stream set" where
"e2finerTime n estream = {finerStream | finerStream. e2rougherTime n\<cdot>finerStream = estream}"



definition etakeMsg::"nat \<Rightarrow> 'msg event stream \<rightarrow> 'msg event stream" where
"etakeMsg n = escanlMsg (\<lambda>n msg. case n of (Suc m) \<Rightarrow> (m,\<up>msg) | _ \<Rightarrow>(0,\<epsilon>)) n"

definition edropMsg::"nat \<Rightarrow> 'msg event stream \<rightarrow> 'msg event stream" where
"edropMsg n = escanlMsg (\<lambda>n msg. case n of (Suc m) \<Rightarrow> (m,\<epsilon>) | _ \<Rightarrow>(0,\<up>msg)) n"



definition etakewhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a event stream \<rightarrow> 'a event stream" where
"etakewhile f = stakewhile (\<lambda>msg. (case msg of EventMsg e \<Rightarrow> f e | Tick \<Rightarrow> True))"

definition edropwhile::"('a \<Rightarrow> bool) \<Rightarrow> 'a event stream \<rightarrow> 'a event stream" where
"edropwhile f = sdropwhile (\<lambda>msg. (case msg of EventMsg e \<Rightarrow> f e | Tick \<Rightarrow> True))"


definition eprojFst::"('a\<times>'b) event stream \<rightarrow> 'a event stream" where
"eprojFst = emap fst"

definition eprojSnd::"('a\<times>'b) event stream \<rightarrow> 'b event stream" where
"eprojSnd = emap snd"

definition ezip::"'a event stream \<rightarrow> 'b event stream \<rightarrow> ('a\<times>'b) event stream" where
"ezip = (\<Lambda> as bs. sListToEvent\<cdot>(smap (\<lambda>(al,bl). zip al bl)\<cdot>(szip\<cdot>(sEventToList\<cdot>as)\<cdot>(sEventToList\<cdot>bs))))"

end