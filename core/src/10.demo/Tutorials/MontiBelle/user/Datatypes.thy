theory Datatypes

imports inc.Prelude

begin

default_sort type

text \<open>We only have @{type bool} messages\<close>
type_synonym msg = bool



datatype channel = CH                               string
                                                    timeType
                                                    "msg set"



fun cName :: "channel \<Rightarrow> string" where
"cName (CH name _ _) = name" 


text\<open>In addition, each channel is typed and therefore, can be 
restricted to allow only a subset of messages from @{type msg} on
its stream. Thus, each channel can be mapped to a set of messages 
from datatype @{type msg}.\<close>

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH n _ S) = S" 

text \<open>\isacommand{definition} @{const cMsg} :: "@{typeof cMsg}"\<close>

text\<open>Such a mapping is described by the @{const cMsg} function. Only
messages included in the @{const cMsg} are allowed to be transmitted
on the respective channel. For the sensor system, channel \<open>c1\<close> would
be allowed to transmit all \<open>\<I> int\<close> and \<open>c2\<close> all \<open>\<B> bool\<close> messages.
The \<open>cempty\<close> channel can never transmit any message, hence, 
@{const cMsg} of \<open>cempty\<close> would be empty.\<close>

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  using cMsg.simps by metis


text \<open>Since one can use different time models for components, we 
also have to use the correct time model for our streams. Therefore,
we define a function that maps a channel to its time model. The 
@{type timeType} is defined as:\<close>

text\<open>@{datatype timeType}\<close>


fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _)= tt"

end
