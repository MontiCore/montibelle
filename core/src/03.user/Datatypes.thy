theory Datatypes
                
imports inc.Prelude

begin

default_sort %invisible type

                                                 text\<open> \label{sec:data}\<close>

text\<open>\gls{MontiArc} components might have different 
channels and types, even user-defined types like an enum are 
possible. Hence, there is no general type definition assigning a message type to every 
possible channel. Thus, the datatypes have to 
be specific to the system under consideration. A possible simple 
example system is shown in \cref{fig:sensor}. It consists of a temperature 
sensor component and a guarding sensor that might cause an alarm 
depending on the temperature. The temperature sensor has no input 
channels, it depends completely on events outside of our modeled system. It 
outputs the temperature as an @{type int}-value. 
The output channel of the sensor is the input channel of the guard 
component, it then checks if a temperature threshold is exceeded to 
then raises an alarm.\<close>





                                           text\<open>\label{sub:pmsgdata}\<close>

datatype colors = ColRed | ColGreen | ColYellow
instance colors :: countable
  apply(intro_classes)
  by(countable_datatype)

datatype button = Pressed
instance button :: countable
  apply(intro_classes)
  by(countable_datatype)


datatype msg = NAT "nat" | BOOL "bool" | STRING string | INT int |
                  PROD msg msg | COLOR colors | BUTTON button



instance msg :: countable
  apply(intro_classes)
  by(countable_datatype)



                                           text\<open>\label{sub:chadata}\<close>



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
