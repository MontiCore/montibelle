theory flexray
  imports stream.StreamAutomaton stream.TsynStream
begin

type_synonym Slot = nat

record 'a Message =
slot::Slot
data::'a 

instance Message_ext ::(countable,countable) countable
proof(standard)
  obtain g where g_def:"inj (g::(Slot \<times>'a \<times> 'b) \<Rightarrow> nat)"
    by auto
  have "inj (\<lambda> cs. g (slot cs, data cs, more cs))"
    apply(rule injI)
    by (simp add: g_def inj_eq)
  then show "\<exists>to_nat::('a,'b) Message_scheme \<Rightarrow> nat. inj to_nat"
    by blast
qed

record Config =
schedule::"Slot list"
cycleLength::nat 

instance Config_ext ::(countable) countable
proof(standard)
  obtain g where g_def:"inj (g::(Slot list \<times> nat \<times> 'a) \<Rightarrow> nat)"
    by auto
  have "inj (\<lambda> cs. g (schedule cs, cycleLength cs, more cs))"
    apply(rule injI)
    by (simp add: g_def inj_eq)
  then show "\<exists>to_nat::'a Config_scheme \<Rightarrow> nat. inj to_nat"
    by blast
qed


definition Scheduler_HLR::"Config \<Rightarrow> Slot tsyn stream \<Rightarrow> bool"where
"Scheduler_HLR c ts= (\<forall> slot t. if slot \<in> set (schedule c) \<and> slot = t mod cycleLength c then snth t ts = TSynMsg slot else snth t ts = Eps)"


fun Receive_HLR::"(Slot tsyn stream \<times> 'a::countable Message tsyn stream) \<Rightarrow> 'a Message tsyn stream \<Rightarrow> bool"where
"Receive_HLR (activation,recv) (store) = (\<forall> t. if snth t activation = Eps then snth t store = snth t recv else snth t store = Eps)"

fun Send_HLR::"(Slot tsyn stream \<times> 'a::countable Message tsyn stream) \<Rightarrow> (Slot tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> bool"where
"Send_HLR (activation,return) (get,send) = (\<forall> t. if snth t activation = Eps then snth t get = Eps \<and> snth t send = Eps else snth t get = snth t activation \<and> snth t send = snth t return)"


fun BusInterface_HLR::"(Slot tsyn stream \<times> 'a::countable Message tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> (Slot tsyn stream \<times> 'a Message tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> bool"where
"BusInterface_HLR (activation, recv, return) (get, send, store)= (Receive_HLR (activation,recv) store \<and> Send_HLR (activation,return)(get,send))"


fun FlexRay_Controller_HLR::"Config \<Rightarrow> ('a::countable Message tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> ('a Message tsyn stream \<times> 'a Message tsyn stream \<times> Slot tsyn stream) \<Rightarrow> bool"where
"FlexRay_Controller_HLR c (recv,return) (send,store,get)= (\<exists>activation. Scheduler_HLR c activation \<and> BusInterface_HLR (activation,recv,return) (get,send,store))"


fun MessageTransmission_HLR::"Config \<Rightarrow> ('a Message tsyn stream) \<Rightarrow> ('a Message tsyn stream \<times> Slot tsyn stream) \<Rightarrow> bool"where
"MessageTransmission_HLR c (return) (store,get) = (\<forall> s\<in>(set (schedule c)). \<forall>t. s= t mod cycleLength c \<longrightarrow> snth t get = TSynMsg s)"

fun MessageTransmission_HLR_2::"(Config\<times>Config) \<Rightarrow> ('a Message tsyn stream\<times> 'a Message tsyn stream) \<Rightarrow> ('a Message tsyn stream \<times>'a Message tsyn stream \<times> Slot tsyn stream \<times> Slot tsyn stream) \<Rightarrow> bool"where
"MessageTransmission_HLR_2 (c1,c2) (return1,return2) (store1,store2,get1,get2) = ( \<forall>t. (\<forall> s\<in>(set (schedule c1)). s= t mod cycleLength c1 \<longrightarrow> snth t get1 = TSynMsg s \<and> snth t store2 = snth t return1) \<and> (\<forall> s\<in>(set (schedule c2)). s= t mod cycleLength c2 \<longrightarrow> snth t get2 = TSynMsg s \<and> snth t store1 = snth t return2))"

fun Broadcast_HLR::"('a Message tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> ('a Message tsyn stream) \<Rightarrow> bool"where
"Broadcast_HLR (send1,send2) (recv) = (\<forall>t. if snth t send1 \<noteq> Eps then snth t recv = snth t send1 else snth t recv = snth t send2)"

fun cable_HLR::"('a Message tsyn stream \<times> 'a Message tsyn stream) \<Rightarrow> ('a Message tsyn stream) \<Rightarrow> bool"where
"cable_HLR (send1,send2) (recv) = ((\<forall>t. snth t send1 = Eps \<or> snth t send2 = Eps) \<longrightarrow> Broadcast_HLR (send1,send2) recv)"

lemma flexray_pred:
  assumes "FlexRay_Controller_HLR c1 (recv,return1) (send1,store1,get1)"
  assumes "FlexRay_Controller_HLR c2 (recv,return2) (send2,store2,get2)"
  assumes "cable_HLR (send1,send2) recv"
  assumes "set (schedule c1) \<inter> set (schedule c2) = {}"
  assumes "cycleLength c1 = cycleLength c2"
  shows "MessageTransmission_HLR_2 (c1,c2) (return1,return2) (store1,store2,get1,get2)"
  using assms apply(simp add: Scheduler_HLR_def)
  apply auto
  apply (metis (full_types) Int_iff emtpy_reduce tsyn.distinct(1))
  apply (metis (full_types) Int_iff emtpy_reduce tsyn.distinct(1)) 
  apply (metis (full_types) disjoint_iff tsyn.distinct(1) tsyn.exhaust)
  apply (metis (full_types) disjoint_iff tsyn.distinct(1))
  done

end