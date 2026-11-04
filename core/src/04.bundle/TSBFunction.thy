theory TSBFunction

imports SBExtend stream.TimedStreamFunction ChannelConverterTypes

begin

lift_definition tsbDrop::"nat \<Rightarrow> 'cs::tchan\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_lsb (\<lambda>c. tsdrop n\<cdot>(sb \<^enum> c))"
  apply (intro cont2cont)
  by (rule sbmap_well, simp)


lemma tsbdrop_getch[simp]: "(tsbDrop n\<cdot>sb) \<^enum> c = tsdrop n\<cdot>(sb \<^enum> c)"
  apply(simp add: tsbDrop.rep_eq sbGetCh.rep_eq)
  apply(subst sb_rep_abs)
  apply (rule lsbwellI, simp)
   apply (meson dual_order.trans lsb_well_def sbwell2fwell tsdrop_sValues)
  by simp

lemma tsbdrop_bot[simp]: "tsbDrop n\<cdot>\<bottom> = \<bottom>"
  by(rule sb_eqI, simp)


lift_definition tsbTake::"nat \<Rightarrow> 'cs::tchan\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_lsb (\<lambda>c. tstake n\<cdot>(sb \<^enum> c))"
  apply (intro cont2cont)
  by (rule sbmap_well, simp)

abbreviation tsbRt :: "'cs::tchan\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>"  where 
"tsbRt \<equiv> tsbDrop 1"


lemma tsbrt_ticksb [simp]: "tsbRt\<cdot>(ticksb \<Zcat>\<Zcat> sb) = sb"
  apply(rule sb_eqI)
  apply(simp add: sbconc_getch_split )
  apply(simp add: ticksb.rep_eq sbgetch_insert)
  by (simp add: one_def)

lemma tsbdrop_ticksb[simp]: "tsbDrop (Suc 0)\<cdot>(ticksb \<Zcat>\<Zcat> sb) = sb"
  by (metis One_nat_def tsbrt_ticksb)


fun toUntimedMElem :: "M \<Rightarrow> M stream" where
"toUntimedMElem (Untimed m) = \<up>(Untimed m)" |
"toUntimedMElem (Timed (Tsyn \<sim>)) = \<epsilon>" |
"toUntimedMElem (Timed (TLive Tick)) = \<epsilon>" |
"toUntimedMElem (Timed (Tsyn (TSynMsg m))) = \<up>(Untimed m)" |
"toUntimedMElem (Timed (TLive (EventMsg m))) = \<up>(Untimed m)" |
"toUntimedMElem (Timed (TOne (TOneMsg m))) = \<up>(Untimed m)" |
"toUntimedMElem (Timed (TFin m)) = smap Untimed\<cdot>(list2s m)"

definition toUntimedM :: "M stream \<rightarrow> M stream" where
"toUntimedM \<equiv> smapAlt toUntimedMElem"

definition tsliced2ustream::"'a::countable list stream \<rightarrow> 'a stream"where
"tsliced2ustream = e2ustream oo sListToEvent"

definition toUntimedS :: "msg combinedstream \<rightarrow> msg stream" where
"toUntimedS = combStreamCases e2ustream tsyn2ustream tone2ustream tsliced2ustream ID"


definition convUntimed::"'cs::{one_chan} sb \<rightarrow> 'cs untimed sb" where
"convUntimed \<equiv> \<Lambda> sb. Abs_lsb(\<lambda>c. toUntimedM\<cdot>(sb \<^enum> (untimedToOrigin c)))"

definition tsbnth :: "nat \<Rightarrow> 'cs::{tchan, one_chan, countable}\<^sup>\<Omega> \<rightarrow> 'cs untimed\<^sup>\<Omega>" where
"tsbnth n \<equiv> \<Lambda> sb. convUntimed\<cdot>(Abs_lsb (\<lambda>c. tsnth n\<cdot>(sb \<^enum> c)))"

primrec sbntimes :: "nat \<Rightarrow> 'cs\<^sup>\<Omega> \<Rightarrow> 'cs\<^sup>\<Omega>" ("_\<diamondop>_" [60,80] 90) where
  "sbntimes 0 sb = \<bottom>" |
  "sbntimes (Suc n) sb = (sbConc sb)\<cdot>(sbntimes n sb)"

definition tsbDelay :: "nat \<Rightarrow> 'cs::{tchan, countable}\<^sup>\<Omega> \<rightarrow> 'cs\<^sup>\<Omega>" where 
"tsbDelay n \<equiv> sbConc (n \<diamondop> sbInfTlen)"

fun toEventElem :: "M \<Rightarrow> M stream" where
"toEventElem (Untimed m) = \<up>(Untimed m)" |
"toEventElem (Timed (Tsyn \<sim>)) = \<up>(Timed (TLive Tick))" |
"toEventElem (Timed (Tsyn (TSynMsg m))) = \<up>(Timed(TLive (EventMsg m))) \<Zcat>\<Zcat> \<up>(Timed (TLive Tick))" |
"toEventElem (Timed (TLive m)) = \<up>(Timed (TLive m))" |
"toEventElem (Timed (TOne (TOneMsg m))) = \<up>(Timed(TLive (EventMsg m))) \<Zcat>\<Zcat> \<up>(Timed (TLive Tick))" |
"toEventElem (Timed (TFin m)) = (smap (Timed o TLive o EventMsg)\<cdot>(list2s m)) \<Zcat>\<Zcat> \<up>(Timed (TLive Tick))"

definition toEventS :: "M stream \<rightarrow> M stream" where
"toEventS \<equiv> smapAlt toEventElem"

definition convEvent::"'cs::{one_chan} sb \<rightarrow> 'cs tlived sb" where
"convEvent \<equiv> \<Lambda> sb. Abs_lsb(\<lambda>c. toEventS\<cdot>(sb \<^enum> (tlivedToOrigin c)))"



definition toEventElemn :: "msg combinedstream \<rightarrow> msg event stream" where
"toEventElemn = combStreamCases ID tsyn2event tone2event sListToEvent (smap EventMsg)"

definition convEventn::"'cs::{one_chan} sb \<rightarrow> 'cs tlived sb" where
"convEventn \<equiv> \<Lambda> sb. Abs_sb(\<lambda>c. TEVENT (toEventElemn\<cdot>((Rep_sb sb)  (tlivedToOrigin c))))"

definition sbMakeUntimed :: "'a :: one_chan\<^sup>\<Omega> \<rightarrow> 'a tlived untimed\<^sup>\<Omega>" where
"sbMakeUntimed \<equiv> convUntimed oo convEvent"

end