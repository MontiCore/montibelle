theory EventStreamCodegen
  imports StreamCodegen StreamWhileCodegen
begin


definition eshdts_nc :: "'a::{countable} event stream \<Rightarrow> 'a stream" where
  "eshdts_nc \<equiv> Rep_cfun eshdts"

lemma [code_abbrev]: "eshdts_nc s = eshdts\<cdot>s"
  by (simp add: eshdts_nc_def)

lemma [code]: "eshdts_nc \<epsilon> = \<epsilon>"
  by (simp add: eshdts_nc_def)

fun inv_EventMsg_code where "inv_EventMsg_code (EventMsg h) = h"

lemma inv_EventMsg_code_eq: "h \<noteq> Tick \<Longrightarrow> inv_EventMsg_code h = (inv EventMsg) h"
  by force

lemma [code]: "eshdts_nc (updis h && rt) = (if h = Tick then \<epsilon> else \<up>(inv_EventMsg_code h) \<Zcat> eshdts_nc rt)"
  by (metis eshdts_event eshdts_nc_def eshdts_tick event_inv inverseEventMsg.cases lscons_conv inv_EventMsg_code_eq)


definition tsdrop_nc :: "nat \<Rightarrow> 'a::{tlen,countable} stream \<Rightarrow> 'a stream" where
  "tsdrop_nc n \<equiv> Rep_cfun (tsdrop n)"

lemma [code_abbrev]: "tsdrop_nc n s = tsdrop n\<cdot>s"
  by (simp add: tsdrop_nc_def)

lemma [code]: "tsdrop_nc 0 s = s"
  by (simp add: tsdrop_nc_def)

lemma "tsdrop_nc (Suc n) (updis Tick && rt) = tsdrop_nc n rt"
  by (simp add: tsdrop_nc_def upstream_abbrev)

lemma "tsdrop_nc (Suc n) (updis (EventMsg x) && rt) = tsdrop_nc (Suc n) rt"
  by (simp add: tsdrop_nc_def upstream_abbrev)


definition esnth_nc :: "nat \<Rightarrow> 'a::{countable} event stream \<Rightarrow> 'a stream" where
"esnth_nc n \<equiv> Rep_cfun (esnth n)"

lemma [code_abbrev]: "esnth_nc n s = esnth n\<cdot>s"
  by (simp add: esnth_nc_def)

lemma [code]: "esnth_nc n = eshdts_nc o (tsdrop_nc n)"
  apply(simp add: o_def)
  by (metis cfcomp2 eshdts_nc_def esnth_def esnth_nc_def tsdrop_nc_def)


definition eValues_nc :: "'a event stream \<Rightarrow> 'a set"
    where "eValues_nc = Rep_cfun eValues"

lemma [code]: "eValues_nc \<epsilon> = {}"
  by (simp add: upstream_abbrev eValues_nc_def)

lemma [code]: "eValues_nc ((updis Tick) && s) = eValues_nc s"
  by (simp add: upstream_abbrev eValues_nc_def)

lemma [code]: "eValues_nc ((updis (EventMsg e)) && s) = insert e (eValues_nc s)"
  by (simp add: upstream_abbrev eValues_nc_def)

lemma [code_abbrev]: "eValues_nc s = eValues\<cdot>s"
  by (simp add: eValues_nc_def)



lemma [nitpick_simp]: "eshdts_nc \<epsilon> = \<epsilon>"
  by (simp add: eshdts_nc_def)

lemma [nitpick_psimp]: "s \<noteq> \<epsilon> \<Longrightarrow> eshdts_nc s = (if shd s = Tick then \<epsilon> else lscons_u (inv_EventMsg_code (shd s)) (eshdts_nc (srt_nc s)))"
  by (metis (no_types, lifting) eshdts_event eshdts_nc_def eshdts_tick inv_EventMsg_code.elims lscons_conv lscons_u_def srt_nc_def surj_scons up_code_abbrev)



lemma [nitpick_simp]: "tsdrop_nc 0 s = s"
  by (simp add: tsdrop_nc_def upstream_abbrev)

lemma [nitpick_psimp]: "n \<noteq> 0 \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow> shd s = Tick \<Longrightarrow> tsdrop_nc n s = tsdrop_nc (n - 1) (srt_nc s)"
  by (metis EventStream.tsdrop_tick add_0_iff add_eq_if srt_nc_def surj_scons tsdrop_nc_def)

lemma [nitpick_psimp]: "n \<noteq> 0 \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> Tick \<Longrightarrow> tsdrop_nc n s = tsdrop_nc n (srt_nc s)"
  by (metis inverseEventMsg.cases not0_implies_Suc srt_nc_def surj_scons tsdrop_event tsdrop_nc_def)



lemma [nitpick_simp]: "esnth_nc n = eshdts_nc o (tsdrop_nc n)"
  apply(simp add: o_def)
  by (metis cfcomp2 eshdts_nc_def esnth_def esnth_nc_def tsdrop_nc_def)


lemma [nitpick_simp]: "eValues_nc stream_bottom_nc = {}"
  by (simp add: upstream_abbrev eValues_nc_def stream_bottom_nc_def)

lemma [nitpick_psimp]: "s \<noteq> stream_bottom_nc \<Longrightarrow> shd s = Tick \<Longrightarrow> eValues_nc s = eValues_nc (srt_nc s)"
  by (metis eValues_nc_def evalues_tick srt_nc_def stream_bottom_code_abbrev surj_scons)

lemma [nitpick_psimp]: "s \<noteq> stream_bottom_nc \<Longrightarrow> shd s \<noteq> Tick \<Longrightarrow> eValues_nc s = insert ((inv EventMsg) (shd s)) (eValues_nc (srt_nc s))"
  by (metis eValues_nc_def evalues_event event_inv inverseEventMsg.cases scases shd1 srt_nc_def srt_supconc stream_bottom_code_abbrev)

end

