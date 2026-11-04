theory StreamCodegen

imports EventStream inc.LNat inc.Codegen inc.LNatcodegen


begin



default_sort "countable"

definition lscons_u ::"'a \<Rightarrow> 'a stream  \<Rightarrow> 'a stream" where
"lscons_u \<equiv> (\<lambda>a0. Rep_cfun (lscons\<cdot>(Iup (Discr a0))))"

lemma ls_code_abbrev[code_abbrev]:" lscons_u a0 a1 = lscons\<cdot>(Iup (Discr a0))\<cdot>a1"
  by (simp add: lscons_u_def)


setup_domain "'a stream" "lscons_u"

instantiation stream::(countable)bot_nc
begin

definition "bot_nc_stream = stream_bottom_nc"

instance
  apply(standard)
  by(simp add: bot_nc_stream_def stream_bottom_nc_def)
end



(*
primrec lnat2enat :: "lnat \<Rightarrow> enat" where
"lnat2enat (Fin n) = n" |
"lnat2enat (Inf') = (\<infinity>::enat)"

lemma "lnat2enat n = (if (n\<noteq>Inf') then (inv Fin n) else (\<infinity>::enat))"
  by (metis Fin_0 add.right_neutral add_eq_0_iff_both_eq_0 plus_lnat_def lnat2enat.simps(1) lnat2enat.simps(2))
*)

lemma up_code_abbrev [code_abbrev]:"Iup a = up\<cdot>a"
  apply (simp add: up_def)
  apply(subst beta_cfun, simp add: cont_Iup)
  ..

lemma upstream_abbrev[code_abbrev]: "updis x && xs = \<up>x \<Zcat> xs"
  by (simp add: lscons_conv)


definition equal_stream2::"'a stream \<Rightarrow> 'a stream \<Rightarrow> bool" where
"equal_stream2 a b \<equiv> (a = b)"

code_printing
code_module test  \<rightharpoonup> (SML)
\<open>fun streamequal a b = a=b \<close> for constant equal_stream2
|constant equal_stream2 \<rightharpoonup> (SML) "streamequal"

code_printing
  code_module test  \<rightharpoonup> (Scala)
\<open>object StreamEqual {
  def streamequal[A](a:Any,b:Any): Boolean = a==b
}\<close> for constant equal_stream2
|constant equal_stream2 \<rightharpoonup> (Scala) "StreamEqual.streamequal"

instantiation stream::("{equal,countable}") equal
begin
definition equal_stream::"'a stream \<Rightarrow> 'a stream \<Rightarrow> bool" where
"equal_stream a b \<equiv> equal_stream2 a b "
instance
  apply(intro_classes)
  by(simp add: equal_stream2_def equal_stream_def)
end




lemma shd_c[ccode]:"shd ((updis a)&&b) = a"
  by(simp add:shd_def)


lemma [ccode]: "sdrop (Suc n)\<cdot>((updis a)&&b) = sdrop n\<cdot>b"
  and [ccode]: "sdrop 0\<cdot>s=s"
  and [ccode]: "sdrop n\<cdot>\<epsilon> = \<epsilon>"
  apply auto[3]
  by (simp add: lscons_conv)


lemma [code_abbrev]:"slen\<cdot>lnx = len lnx"
  by (simp add: len_stream_def)

lemma [ccode]: "slen\<cdot>(\<epsilon>) = (0)" and
      [ccode]: "slen\<cdot>(updis a && as) = lnsuc\<cdot>(#as)"
  apply(subst slen_def [THEN fix_eq2], simp add: lnzero_def)
  apply (simp add: len_stream_def)
  by (subst slen_def [THEN fix_eq2], simp add: lnle_def)

lemma [code_abbrev]:"(if (x=y) then False else (Fin x \<le> Fin y)) = (Fin x < Fin y)"
  by (simp add: less_le)



lemma [ccode]: "smap f\<cdot>(updis a && as) = \<up> (f a) \<Zcat> smap f\<cdot>as"
    and [ccode]: "smap f\<cdot>\<epsilon>=\<epsilon>"
  apply (simp add: lscons_conv)
  by simp

lemma [code_abbrev]:"smap_nc a = Rep_cfun (smap a)"
  by (simp add: smap_nc_def)

lemma [ccode]:"emap f\<cdot>s = smap (map_event f)\<cdot>s"
  by(simp add: emap_def)


lemma [ccode]:"efilter P\<cdot>\<epsilon> = \<epsilon>"
and [ccode]:"efilter P\<cdot>(updis (EventMsg a) && as) =  (if P a then \<up>(EventMsg a) \<Zcat> efilter P\<cdot>as else efilter P\<cdot>as)"
and [ccode]:"efilter P\<cdot>(updis Tick && as) = \<up>Tick \<Zcat> efilter P\<cdot>as"
  by(simp_all add: lscons_conv)


lemma [ccode]: "szip\<cdot>(updis a && as)\<cdot>(updis b && bs) = \<up> (a,b) \<Zcat> szip\<cdot>as\<cdot>bs"
and [ccode]: "szip\<cdot>as\<cdot>\<epsilon>=\<epsilon>"
and [ccode]: "szip\<cdot>\<epsilon>\<cdot>bs=\<epsilon>"
  apply (auto simp add: lscons_conv)
  done



lemma [code]: " \<epsilon> \<sqsubseteq> as = True"  and
      [code]: "(updis a && as) \<sqsubseteq>  (updis b && bs) =  (if a\<noteq>b then False else as \<sqsubseteq> bs) "
  by simp+


lemma [ccode]:"sconc s1\<cdot> \<epsilon> = s1" and
      [ccode]:"sconc \<epsilon>\<cdot>s2 = s2" and
      [ccode]:"sconc (updis a && s1)\<cdot>s2 = updis a && (sconc s1\<cdot>s2)"
  apply simp+
  using sconc_scons' by blast

lemma[code]:"Rep_cfun (conc s1) = sconc_nc s1"
  by(simp add: sconc_nc_def)


definition "pconc_nc a= Rep_cfun (pconc a)"

lemma[code]:"pconc_nc(a::'a::conc,b::'b::conc) (c,d) = (a\<Zcat>\<Zcat>c,b\<Zcat>\<Zcat>d)"
  by(simp add: pconc_nc_def)

lemma [code]:"Rep_cfun (pconc a)= pconc_nc a"
  by(simp add: pconc_nc_def)


definition stake1::"nat \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"stake1 \<equiv> stake"

lemma [code_abbrev]:"stake1 = stake"
  by (simp add: stake1_def)

lemma [ccode]: "stake1 0\<cdot>s = \<epsilon>"
  and [ccode]: "stake1 (Suc n)\<cdot>(updis a && as) = updis a && stake1 n\<cdot>as"
  by(simp add: stake1_def)+



lemma sscanlaut_bot[ccode]:"sscanlA x xa\<cdot>\<epsilon> = bot_nc"
  by (simp add: botnc_eq_bot)

lemma sscanlaut_step[ccode]:"sscanlA f s\<cdot>(updis a && b) = (snd(f s a)) \<Zcat>\<Zcat> sscanlA f (fst (f s a))\<cdot>b"
  by (simp add: lscons_conv)

hide_fact sscanlA_def




lemma [ccode]:"sEventToList\<cdot>s = sscanlA toListHelper []\<cdot>s"
  by(simp add: sEventToList_def)


lemma [ccode]: "sscanlAOne x xa\<cdot>\<epsilon> = \<epsilon>"
  and [ccode]:"sscanlAOne f s\<cdot>(updis a && b) =
        \<up>(snd(f s a)) \<Zcat> sscanlAOne f (fst (f s a))\<cdot>b"
  by (simp add: sscanlAOne_def lscons_conv)+


lemma [code]:"s2list \<epsilon> = []" and
      [code]:"s2list (updis a && s) = (if #s=\<infinity> then undefined else a#(s2list s))"
  apply simp
  apply(auto simp add: s2list_def lscons_conv)[1]
  by (metis fair_sdrop infI inject_scons s2list2lcons s2list_def sconc_fst_inf sdropl6)



lemma slisttotimedsimps[ccode]:"sListToEvent\<cdot>\<epsilon> = \<epsilon>"
  and [ccode]:"sListToEvent\<cdot>(updis ([]) && s) = (\<up>Tick) \<Zcat> sListToEvent\<cdot>s"
  and [ccode]:"sListToEvent\<cdot>((updis(x#xs)) && s) = \<up>(EventMsg x) \<Zcat> sListToEvent\<cdot>((\<up>(xs)) \<Zcat> s)"
  by(simp_all add: lscons_conv)


lemma [code]:"sinftimes \<epsilon> = \<epsilon>"
  by auto

(*
subsection\<open>relator\<close>

lemma  [code]: "rel_stream P \<epsilon> ys = (ys = \<epsilon>)"
  by (simp add: rel_stream_Nil)

lemma [code]: "rel_stream P xs \<epsilon> = (xs = \<epsilon>)"
  by (simp add: rel_stream_Nil2 )

lemma  [code]:
  "rel_stream P (updis x && xs) (updis y && ys) = (P x y \<and> rel_stream P xs ys)"
  by(simp add: rel_stream_Cons)
*)


lemma [code]:"sntimes 0 s = \<epsilon>" and
      [code]:"sntimes (Suc n) s = s \<Zcat> (sntimes n s)"
  by auto

lemma [ccode]:"sValues\<cdot>\<epsilon> = {}" and
      [ccode]:"sValues\<cdot>(updis a && s) = {a} \<union> sValues\<cdot>(s)"
  by(auto simp add: lscons_conv)


lemma [code]: "snth 0 (updis a && s) = a" and
      [code]: "snth (Suc n) (updis a && s) = snth n s"
   apply(auto)[1]
   apply (simp add: shd_c; fail)
  by (simp add: snth_rt)


lemma [code]: "tlen (\<epsilon> ::  'a::{tlen,countable} stream) = bot_nc"
  by (simp add: bot_nc_lnat_def)

lemma [code]: "tlen ((Iup (Discr v)) && (rt :: 'a::{tlen,countable} stream)) = lAdd\<cdot>(tlen v)\<cdot>(tlen rt)"
  by (simp add: tlen_stream_def up_code_abbrev ladd_insert)


definition "sreachable_nda_all_nc_h transition = Rep_cfun (sreachable_nda_all transition)"
definition "sreachable_nda_all_nc transition S = Rep_cfun (sreachable_nda_all_nc_h transition S)"


lemma [code_abbrev]:
  "sreachable_nda_all_nc transition S Init = sreachable_nda_all transition\<cdot>S\<cdot>Init"
  by (simp add: sreachable_nda_all_nc_h_def sreachable_nda_all_nc_def)


lemma [code]:
  "Rep_cfun (sreachable_nda_all transition) = sreachable_nda_all_nc_h transition"
  by (simp add: sreachable_nda_all_nc_h_def)

lemma [code]:
  "Rep_cfun (sreachable_nda_all_nc_h transition S) = sreachable_nda_all_nc transition S"
  by (simp add: sreachable_nda_all_nc_h_def sreachable_nda_all_nc_def)

lemma [code]:"sreachable_nda_all_nc transition Init \<epsilon> = Init"
  by(simp add: sreachable_nda_all_nc_def sreachable_nda_all_nc_h_def)

lemma [code]:
  "sreachable_nda_all_nc transition Init (updis a && s) =  Init \<union> sreachable_nda_all_nc transition (\<Union>state\<in>Init. transition state a) s"
  by (simp add: lscons_conv sreachable_nda_all_unfold sreachable_nda_all_nc_def sreachable_nda_all_nc_h_def)

lemma[code]: "Rep_cfun (sreachableStates aut) = sreachable_nda_all_nc (\<lambda> s m. fst ` ((autTransition\<cdot>aut) s m)) (fst ` (autInitConfig\<cdot>aut))"
  by (simp add: sreachableStates_def sreachable_nda_all_nc_def
      sreachable_nda_all_nc_h_def)


instantiation stream::("{narrowing,countable,typerep}")narrowing
begin

function narrowing_stream :: "('a stream) narrowing" where
"narrowing_stream n =  Quickcheck_Narrowing.sum
    (Quickcheck_Narrowing.cons bot_nc)
    (Quickcheck_Narrowing.apply (Quickcheck_Narrowing.apply
      (Quickcheck_Narrowing.cons lscons_u_nc) narrowing) narrowing_stream) n"
by pat_completeness simp
termination apply(relation "measure nat_of_integer")apply(simp_all, transfer, simp)
proof auto
  fix n d'::integer
  assume a1:"0 \<le> d'"
  assume a2:"d' < n"
  obtain d where d_def:"int_of_integer d' = of_nat d"
    using a1 integer_less_eq_iff zero_le_imp_eq_int by fastforce
  obtain n' where n'_def:"int_of_integer n = of_nat n'"
    using a1 a2 nonneg_int_cases dual_order.trans le_cases
    by (metis less_eq_integer.rep_eq verit_comp_simplify1(3) zero_integer.rep_eq)
  show "nat_of_integer d' < nat_of_integer n"
    using d_def n'_def a2 integer_less_iff nat_of_integer.rep_eq by auto
qed


instance ..
end
(*
subsection \<open>sfoot\<close>

lemma len_rew: "(THE a. lnsuc\<cdot>(Fin a) = #s)= (the_lnat(#s)-1)"
  sorry

lemma [code]: "sfoot s = snth (thelnat(#s)-1) s"
  by (metis len_rew sfoot_def)
*)



setup\<open>
Nitpick_HOL.register_codatatype_global @{typ "'a stream"}
"" (map dest_Const [@{term stream_bottom_nc},@{term lscons_u}])\<close>

lemma [nitpick_simp]:"\<epsilon> = stream_bottom_nc"
  by(simp add: stream_bottom_nc_def)

(*
lemma [nitpick_simp]:"sscanlAutOne_nc f s (lscons_u x xs) = lscons_u (snd (f s x)) (sscanlAutOne_nc f (fst (f s x)) xs)" and
      [nitpick_simp]:"sscanlAutOne_nc f s \<epsilon> = \<epsilon>"
  apply(simp add: ls_code_abbrev sscanlAutOne_nc_def up_code_abbrev lscons_conv)
  by (simp add: c25_nc)
*)

lemma [nitpick_simp]: "sup' a = lscons_u a stream_bottom_nc"
  by (simp add: lscons_u_def stream_bottom_code_abbrev sup'_def up_code_abbrev)



lemma [nitpick_simp]:"shd (lscons_u x xs) = x"
  by(simp add: shd_def lscons_u_def up_code_abbrev)



definition srt_nc :: "'a stream \<Rightarrow> 'a stream" where "srt_nc s = srt\<cdot>s"

lemma
      [nitpick_simp]: "srt_nc (lscons_u x xs) = xs"
  and [nitpick_simp]: "srt_nc stream_bottom_nc = stream_bottom_nc"
  by(simp add: srt_nc_def lscons_u_def up_code_abbrev stream_bottom_nc_def)+




lemma [nitpick_simp]: "sconc_nc stream_bottom_nc bs = bs"
  and [nitpick_simp]: "sconc_nc (lscons_u x xs) bs = lscons_u x (sconc_nc xs bs)"
   apply(simp add: stream_bottom_code_abbrev sconc_nc_def)+
  by (simp add: ls_code_abbrev lscons_conv up_code_abbrev)


lemma [nitpick_simp]: "sValues_nc \<epsilon> = {}"
  and [nitpick_psimp]: "s \<noteq> \<epsilon> \<Longrightarrow> sValues_nc s = {shd s} \<union> sValues_nc (srt_nc s)"
   apply (simp add: c28_nc)
  by (metis sValues2un sValues_code_abbrev srt_nc_def surj_scons)



lemma
      [nitpick_simp]: "slen_nc stream_bottom_nc = 0"
  and [nitpick_psimp]: "s \<noteq> stream_bottom_nc \<Longrightarrow> slen_nc s = lnsuc_nc (slen_nc (srt_nc s))"
  apply(simp add: stream_bottom_nc_def slen_nc_def)
    apply (metis len_stream_def slen_zero)
   apply(simp add: lnsuc_nc_def slen_nc_def srt_nc_def)
  by (metis len_stream_def srt_decrements_length stream_bottom_nc_def)





lemma [nitpick_simp]:"smap_nc f (lscons_u x xs) = lscons_u (f x) (smap_nc f xs)" and
      [nitpick_simp]:"smap_nc f stream_bottom_nc = stream_bottom_nc"
   apply(simp add: ls_code_abbrev smap_nc_def up_code_abbrev lscons_conv; fail)
  by (simp add: c7_nc stream_bottom_nc_def)





lemma [nitpick_simp]: "tlen (stream_bottom_nc :: ('a :: {tlen, countable}) stream) = 0"
and [nitpick_psimp]: "s \<noteq> stream_bottom_nc \<Longrightarrow>
      tlen (s :: ('a :: {tlen, countable}) stream) = (tlen (shd s)) + (tlen (srt_nc s))"
   apply (simp add: stream_bottom_code_abbrev)
  by (metis srt_nc_def stream_bottom_code_abbrev stream_tlen_step surj_scons)




end
