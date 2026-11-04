theory TsynStreamEx
imports stream.TsynStream StreamScanlEx

begin


text \<open>Auxiliary function for @{term tsynRemDups}.\<close>
fun tsynRemDups_h :: "'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> 'a tsyn)" where
  "tsynRemDups_h x eps = (eps, x)" |
  "tsynRemDups_h x y = (if x = y then (eps, x) else (y, y))"


text \<open>@{term tsynRemDups}: Remove all duplicates from the stream.\<close>
definition tsynRemDups :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where 
  "tsynRemDups = sscanlA tsynRemDups_h eps"


text \<open>Auxiliary function for @{term tsynScanlExt}.\<close>
fun tsynScanlExt_h :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's \<Rightarrow> 'a tsyn \<Rightarrow> ('b tsyn \<times> 's)" where
  "tsynScanlExt_h f s (Msg m) = (Msg (fst (f s m)), (snd (f s m)))" |
  "tsynScanlExt_h f s eps = (eps, s)"

text \<open>@{term tsynScanlExt}: Apply a function elementwise to the input stream. Behaves like 
        @{term tsynMap}, but also takes a state as additional input to the function. For the first 
        computation an initial state is provided.\<close>
definition tsynScanlExt :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's)) \<Rightarrow> 's \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanlExt f = sscanlA (tsynScanlExt_h f)"

text \<open>@{term tsynScanl}: Apply a function elementwise to the input stream. Behaves like 
  @{term tsynMap}, but also takes the previously generated output element as additional input to 
  the function. For the first computation an initial value is provided.\<close>
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanl f i = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i"

text \<open>Auxiliary function for @{term tsynDropWhile}.\<close>
fun tsynDropWhile_h :: "('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> bool)" where
  "tsynDropWhile_h f x eps = (eps, x)"|
  "tsynDropWhile_h f True (Msg x) = (if f x then (eps, True) else ((Msg x), False))" |
  "tsynDropWhile_h f False (Msg x) = ((Msg x), False)"

text \<open>@{term tsynDropWhile}: Check each element of the stream and remove elements satisfying f.\<close>
definition tsynDropWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynDropWhile f =  sscanlA (tsynDropWhile_h f) True"



text \<open>Each element of @{term sValues} of @{term sscanlA} is in the range of @{term fst} of f\<close>
lemma sscanla_sValues: "sValues\<cdot>(sscanlA f i\<cdot>s) \<subseteq> { fst(f i a) | i a. True }"
  by (induction s  arbitrary: i rule: ind, auto)






text \<open>@{term tsynRemDups} insertion lemma.\<close>
lemma tsynremdups_insert: "tsynRemDups\<cdot>s = sscanlA tsynRemDups_h eps\<cdot>s"
  by (simp add: tsynRemDups_def)

text \<open>@{term tsynRemDups} is strict.\<close>
lemma tsynremdups_strict [simp]: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_insert)

text \<open>@{term tsynRemDups} distributes over concatenation.\<close>
lemma tsynremdups_sconc_msg:
  "tsynRemDups\<cdot>(\<up>(Msg a) \<Zcat> as) = \<up>(Msg a) \<Zcat> sscanlA tsynRemDups_h (Msg a)\<cdot>as"
  by (simp add: tsynremdups_insert)
 
text \<open>@{term tsynRemDups} ignores empty time-slots.\<close>
lemma tsynremdups_sconc_eps: "tsynRemDups\<cdot>(\<up>eps \<Zcat> s) = \<up>eps \<Zcat> tsynRemDups\<cdot>s"
  by (simp add: tsynremdups_insert)

text \<open>@{term tsynRemDups} does nothing on a singleton stream as there can't be a duplicate.\<close>
lemma tsynremdups_singleton_msg: "tsynRemDups\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  by (metis sconc_snd_empty sscanla_bot tsynremdups_sconc_msg)

text \<open>@{term tsynRemDups} ignores empty time-slots.\<close>
lemma tsynremdups_singleton_eps: "tsynRemDups\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynRemDups_def)

text \<open>@{term tsynRemDups} leaves the length of a stream unchanged.\<close>
lemma tsynremdups_slen: "#(tsynRemDups\<cdot>s) = #s"
  by (simp add: tsynremdups_insert)

lemma tsynremdups_h_tsynlen: "tsynLen\<cdot>(sscanlA tsynRemDups_h a\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s arbitrary: a rule: tsyn_ind)
  case adm
  then show ?case
    by (simp add: admI contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case 
    apply (simp add: sscanla_step)
    apply (auto)
    apply (simp add: tsynlen_sconc_eps tsynlen_sconc_msg)
    using dual_order.trans less_lnsuc apply blast
    by (simp add: tsynlen_sconc_msg)
next
  case (eps s)
  then show ?case by (simp add: tsynremdups_sconc_eps tsynlen_sconc_eps)
qed

text \<open>@{term tsynRemDups} leaves the length of a tsyn-stream unchanged.\<close>
lemma tsynremdups_tsynlen: "tsynLen \<cdot> (tsynRemDups\<cdot>ts) <= tsynLen \<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by (simp add: admI contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_sconc_eps)
next
  case (msg m s)
  then show ?case 
    apply (simp add: tsynremdups_sconc_msg)
    apply (simp add: tsynlen_sconc_msg)
    apply (rule tsynremdups_h_tsynlen)
    done
qed

text \<open>Abstraction of @{term sscanlA} execution on @{term tsynRemDups_h} on the state \<open>(\<M> m)\<close> 
        equals srcdups executed on abstracted stream stepping with m.\<close>
lemma tsynremdups_h_tsynabs:
  "tsynAbs\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) = srcdups\<cdot>(sdropwhile (\<lambda>x. x = m)\<cdot>(tsynAbs\<cdot>s))"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_eps tsynremdups_sconc_eps tsynabs_sconc_msg 
                    tsynremdups_sconc_msg srcdups_step)

text \<open>Abstraction of @{term tsynRemDups} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_tsynabs: "tsynAbs\<cdot>(tsynRemDups\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_eps tsynremdups_sconc_eps tsynabs_sconc_msg 
      tsynremdups_sconc_msg srcdups_step tsynremdups_h_tsynabs)

text \<open>@{term tsynRemDups_h} is subset of @{term sValues} of a stream @{term union} eps\<close>
lemma tsynremdups_h_sValues: "sValues\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) \<subseteq> sValues\<cdot>s \<union> {eps}"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union)
  by blast+

text \<open>@{term tsynRemDups} is subset of @{term sValues} of a stream @{term union} eps\<close>
lemma tsynremdups_sValues: "sValues\<cdot>(tsynRemDups\<cdot>s) \<subseteq> sValues\<cdot>s \<union> {eps}"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union, blast)
  apply (metis (no_types, opaque_lifting) Un_commute Un_insert_left insert_mono sValues2un 
         sup_bot.left_neutral tsynremdups_sconc_msg tsynremdups_h_sValues)
  by (simp add: tsynremdups_sconc_eps)

text \<open>@{term tsynRemDups} doesn't change the @{term tsynValues} of a stream\<close>
lemma tsynremdups_tsyndom: "tsynValues\<cdot>(tsynRemDups\<cdot>s) = tsynValues\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynremdups_tsynabs)

text \<open>@{term tsynRemDups} test on finite stream.\<close>
lemma tsynremdups_test_finstream:
  "tsynRemDups\<cdot>(<[eps, Msg (1 :: nat), Msg (1 :: nat), eps, eps, Msg (1 :: nat), Msg (2 :: nat),
   eps, Msg (2 :: nat)]>) = 
   <[eps, Msg (1 :: nat), eps, eps, eps, eps, Msg (2 :: nat), eps, eps]>"
  by (simp add: tsynremdups_insert)

(*
text \<open>@{term tsynRemDups} test on infinitely many time-slots.\<close>
lemma tsynremdups_test_infstream:  "tsynRemDups\<cdot>(<[Msg (1 :: nat), Msg (1 :: nat)]> \<Zcat> ((<[eps]>)\<^sup>\<infinity>)) 
  = <[Msg (1 :: nat), eps]> \<Zcat> ((<[eps]>)\<^sup>\<infinity>)"
  apply (simp add: tsynremdups_insert)
  apply (subst rek2sinftimes [of "sscanlA tsynRemDups_h (\<M> 1::nat)\<cdot>\<up>eps\<^sup>\<infinity>" "\<up>eps\<^sup>\<infinity>"], simp_all)
  apply(subst s2sinftimes, simp_all)
  apply(subst sinftimes_unfold)
  by (simp add: tsynremdups_sconc_eps)
  
  
   
(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynRemDups_fix_h\<close>
(* ----------------------------------------------------------------------- *)

declare tsynRemDups_fix_h.simps [simp del]

text \<open>@{term tsynRemDups_fix} is strict.\<close>
lemma tsynremdups_fix_h_strict [simp]: "tsynRemDups_fix_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>"
  by (fixrec_simp)

text \<open>@{term tsynRemDups_fix} without option ignores message.\<close>
lemma tsynremdups_fix_h_sconc_msg_none:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<Zcat> as)\<cdot>None = \<up>(Msg a) \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix} removes message if it is equal to the given option.\<close>
lemma tsynremdups_fix_h_sconc_msg_some_eq:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<Zcat> as)\<cdot>(Some (Discr (Msg a))) 
     = \<up>eps \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix} ignores message if it is not equal to the given option.\<close>
lemma tsynremdups_fix_h_sconc_msg_some_neq:
  assumes "a \<noteq> b"
  shows "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<Zcat> as)\<cdot>(Some (Discr (Msg b))) 
           = \<up>(Msg a) \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  using assms
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} ignores empty time-slots.\<close>
lemma tsynremdups_fix_h_sconc_eps_none:
  "tsynRemDups_fix_h\<cdot>(\<up>eps \<Zcat> as)\<cdot>None = \<up>eps \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>None"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} ignores empty time-slots even with a given option.\<close>
lemma tsynremdups_fix_h_sconc_eps_some:
  "tsynRemDups_fix_h\<cdot>(\<up>eps \<Zcat> as)\<cdot>(Some (Discr (Msg a))) 
    = \<up>eps \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} leaves the length of the stream unchanged.\<close>
lemma tsynremdups_fix_h_slen_some: "#(tsynRemDups_fix_h\<cdot>s\<cdot>(Some (Discr (\<M> m)))) = #s"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (case_tac "x = z")
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_eq)
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_neq)
  by (simp add: tsynremdups_fix_h_sconc_eps_some)

text \<open>@{term tsynRemDups_fix_h} leaves the length of the stream unchanged.\<close>
lemma tsynremdups_fix_h_slen_none: "#(tsynRemDups_fix_h\<cdot>s\<cdot>None) = #s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_slen_some)
  by (simp add: tsynremdups_fix_h_sconc_eps_none)

lemma tsynremdups_fix_h_tsynlen_some: "tsynLen\<cdot>(tsynRemDups_fix_h\<cdot>s\<cdot>(Some (Discr (\<M> m)))) <= tsynLen\<cdot>s"
proof(induction s arbitrary: m rule: tsyn_ind)
case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (metis (no_types, lifting) dual_order.strict_implies_order inf_ub le2lnle
 lnsuc_lnle_emb order.not_eq_order_implies_strict tsynlen_sconc_msg tsynlen_sconc_eps
           tsynremdups_fix_h_sconc_msg_some_eq tsynremdups_fix_h_sconc_msg_some_neq)
next
case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_fix_h_sconc_eps_some)
qed

lemma tsynremdups_fix_h_tsynlen_none: "tsynLen\<cdot>(tsynRemDups_fix_h\<cdot>s\<cdot>None) <= tsynLen\<cdot>s"
proof (induction s rule: tsyn_ind)
  case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (simp add: tsynlen_sconc_msg tsynremdups_fix_h_sconc_msg_none
                      tsynremdups_fix_h_tsynlen_some)
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_fix_h_sconc_eps_none)
qed
  
text \<open>@{term tsynRemDups_fix_h} test on finite stream.\<close>
lemma tsynremdups_fix_h_test_finstream:
  "tsynRemDups_fix_h\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>)\<cdot>None = 
   <[eps, Msg (1 :: nat), eps, eps]>"
  by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sup'_def 
      tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_sconc_msg_some_eq 
      tsynremdups_fix_h_sconc_eps_none tsynremdups_fix_h_sconc_eps_some tsynremdups_fix_h_strict)

text \<open>@{term tsynRemDups_fix_h} test on infinite stream.\<close>
lemma tsynremdups_fix_h_test_infinstream:
  "tsynRemDups_fix_h\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>\<infinity>)\<cdot>None = 
   <[eps, Msg (1 :: nat)]> \<Zcat> (<[eps]>\<infinity>)"
  apply (subst sinftimes_unfold)
  apply (simp add: tsynremdups_fix_h_sconc_eps_none tsynremdups_fix_h_sconc_msg_none
                   tsynremdups_fix_h_sconc_eps_some tsynremdups_fix_h_sconc_msg_some_eq)
  apply (subst rek2sinftimes [of "tsynRemDups_fix_h\<cdot>\<up>eps \<Zcat> \<up>(\<M> 1::nat) \<Zcat> \<up>eps \<Zcat> \<up>(\<M> 1::nat)\<infinity>\<cdot>(Some (Discr (\<M> 1::nat)))" "\<up>eps\<infinity>"], simp_all)
  apply (subst sinftimes_unfold)
  oops

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynRemDups_fix\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynRemDups_fix} insertion lemma.\<close>
lemma tsynremdups_fix_insert: "tsynRemDups_fix\<cdot>s = tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynRemDups_fix_def)

text \<open>@{term tsynRemDups_fix} is strict.\<close>
lemma tsynremdups_fix_strict [simp]: "tsynRemDups_fix\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_fix_insert)

text \<open>@{term tsynRemDups_fix} distributes over concatenation.\<close>
lemma tsynremdups_fix_sconc_msg:
  "tsynRemDups_fix\<cdot>(\<up>(Msg a) \<Zcat> as) = \<up>(Msg a) \<Zcat> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_msg_none)

text \<open>@{term tsynRemDups_fix} ignores empty time-slots.\<close>
lemma tsynremdups_fix_sconc_eps: "tsynRemDups_fix\<cdot>(\<up>eps \<Zcat> s) = \<up>eps \<Zcat> tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_eps_none)

text \<open>@{term tsynRemDups_fix} leaves the length of a stream unchanged.\<close>
lemma tsynremdups_fix_slen: "#(tsynRemDups_fix\<cdot>s) = #s"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_slen_none)

lemma tsynremdups_fix_tsynlen: "tsynLen\<cdot>(tsynRemDups_fix\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s rule: tsyn_ind)
  case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case 
    apply (simp add: tsynremdups_fix_sconc_msg tsynlen_sconc_msg)
    by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_tsynlen_none tsynremdups_fix_h_tsynlen_some)
next
  case (eps s)
  then show ?case 
    apply (simp add : tsynremdups_fix_sconc_eps tsynlen_sconc_eps)
    by (simp add: tsynremdups_fix_h_tsynlen_none)
qed

text \<open>Abstraction of @{term tsynRemDups_fix} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_fix_tsynabs: "tsynAbs\<cdot>(tsynRemDups_fix\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)" 
  oops

text \<open>@{term tsynRemDups_fix} test on finite stream.\<close>
lemma tsynremdups_fix_test_finstream:
  "tsynRemDups_fix\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>) 
     = <[eps, Msg (1 :: nat), eps, eps]>"
  by (metis tsynremdups_fix_h_test_finstream tsynremdups_fix_insert)

text \<open>@{term tsynRemDups_fix} test on infinite stream.\<close>
lemma tsynremdups_fix_test_infinstream:
  "tsynRemDups_fix\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>\<infinity>) 
     = <[eps, Msg (1 :: nat)]> \<Zcat> (<[eps]>\<infinity>)"
  oops
(*
  by (metis tsynremdups_fix_h_test_infinstream tsynremdups_fix_insert)
*)

text \<open>Abstraction of @{term tsynRemDups_fix} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_fix_tsynabs: "tsynAbs\<cdot>(tsynRemDups_fix\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)" 
  oops
  *)





text \<open>@{term tsynScanlExt} insertion lemma.\<close>
lemma tsynscanlext_insert: "tsynScanlExt f i\<cdot>s = sscanlA (tsynScanlExt_h f) i\<cdot>s"
  by (simp add: tsynScanlExt_def)

text \<open>@{term tsynScanlExt} maps the empty stream on the empty stream.\<close>
lemma tsynscanlext_strict [simp]: "tsynScanlExt f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} distributes over concatenation.\<close>
lemma tsynscanlext_sconc_msg: 
  "tsynScanlExt f i\<cdot>(\<up>(Msg a) \<Zcat> as) = \<up>(Msg (fst (f i a))) \<Zcat> (tsynScanlExt f (snd (f i a))\<cdot>as)"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} ignores empty time-slots.\<close>
lemma tsynscanlext_sconc_eps: "tsynScanlExt f i\<cdot>(\<up>eps \<Zcat> s) = \<up>eps \<Zcat> (tsynScanlExt f i\<cdot>s)"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} maps the singleton stream containing a message a to the
        singleton stream containing the message received by applying f to the message.\<close>
lemma tsynscanlext_singleton: "tsynScanlExt f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (\<lambda>x. fst (f i x)) a)"
  by (cases a, simp_all add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} leaves the length of a stream unchanged.\<close>
lemma tsynscanlext_slen: "#(tsynScanlExt f i\<cdot>s) = #s"
  by (simp add: tsynscanlext_insert)

lemma tsynscanlext_tsynlen: "tsynLen\<cdot>(tsynScanlExt f i\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s arbitrary: i rule: tsyn_ind)          
  case adm
  then show ?case 
    apply (rule admI)
    apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
    done
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (simp add: tsynscanlext_sconc_msg tsynlen_sconc_msg)
next
  case (eps s)
then show ?case  by (simp add: tsynlen_sconc_eps tsynscanlext_sconc_eps)
qed

text \<open>Abstraction of @{term tsynScanlExt} equals sscanlA executed on abstracted stream.\<close>
lemma tsynscanlext_tsynabs: "tsynAbs\<cdot>(tsynScanlExt f i\<cdot>s) = sscanlA f i\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s arbitrary: i rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanlext_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynscanlext_sconc_eps tsynabs_sconc_eps)

text \<open>@{term ifEqualThenZero} Auxiliary function for tsynScanlExt finite test. Checks whether
 both input nats x and y are equal and if so returns tuple of 0, otherwise returns tuple of y\<close>
fun ifEqualThenZero :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat)" where
  "ifEqualThenZero x y = (if x = y then (0, 0) else (y, y))"

text \<open>@{term tsynScanlExt} test on finite nat tsyn-stream.\<close>
lemma tsynscanlext_test_finstream:
  "tsynScanlExt ifEqualThenZero 0\<cdot>(<[Msg 5, Msg 3, Msg 3, eps]>) = <[Msg 5, Msg 3, Msg 0, eps]>"
  by (simp add: tsynscanlext_insert)



text \<open>This lemma makes it possible to filter eps-elements from the input before applying a
        @{term sscanlA2}\<close>
lemma sscanlA2_epsfilter_input: assumes "\<And> x. (f x eps) = (x,eps)" 
  shows "tsynAbs\<cdot>(sscanlAsnd f a\<cdot>s) = tsynAbs\<cdot>(sscanlAsnd f a\<cdot>(sfilter {e. e \<noteq> eps}\<cdot>s))"
  apply(induction s arbitrary: a rule: tsyn_ind)
  apply(rule admI)
  by (simp_all add: tsynabs_sconc assms contlub_cfun_arg contlub_cfun_fun lub_mono2)


text \<open>@{term tsynScanl} insertion lemma.\<close>
lemma tsynscanl_insert: "tsynScanl f i\<cdot>s = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i\<cdot>s"
  by (simp add: tsynScanl_def)

text \<open>@{term tsynScanl} maps the empty stream on the empty stream.\<close>
lemma tsynscanl_strict [simp]: "tsynScanl f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanl_insert)

text \<open>@{term tsynScanl} maps the singleton stream containing message a to the singleton stream
containing the message received by applying f to a.\<close>
lemma tsynscanl_singleton: "tsynScanl f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (f i) a)"
  by (simp add: tsynscanl_insert tsynscanlext_singleton)

text \<open>@{term tsynScanl} distributes over concatenation.\<close>
lemma tsynscanl_sconc_msg: 
  "tsynScanl f i\<cdot>(\<up>(Msg a) \<Zcat> as) = \<up>(Msg (f i a)) \<Zcat> (tsynScanl f (f i a)\<cdot>as)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg)

text \<open>@{term tsynScanl} ignores empty time-slots.\<close>
lemma tsynscanl_sconc_eps: "tsynScanl f i\<cdot>(\<up>eps \<Zcat> s) = \<up>eps \<Zcat> (tsynScanl f i\<cdot>s)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_eps)

text \<open>@{term tsynScanl} leaves the length of a stream unchanged.\<close>
lemma tsynscanl_slen: "#(tsynScanl f i\<cdot>s) = #s"
  by (simp add: tsynscanl_insert tsynscanlext_slen)

text \<open>@{term tsynScanl} test on finite nat tsyn-stream.\<close>
lemma tsynscanl_test_finstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]>) = <[Msg 3, Msg 7]>"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg tsynscanlext_singleton)

text \<open>@{term tsynScanl} test on infinite nat tsyn-stream.\<close>
lemma tsynscanl_test_infinstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]> \<Zcat> ((<[eps]>)\<^sup>\<infinity>)) = <[Msg 3, Msg 7]> \<Zcat> ((<[eps]>)\<^sup>\<infinity>)"
  apply (simp add: tsynscanl_sconc_msg)
  oops
  

text \<open>The length of @{term sscanlA2} without @{term eps} of input and output is the same, if the
function f does not introduce or eliminate @{term eps} from the stream.\<close>
lemma sccanla2_tsynlen:
  assumes "\<And> a. snd (f a eps) = eps"
      and "\<And> a. \<forall>m. snd (f a (\<M> m)) \<noteq> eps"
    shows "tsynLen\<cdot>(sscanlAsnd f a\<cdot>s) = tsynLen\<cdot>s"
  apply (induction s arbitrary: a rule: tsyn_ind)
  apply (rule admI)
  apply (simp_all add: assms contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (subst (1 2) tsynlen_sconc_msg2)
  by (simp_all add: assms tsynlen_sconc_eps)

text \<open>Same as @{term sccanla2_tsynlen}, but with another formulation of the second assumption..\<close>
lemma sccanla2_tsynlen2:
  assumes "\<And> a. snd (f a eps) = eps"
      and "\<And> a m. m \<noteq> eps ==> snd (f a m) \<noteq> eps"
    shows "tsynLen\<cdot>(sscanlAsnd f a\<cdot>s) = tsynLen\<cdot>s "
  apply (induction s arbitrary: a rule: tsyn_ind)
  apply (rule admI)
  apply (simp_all add: assms contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (subst (1 2) tsynlen_sconc_msg2)
  by (simp_all add: assms tsynlen_sconc_eps)


text \<open>@{term tsynDropWhile} insertion lemma.\<close>
lemma tsyndropwhile_insert: "tsynDropWhile f\<cdot>s = sscanlA (tsynDropWhile_h f) True\<cdot>s "
  by(simp add: tsynDropWhile_def)
    
text \<open>@{term tsynDropWhile} is strict.\<close>
lemma tsyndropwhile_strict [simp]: "tsynDropWhile f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsyndropwhile_insert)

text \<open>If the head passes the predicate f, then the head of the result of @{term tsynDropWhile} 
        will be eps.\<close>
lemma tsyndropwhile_sconc_msg_t:
  assumes "f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<Zcat> s) = \<up>eps \<Zcat> tsynDropWhile f\<cdot>s"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the head fails the predicate f and is not eps, then the head of the result of 
        @{term tsynDropWhile} will start with the head of the input.\<close>
lemma tsyndropwhile_sconc_msg_f:
  assumes "\<not>f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<Zcat> s) = \<up>(Msg a) \<Zcat> s"
  using assms
  apply (simp add: tsyndropwhile_insert)
  apply (induction s arbitrary: f a rule: tsyn_ind, simp_all)
  using inject_scons by fastforce+

text \<open>If the head is eps, then the head of the result of @{term tsynDropWhile} will be eps.\<close>    
lemma tsyndropwhile_sconc_eps: "tsynDropWhile f\<cdot>(\<up>eps \<Zcat> s) = \<up>eps \<Zcat> tsynDropWhile f\<cdot>s"
  by (simp add: tsyndropwhile_insert)
    
text \<open>If the only element in a singleton stream passes the predicate f, then @{term tsynDropWhile} 
        will produce the singleton stream with eps.\<close>
lemma tsyndropwhile_singleton_msg_t: 
  assumes "f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>eps"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the only element in a singleton stream fails the predicate f, then @{term tsynDropWhile} 
        does not change the stream.\<close>    
lemma tsyndropwhile_singleton_msg_f:
  assumes "\<not>f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the only element in a singleton stream passes is eps, then @{term tsynDropWhile} 
        will produce the singleton stream with eps.\<close>
lemma tsyndropwhile_singleton_eps: "tsynDropWhile f\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsyndropwhile_insert)
  
text \<open>@{term tsynDropWhile} does not change the length of a stream.\<close>
lemma tsyndropwhile_slen: "#(tsynDropWhile f\<cdot>s) = #s "
  by (simp add: tsyndropwhile_insert)

lemma tsyndropwhile_tsynlen: "tsynLen\<cdot>(tsynDropWhile f\<cdot>s) \<le> tsynLen\<cdot>s"
  proof(induction s rule: tsyn_ind)
    case adm
    then show ?case 
      apply (rule admI)
      by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
  next
    case bot
    then show ?case by simp
  next
    case (msg m s)
    then show ?case 
      apply (case_tac "f m = True")
      apply (simp add: tsyndropwhile_sconc_msg_t tsynlen_sconc_eps tsynlen_sconc_msg)
      using dual_order.trans less_lnsuc apply blast
      by (simp add: tsyndropwhile_sconc_msg_f)
  next
    case (eps s)
    then show ?case by (simp add: tsyndropwhile_sconc_eps tsynlen_sconc_eps)
  qed

text \<open>Abstraction of @{term tsynDropWhile} equals sdropwhile executed on abstracted stream.\<close>
lemma tsyndropwhile_tsynabs: "tsynAbs\<cdot>(tsynDropWhile f\<cdot>s) = sdropwhile f\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "f x")
  apply (simp add: tsyndropwhile_sconc_msg_t tsynabs_sconc_msg tsynabs_sconc_eps)
  apply (simp add: tsyndropwhile_sconc_msg_f tsynabs_sconc_msg)
  by (simp add: tsyndropwhile_sconc_eps tsynabs_sconc_eps)

text \<open>@{term tsynDropWhile} is idempotent.\<close>    
lemma tsyndropwhile_idem: "tsynDropWhile f\<cdot>(tsynDropWhile f\<cdot>s) = tsynDropWhile f\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (metis tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t tsyndropwhile_sconc_eps)
  by (simp add: tsyndropwhile_sconc_eps)

lemma sdropwhile_neps: "sdropwhile (\<lambda>x. x = eps)\<cdot>s \<noteq> \<up>eps \<Zcat> sa"
  using sdropwhile_resup by auto

lemma sdropwhile_eps_cases [case_names bot msg]:
  assumes bot: "sdropwhile (\<lambda>x. x = eps)\<cdot>x = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. sdropwhile (\<lambda>x. x = eps)\<cdot>x = \<up>(Msg m) \<Zcat> s \<Longrightarrow> P (\<up>(Msg m) \<Zcat> s)"
  shows "P (sdropwhile (\<lambda>x. x = eps)\<cdot>x)"
  using assms
  apply (rule_tac x = "sdropwhile (\<lambda>x. x = eps)\<cdot>x" in tsyn_cases)
  apply simp_all
  by (simp add: sdropwhile_neps)

lemma sdropwhile_shd_ex:
  assumes "tsynAbs\<cdot>s \<noteq> \<epsilon>"
  obtains m where "shd (sdropwhile (\<lambda>x. x = eps)\<cdot>s) = Msg m"
  by (metis assms sdropwhile_neps surj_scons tsyn.exhaust tsynabs_sdropwhile_neps)

text \<open>@{term sValues} of @{term tsynDropWhile} is subset of @{term sValues} of 
        the original stream @{term union} eps.\<close>

lemma tsyndropwhile_sValues: "sValues\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> sValues\<cdot>s \<union> {eps}"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union, blast)
  apply (metis (no_types, opaque_lifting) insert_commute insert_is_Un insert_subset sValues2un 
         subset_insertI2 subset_refl tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t)
  by (simp add: tsyndropwhile_sconc_eps)

text \<open>@{term tsynValues} of @{term tsynDropWhile} is subset of @{term tsynValues} of 
        the original stream.\<close>
lemma tsyndropwhile_tsyndom: "tsynValues\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> tsynValues\<cdot>s" 
  by (simp add: sdropwhile_sValues tsynabs_tsyndom tsyndropwhile_tsynabs)

text \<open>@{term tsynDropWhile} test on finite stream.\<close>    
lemma tsyndropwhile_test_finstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(<[Msg 1, Msg 1, eps, Msg 1, Msg 2, Msg 1]>) 
     = <[eps, eps, eps, eps, Msg 2, Msg 1]>"
  by (simp add: tsyndropwhile_insert)
(*
text \<open>@{term tsynDropWhile} test on infinite stream.\<close>
lemma tsyndropwhile_test_infstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, eps, Msg 2]>)\<^sup>\<infinity>) = 
     <[eps, eps, Msg 2]> \<Zcat> ((<[Msg 1, eps, Msg 2]>)\<^sup>\<infinity>)"
proof -
  have split_stream: "(<[Msg 1, eps, Msg 2]>)\<infinity> = \<up>(Msg 1) \<Zcat> \<up>eps \<Zcat> \<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>)"
    by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sconc_scons' 
        sinftimes_unfold sup'_def)
  have first_elem_t: "(\<lambda> a. a \<noteq> (2 :: nat)) 1"
    by simp
  from split_stream first_elem_t have drop_first: 
      "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, eps, Msg 2]>)\<infinity>) =
         \<up>eps \<Zcat> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>eps \<Zcat> \<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>)))"
    by (metis (mono_tags, lifting) inverseMsg.simps(2) tsyndropwhile_sconc_msg_t)      
  then have drop_second:
      "\<up>eps \<Zcat> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>eps \<Zcat> \<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>))) =
         \<up>eps \<Zcat> \<up>eps \<Zcat>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>)))"
    by (simp add: tsyndropwhile_sconc_eps)
  then have drop_third:
      " \<up>eps \<Zcat> \<up>eps \<Zcat>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>))) = 
          \<up>eps \<Zcat> \<up>eps \<Zcat> \<up>(Msg 2) \<Zcat> (<[Msg 1, eps, Msg 2]>\<infinity>)"
    by (simp add: tsyndropwhile_sconc_msg_f)
  from drop_first drop_second drop_third show ?thesis 
    by simp
qed
*)






text \<open>@{term tsynSum} maps a stream to a stream containing the sum of read messages.\<close>
definition tsynSum :: 
  "'a :: {zero, countable, monoid_add, ab_semigroup_add, plus} tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynSum = tsynScanl plus 0"

text \<open>@{term tsynSum} insertion lemma.\<close>
lemma tsynsum_insert: "tsynSum\<cdot>s = tsynScanl plus 0\<cdot>s"
  by (simp add: tsynSum_def)

text \<open>@{term tsynSum} is strict.\<close>
lemma tsynsum_strict [simp]: "tsynSum\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynsum_insert)

text \<open>@{term tsynSum} maps the stream containing only a singleton to the singleton.\<close>
lemma tsynsum_singleton: "tsynSum\<cdot>(\<up>a) = \<up>a"
  by (cases a, simp_all add: tsynsum_insert tsynscanl_singleton)

lemma "tsynScanl plus n\<cdot>(\<up>(Msg a) \<Zcat> as) = \<up>(Msg (n + a)) \<Zcat> tsynMap (plus a)\<cdot>(tsynScanl plus n\<cdot>as)"
  apply (induction as arbitrary: a n rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanl_singleton)         
  oops

text \<open>@{term tsynSum} test on infinite stream.\<close>
lemma tsynsum_test_infmsg: "tsynSum\<cdot>(\<up>(Msg 0)\<^sup>\<infinity>) = \<up>(Msg 0)\<^sup>\<infinity>"
  by (metis add.left_neutral s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_msg)

text \<open>@{term tsynSum} test on infinite stream containing no messages.\<close>
lemma tsynsum_test_infeps: "tsynSum\<cdot>(\<up>eps\<^sup>\<infinity>) = \<up>eps\<^sup>\<infinity>"
  by (metis s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_eps)
(*
text \<open>Auxiliary function for @{term tsynsum_even}.\<close>
lemma tsynsum_even_h:
  assumes "tsynValues\<cdot>s \<subseteq> {n. even n}"
    and "even m"
  shows "tsynValues\<cdot>(tsynScanl plus m\<cdot>s) \<subseteq> {n. even n}"
  using assms
  apply (induction s arbitrary: m rule: tsyn_ind)
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
  apply (simp add: tsynscanl_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsynscanl_sconc_eps tsyndom_sconc_eps)

text \<open>@{term tsynSum} leaves the domain unchanged if the stream contains only even messages.\<close>
lemma tsynsum_even: assumes "tsynValues\<cdot>s \<subseteq> {n. even n}"
  shows "tsynValues\<cdot>(tsynSum\<cdot>s) \<subseteq> {n. even n}"
  by (simp add: assms tsynsum_insert tsynsum_even_h)
*)

end