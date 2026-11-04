theory TsynStreamFilterWithBool
  imports TsynStream Stream 
begin


definition fitTime :: "'a tsyn stream \<rightarrow> 'b stream \<rightarrow> 'b tsyn stream" where
"fitTime \<equiv> fix\<cdot>(\<Lambda> h xs ys. slookahd\<cdot>xs\<cdot>(\<lambda> x. if x = Eps 
      then \<up>Eps \<Zcat> (h\<cdot>(srt\<cdot>xs)\<cdot>ys)
      else slookahd\<cdot>ys\<cdot>(\<lambda> y. \<up>(TSynMsg (y)) \<Zcat> (h\<cdot>(srt\<cdot>xs)\<cdot>(srt\<cdot>ys)))))"

lemma fitTime_cont[simp]: "cont (\<lambda> h xs ys. slookahd\<cdot>xs\<cdot>(\<lambda> x. if x = Eps 
      then \<up>Eps \<Zcat> (h\<cdot>(srt\<cdot>xs)\<cdot>ys)
      else  slookahd\<cdot>ys\<cdot>(\<lambda> y. \<up>(TSynMsg (y)) \<Zcat> (h\<cdot>(srt\<cdot>xs)\<cdot>(srt\<cdot>ys)))))"
  by (intro cont2cont) 

lemma fitTime_strict[simp]: "fitTime\<cdot>\<epsilon>\<cdot>ys = \<epsilon>" 
  by (subst fitTime_def [THEN fix_eq2],simp)

lemma fitTime_unfold:
  "fitTime\<cdot>xs\<cdot>ys =
     slookahd\<cdot>xs\<cdot>(\<lambda> x. if x = Eps 
      then \<up>Eps \<Zcat> (fitTime\<cdot>(srt\<cdot>xs)\<cdot>ys)
      else slookahd\<cdot>ys\<cdot>(\<lambda> y. \<up>(TSynMsg (y)) \<Zcat> (fitTime\<cdot>(srt\<cdot>xs)\<cdot>(srt\<cdot>ys))))"
  unfolding fitTime_def 
  apply (subst fix_eq2, simp)
  using  [[simp_trace_new]] by simp

lemma fitTime_msg_rec: "fitTime\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) = \<up>(TSynMsg b) \<Zcat> fitTime\<cdot>as\<cdot>bs"
  by (simp add: fitTime_unfold)

lemma fitTime_eps_rec: "fitTime\<cdot>(\<up>\<sim> \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim> \<Zcat> fitTime\<cdot>as\<cdot>(\<up>b \<Zcat> bs)"
  by (simp add: fitTime_unfold)

lemma stream_decomp_nonempty[simp]:
  assumes "bs \<noteq> \<epsilon>"
  shows   "bs = \<up>(shd bs) \<Zcat> (srt\<cdot>bs)"
  using assms by (cases bs) simp_all

lemma fitTime_msg_stream: "bs \<noteq> \<epsilon> \<Longrightarrow> fitTime\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>bs = \<up>(TSynMsg (shd bs)) \<Zcat> fitTime\<cdot>as\<cdot>(srt\<cdot>bs)"  
  by (simp add: fitTime_unfold)

definition filter :: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
"filter \<equiv> \<Lambda> s1 s2. smap (\<lambda> pair. if inverseMsg (snd pair) then fst pair else \<sim>)\<cdot>(szip\<cdot>s1\<cdot>(fitTime\<cdot>s1\<cdot>s2))"



lemma slen_fitTime: "#xs \<le> # ys \<longrightarrow> #(fitTime\<cdot>xs\<cdot>ys) = #xs"
proof (induction xs arbitrary: ys rule: tsyn_ind)
  case adm
  then show ?case
    apply (rule admI)
    apply (simp add: contlub_cfun_arg)
    sorry
  case bot
    then show ?case 
      by simp
  next
  case (msg m s)
    then show ?case 
     apply (case_tac ys)
     apply auto
      apply (simp only: fitTime_msg_rec) 
      by (metis slen_scons)
  case (Eps s)
  then show ?case
     apply (case_tac ys)
     apply auto
     apply (simp add: fitTime_eps_rec) 
     by (metis dual_order.trans less_lnsuc slen_scons)
qed

lemma slen_stsynfilter: "#ys = \<infinity> \<longrightarrow> #(filter\<cdot>xs\<cdot>ys) = #xs"
  apply(simp add: filter_def slen_fitTime)
  done

lemma filter_empty_left: "filter\<cdot>\<epsilon>\<cdot>s = \<epsilon>"
  by (simp add: filter_def)


(* Filtering with empty boolean stream yields empty stream  \<rightarrow> not valid with new filter
lemma filter_empty_right: "filter\<cdot>s\<cdot>\<epsilon> = \<epsilon>"
  apply (simp add: filter_def)
  done  *)

lemma [simp]: "fitTime\<cdot>(\<up>\<sim>)\<cdot>(\<up>True) = \<up>\<sim>"
  by (simp add: fitTime_unfold)


lemma filter_single_true: "filter\<cdot>(\<up>a)\<cdot>(\<up>True) = \<up>a"
  by (simp add: filter_def fitTime_unfold)

lemma filter_single_false: "filter\<cdot>(\<up>a)\<cdot>(\<up>False) = \<up>\<sim>"
  by (simp add: filter_def fitTime_unfold)

lemma filter_eps_any: "filter\<cdot>(\<up>\<sim>)\<cdot>(\<up>b) = \<up>\<sim>"
  by (simp add: filter_def fitTime_unfold)

lemma filter_eps_head: "filter\<cdot>(\<up>\<sim>)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim>"
  by (simp add: filter_def fitTime_unfold)

lemma filter_eps_infinite: "#s = \<infinity> \<longrightarrow> filter\<cdot>(\<up>\<sim>)\<cdot>s = \<up>\<sim>"
  apply (cases s) 
  by (simp_all add: filter_eps_head)

lemma filter_eps_up_and_infinite: "#s = \<infinity> \<longrightarrow> filter\<cdot>(\<up>\<sim>)\<cdot>(up\<cdot>x && s) = \<up>\<sim>"
  by (metis discr.exhaust filter_eps_head lscons_conv)

lemma filter_eps_updis_and_infinite: "#s = \<infinity> \<longrightarrow> filter\<cdot>(\<up>\<sim>)\<cdot>(updis x && s) = \<up>\<sim>"
  by (simp add: filter_eps_head lscons_conv) 

lemma filter_eps_cons_infinite: "#s = \<infinity> \<longrightarrow> filter\<cdot>(\<up>\<sim>)\<cdot>(\<up>x \<Zcat> s) = \<up>\<sim>"
  by (simp_all add: filter_eps_head)

lemma filter_eps_lscons_infinite: "#s = \<infinity>  \<longrightarrow> filter\<cdot>(\<up>\<sim>)\<cdot>(x && s) = \<up>\<sim>"
  by (simp add: filter_def fitTime_msg_rec fitTime_unfold)

lemma filter_msg_head: "filter\<cdot>(\<up>(TSynMsg a))\<cdot>(\<up>b \<Zcat> bs) = (if b then \<up>(TSynMsg a) else \<up>\<sim>)"
  by (simp add: filter_def fitTime_msg_rec fitTime_unfold)

lemma filter_msg_stream: "filter\<cdot>(\<up>(TSynMsg a))\<cdot>bs = (if bs = \<epsilon> then \<epsilon> else (if shd bs then \<up>(TSynMsg a) else \<up>\<sim>))"
  apply (cases bs)
  apply (simp add: filter_def fitTime_unfold)
  by (simp add: filter_msg_head)

lemma filter_msg_up_head: "filter\<cdot>(\<up>(TSynMsg a))\<cdot>(up\<cdot>b && bs) = (if (undiscr b) then \<up>(TSynMsg a) else \<up>\<sim>)"
  apply (simp add: filter_msg_stream)
  by (metis Discr_undiscr lscons_conv shd1)

lemma filter_msg_updis_head: "filter\<cdot>(\<up>(TSynMsg a))\<cdot>(updis b && bs) = (if b then \<up>(TSynMsg a) else \<up>\<sim>)"
  apply (simp add: filter_msg_stream)
  by (simp add: lscons_conv)

lemma inj_Iup [simp]: "inj Iup"
  by (intro injI) simp  

lemma inv_Iup_up [simp]: "inv Iup (up\<cdot>x) = x"
  by (simp add: up_def cont_Iup inv_f_f)

lemma filter_msg_lscons: "filter\<cdot>(\<up>(TSynMsg a))\<cdot>(b && bs) = 
                      (if b = \<bottom> then \<epsilon> else (if undiscr (inv Iup b) then \<up>(TSynMsg a) else \<up>\<sim>))"
  apply (cases b)
   apply (simp add: filter_def fitTime_unfold)
  by (simp add: filter_msg_up_head)

lemma filter_msg_tuple_infinite: "#s = \<infinity> \<longrightarrow> filter\<cdot>(\<up>(TSynMsg (m, True)))\<cdot>s 
                            = (if shd s then \<up>(TSynMsg (m, True)) else \<up>\<sim>)"
  by (simp add: filter_msg_stream)

(* (* Filtering the first message of a stream with singetlon stream True returns that message as singelton *)
lemma filter_msg_head_true: "filter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>True) = \<up>(TSynMsg a)"
  apply (simp add: filter_def)
  apply (simp add: fitTime_unfold)
  done   \<rightarrow> not valid with new filter  *)

(* (*Filtering the first message of a stream with singetlon stream False returns singelton stream ~ *)
lemma filter_msg_head_false: "filter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>False) = \<up>\<sim>"
  apply  (simp add: filter_def fitTime_unfold) done \<rightarrow> not valid with new filter  *)

lemma filter_msg_true_rec: "filter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>True \<Zcat> bs) = \<up>(TSynMsg a) \<Zcat> filter\<cdot>as\<cdot>bs"
  by (simp add: filter_def fitTime_msg_rec)

lemma filter_msg_false_rec: "filter\<cdot>(\<up>(TSynMsg a) \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs) = \<up>\<sim> \<Zcat> filter\<cdot>as\<cdot>bs"
  by (simp add: filter_def fitTime_msg_rec)

lemma filter_eps_bool_rec: "filter\<cdot>(\<up>\<sim> \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) = \<up>\<sim> \<Zcat> filter\<cdot>as\<cdot>(\<up>b \<Zcat> bs)"
  by (simp add: filter_def fitTime_eps_rec)

lemma filter_val_true_rec: "filter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>True \<Zcat> bs) = 
          (if a = \<sim> then \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>(\<up>True \<Zcat> bs) else \<up>a \<Zcat> filter\<cdot>as\<cdot>bs)"
  apply (simp add: filter_def fitTime_unfold)  
  done

lemma filter_val_updis_true_rec: "filter\<cdot>(\<up>a \<Zcat> as)\<cdot>(updis True && bs) = 
        (if a = \<sim> then \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>(updis True && bs) else \<up>a \<Zcat> filter\<cdot>as\<cdot>bs)"
  by (simp add: lscons_conv filter_def fitTime_unfold)

lemma filter_val_false_rec: "filter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>False \<Zcat> bs)
          = (if a = \<sim> then \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>(\<up>False \<Zcat> bs) else \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>bs)"
  by (simp add: filter_def fitTime_unfold)   

lemma filter_val_updis_false_rec: "filter\<cdot>(\<up>a \<Zcat> as)\<cdot>(updis False && bs) 
         = (if a = \<sim> then \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>(updis False && bs) else \<up>\<sim>  \<Zcat> filter\<cdot>as\<cdot>bs)"
  by (simp add: lscons_conv filter_def fitTime_unfold)

lemma filter_inf_true: "filter\<cdot>s\<cdot>((\<up>True)\<^sup>\<infinity>) = s"
 apply (induction s)
  apply auto
  apply (simp add: filter_def fitTime_unfold)
  using sinftimes_unfold filter_val_true_rec
  by (metis (no_types, lifting))

lemma filter_single_inf_false: "filter\<cdot>(\<up>a)\<cdot>((\<up>False)\<^sup>\<infinity>) = \<up>\<sim>"
  apply (subst sinftimes_unfold)
  apply (simp add: fitTime_unfold filter_def)
  done

lemma filter_length_le: "#(filter\<cdot>s\<cdot>ora) \<le> #s"
  apply (simp add: filter_def) 
  done

lemma filter_inf_false_rec: "filter\<cdot>(\<up>a \<Zcat> s)\<cdot>((\<up>False)\<^sup>\<infinity>) = \<up>\<sim> \<Zcat> filter\<cdot>s\<cdot>((\<up>False)\<^sup>\<infinity>)"
   apply (subst sinftimes_unfold)
   apply (simp add: filter_val_false_rec)
  by (metis sinftimes_unfold)

lemma filter_inf_const_false: "filter\<cdot>((\<up>a)\<^sup>\<infinity>)\<cdot>((\<up>False)\<^sup>\<infinity>) = ((\<up>\<sim>)\<^sup>\<infinity>)"
  by (metis filter_inf_false_rec s2sinftimes sinftimes_unfold)  


lemma filter_preserves_cons_msg: "filter\<cdot>(\<up>(TSynMsg m) \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) 
                              = filter\<cdot>(\<up>(TSynMsg m))\<cdot>(\<up>b) \<Zcat> filter\<cdot>as\<cdot>bs" 
  using filter_single_false filter_single_true
  by (metis (full_types) filter_msg_false_rec filter_msg_true_rec)

lemma filter_preserves_cons: "filter\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs) 
                    = filter\<cdot>(\<up>a)\<cdot>(\<up>b) \<Zcat> (if a = Eps then filter\<cdot>as\<cdot>(\<up>b \<Zcat> bs) else filter\<cdot>as\<cdot>bs)" 
  using filter_single_false filter_single_true filter_val_false_rec filter_val_true_rec
by (cases b; simp add: filter_single_true filter_single_false
                       filter_val_true_rec filter_val_false_rec)


lemma cont_filter: "cont (\<lambda> s. filter\<cdot>s\<cdot>ora)"
  using  [[simp_trace_new mode=full]]
  by simp

lemmas filter_lemmas =
  filter_empty_left filter_single_true filter_single_false
  filter_eps_any filter_eps_head filter_eps_infinite filter_eps_up_and_infinite
  filter_eps_updis_and_infinite filter_eps_cons_infinite 
  filter_msg_head filter_msg_stream filter_msg_up_head filter_msg_updis_head
  filter_msg_lscons filter_msg_tuple_infinite filter_val_true_rec
  filter_msg_true_rec filter_msg_false_rec filter_val_updis_true_rec
  filter_eps_bool_rec  filter_val_updis_false_rec
  filter_inf_true  filter_length_le filter_val_updis_false_rec
   filter_inf_const_false filter_inf_false_rec filter_single_inf_false
   cont_filter filter_preserves_cons_msg

lemma lnsuc_as_1_plus_fin: "lnsuc\<cdot>x = 1 + Fin x"
  apply auto
  apply (subst Suc_eq_plus1)
  by (simp add: one_lnat_def)

lemma inv_fin_append_id: "inv Fin x\<star>\<up>a \<Zcat> \<up>a = x\<star>\<up>a \<Zcat> \<up>a"
  by simp

lemma inv_fin_suc: "inv Fin (1 + Fin x)\<star>\<up>a =  inv Fin x\<star>\<up>a \<Zcat> \<up>a "
  apply simp
  apply (simp add: one_lnat_def)
  using sntimes_Suc2 by auto

end