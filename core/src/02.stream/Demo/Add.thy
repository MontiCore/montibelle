theory Add
imports stream.Stream

begin


definition merge:: "('a  \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a stream \<rightarrow> 'b stream \<rightarrow> 'c stream" where
"merge f \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. f (fst s3) (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"



subsection \<open>@{term merge}\<close>

lemma merge_cont:"cont(\<lambda>s1 s2 . smap (\<lambda> s3. f (fst s3) (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2))"
  by(intro cont2cont)

lemma merge_unfold: "merge f\<cdot>(\<up>x \<Zcat> xs)\<cdot>(\<up>y\<Zcat> ys) = \<up>(f x y) \<Zcat> merge f\<cdot>xs\<cdot>ys"
  by(simp add: merge_def)

lemma merge_snth[simp]: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (merge f\<cdot>xs\<cdot>ys) = f (snth n xs) (snth n ys)"
  apply(induction n arbitrary:xs ys)
  apply (metis Fin_02bot merge_unfold lnless_def lnzero_def shd1 slen_empty_eq snth_shd surj_scons)
  apply(case_tac xs rule: scases;simp)
  apply(case_tac ys rule: scases;simp)
  by (simp add: merge_unfold)
lemma merge_eps1[simp]: "merge f\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: merge_def)

lemma merge_eps2[simp]: "merge f\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: merge_def)

lemma [simp]: "srt\<cdot>(merge f\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs)) = merge f\<cdot>as\<cdot>bs"
  by (simp add: merge_unfold)

lemma merge_len [simp]: "#(merge f\<cdot>as\<cdot>bs) = min (#as) (#bs)"
by(simp add: merge_def)

lemma merge_commutative: assumes "\<And> a b. f a b = f b a"
  shows "merge f\<cdot>as\<cdot>bs = merge f\<cdot>bs\<cdot>as"
  apply(rule snths_eq)
   apply (simp add: min.commute)
  by (simp add: assms)




definition add:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"add \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) + (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

lemma "cont (\<lambda> s1 s2 . smap (\<lambda> s3. (fst s3) + (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2))"
by simp


lemma add2smapsuc_helper:" Suc = (\<lambda>z. z+1)"
by auto


lemma "add = merge plus"
by(simp add: add_def merge_def)

lemma add_unfold: "add\<cdot>(\<up>x \<Zcat> xs)\<cdot>(\<up>y\<Zcat> ys) = \<up>(x+y) \<Zcat> add\<cdot>xs\<cdot>ys"
  by(simp add: add_def)

lemma add_snth: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (add\<cdot>xs\<cdot>ys) = snth n xs + snth n ys"
  by (simp add: add_def smap_snth_lemma szip_nth)

lemma add_eps1[simp]: "add\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: add_def)

lemma add_eps2[simp]: "add\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: add_def)

lemma [simp]: "srt\<cdot>(add\<cdot>(\<up>a \<Zcat> as)\<cdot>(\<up>b \<Zcat> bs)) = add\<cdot>as\<cdot>bs"
  by (simp add: add_unfold)

lemma add_commu_helper: assumes "\<And>y. add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  shows "add\<cdot>(\<up>a \<Zcat> x)\<cdot>y = add\<cdot>y\<cdot>(\<up>a \<Zcat> x)"
  apply(cases "y = \<epsilon>")
   apply auto[1]
  by (metis (no_types, lifting) Groups.add_ac(2) assms add_unfold surj_scons)

lemma add_commutative: "add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  apply(induction x arbitrary: y)
    apply(simp_all)
  by (metis add_commu_helper stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma add_len: assumes "xs\<noteq>\<bottom>" and "u\<noteq>\<bottom>"
  shows "#(add\<cdot>xs\<cdot>(u && ys)) = lnsuc\<cdot>(#(add\<cdot>(srt\<cdot>xs)\<cdot>ys))"
  by (metis (no_types, lifting) add_unfold assms(1) assms(2) slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)


lemma add2smapsuc:"add\<cdot>((\<up>1)\<^sup>\<infinity>)\<cdot>s=smap (Suc)\<cdot>s"
  by (metis add_eps2 add_unfold plus_1_eq_Suc rek2smap sinftimes_unfold)

lemma add2smap_f: "add\<cdot>((\<up>x)\<^sup>\<infinity>) = smap (\<lambda>z. z+x)"
apply(rule cfun_eqI)
by (metis (no_types, lifting) add_commutative add_eps2 add_unfold rek2smap sinftimes_unfold)



lemma add2ID_h:"add\<cdot>((\<up>0)\<^sup>\<infinity>)\<cdot>s=ID\<cdot>s"
proof(induction s rule: ind)
  case 1
  then show ?case 
    by simp
next
case 2
  then show ?case
    by simp
next
  case (3 a s)
  then show ?case
    by (metis ID1 add_unfold semiring_normalization_rules(5) sinftimes_unfold)
qed

lemma add2ID:"add\<cdot>\<up>0\<^sup>\<infinity> = ID"
by (simp add: add2ID_h cfun_eqI)



end