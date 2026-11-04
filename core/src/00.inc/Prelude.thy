
theory Prelude
imports HOLCF "HOL-Eisbach.Eisbach_Tools"
begin

default_sort type

setup_lifting type_definition_cfun

sledgehammer_params [smt_proofs=false]


lemma trivial[simp]: "(Not \<circ> Not) = id"
  by auto

definition rel2map ::   "('c * 'm) set \<Rightarrow> ('c \<rightharpoonup> 'm)"
where rel2map_def: "rel2map r \<equiv> \<lambda>x. (if x \<in> Domain r then Some (SOME a. (x,a) \<in> r) else None)"

lemma dom_relmap[simp]: "Map.dom (rel2map r) = Domain r"
by (simp add: rel2map_def Map.dom_def)

definition unsome :: "'a option \<Rightarrow> 'a" where
"unsome x = (case x of Some y \<Rightarrow> y | None \<Rightarrow> undefined)"

lemma unsomesome[simp]: "unsome (Some x) = x"
  by (simp add: unsome_def)

lemma some_eqI:"sbe \<noteq> None \<and> the sbe = f \<Longrightarrow> Some f = sbe"
  by auto


lemma p2somep:"\<exists>x. P x \<Longrightarrow> (\<forall>x. P x \<longrightarrow> P2 x) \<Longrightarrow> P2 (SOME x. P x)"
  by (simp add: someI_ex)


text \<open>For natural numbers j and k with @{term "j \<le> k"}, @{term "k - j"} is natural as well\<close>
lemma natl1: "(j::nat) \<le> k \<Longrightarrow> \<exists>i. j + i = k"
  by presburger

primrec lrcdups :: "'a list \<Rightarrow> 'a list"
where
  "lrcdups [] = []" |
  "lrcdups (x#xs) = 
     (if xs = [] 
        then [x] 
        else 
          (if x = List.hd xs 
             then lrcdups xs 
             else (x#(lrcdups xs))))"


primrec lscanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"lscanl f e [] = [] " |
"lscanl f e (x#xs) =f e x#(lscanl f (f e x) xs)"

primrec lscanlAg::
"('s \<Rightarrow>'a \<Rightarrow> ('s \<times>'b)) \<Rightarrow> 
's \<Rightarrow> 'a list \<Rightarrow> (('s \<times> 'b) list)" where
"lscanlAg f s [] = []" |
"lscanlAg f s (x#xs) = 
               (f s x)#(lscanlAg f (fst (f s x)) xs)"


definition stateSemList:: "('state \<Rightarrow> 'a \<Rightarrow> 'state \<times> 'b) \<Rightarrow>'state \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"stateSemList f state xs \<equiv> map snd (lscanlAg f state xs)"



  

lemma conf_fun2[simp]: "cont (\<lambda> f. f x)"
  by (simp add: cont_fun)

lemma chain_tord: "chain S \<Longrightarrow> S k \<sqsubseteq> S j \<or> S j \<sqsubseteq> S k"
  using nat_le_linear po_class.chain_mono by blast 


lemma neq_emptyD: "s \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> s"
by auto

lemma cont_pref_eq1I: assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>a \<sqsubseteq> f\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
     
lemma cont_pref_eq2I:  assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>x\<cdot>a \<sqsubseteq> f\<cdot>x\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
    
lemma cfun_arg_eqI:  assumes "(a = b)"
  shows "f\<cdot>a = f\<cdot>b"
  by (simp add: assms)  


lemma beta_cfun_cont_fun:
  assumes "cont f"
  shows "(\<Lambda> x. f (g\<cdot>x))\<cdot>a = f (g\<cdot>a)"
proof -
  have "(\<Lambda> x. f (g\<cdot>x)) = (\<Lambda> x. (Abs_cfun f)\<cdot>(g\<cdot>x))"
    using assms by simp
  also have "... = (\<Lambda> x. ((Abs_cfun f) oo g)\<cdot>x)"
    by simp
  finally have "(\<Lambda> x. f (g\<cdot>x))\<cdot>a = ((Abs_cfun f) oo g)\<cdot>a"
    by simp
  moreover have "... = (Abs_cfun f)\<cdot>(g\<cdot>a)"
    by simp
  also have "... = f (g\<cdot>a)"
    using assms by simp
  ultimately show "(\<Lambda> x. f (g\<cdot>x))\<cdot>a = f (g\<cdot>a)"
    by presburger
qed

lemma abs_cfun_id: "Abs_cfun id\<cdot>x = x"
  using eq_id_iff by fastforce

lemma  SOME_inj_f_eq_insert:
  assumes "inj (Rep_cfun f)"
  shows "(SOME x. (\<lambda>c. f\<cdot>x) = (\<lambda>c. f\<cdot>y)) = y"
proof-
  have "(SOME x. (\<lambda>c. f\<cdot>x) = (\<lambda>c. f\<cdot>y)) = (SOME x. x = y)"
    by (metis assms inj_def)
  thus ?thesis
    by simp
qed

     

lift_definition parComp :: "('a::cpo \<rightarrow> 'b::cpo) \<Rightarrow> ('c::cpo \<rightarrow> 'd::cpo) \<Rightarrow> (('a \<times> 'c) \<rightarrow> ('b \<times> 'd))"
  is "\<lambda>f g. \<lambda>(s1, s2). (f\<cdot> s1, g\<cdot> s2)"
  unfolding cfun_def
  by simp

lift_definition mu :: "(('a::pcpo \<times> 'b::pcpo) \<rightarrow> ('c::pcpo \<times> 'b)) \<Rightarrow> ('a \<rightarrow> ('c \<times> 'b))"
  is "\<lambda>f a::'a. fix\<cdot>(Abs_cfun (\<lambda>(_::'c, d::'b). f\<cdot> (a, d)))"
  unfolding cfun_def
  by simp



lemma less_lubl1: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); X \<sqsubseteq> (\<Squnion>k. Y (k + j))\<rbrakk> \<Longrightarrow> X \<sqsubseteq> (\<Squnion>k. Y k)"
by (subst lub_range_shift [THEN sym, of "Y" "j"], simp+)

lemma less_lubl2:
"\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); chain f; \<And>x. (\<Squnion>k. f k\<cdot>x) = x; \<And>n. f n\<cdot>x \<sqsubseteq> (f n\<cdot>(Lub Y))\<rbrakk> \<Longrightarrow> x \<sqsubseteq> Lub Y"
by (insert lub_mono [of "\<lambda>n. f n\<cdot>x" "\<lambda>n. f n\<cdot>(Lub Y)"], simp)

lemma Suc2plus: "Suc n = Suc 0 + n"
by simp

lemma Suc_def2: "Suc i = i + Suc 0"
by simp

lemma max_in_chainI3: "\<lbrakk>chain (Y::nat\<Rightarrow>'a::cpo); Y i = Lub Y\<rbrakk> \<Longrightarrow> max_in_chain i Y"
  by (simp add: maxinch_is_thelub)

lemma lub_prod2: "\<lbrakk>chain (X::nat \<Rightarrow> 'a::cpo); chain (Y::nat \<Rightarrow> 'b::cpo)\<rbrakk> \<Longrightarrow>
                        (\<Squnion>k. (X k,Y k)) = (Lub X, Lub Y)"
by (subst lub_prod, simp+)

lemma lub_range_shift2: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = (\<Squnion>i. Y (i+j))"
  apply(simp add: lub_def)
  using is_lub_range_shift lub_def by fastforce
  

lemma l42: "chain S \<Longrightarrow> finite_chain S \<Longrightarrow> \<exists>t. (\<Squnion> j. S j) = S t"
using lub_eqI lub_finch2 by auto

lemma finite_chain_lub: fixes Y :: "nat \<Rightarrow> 'a ::cpo"
  assumes "finite_chain Y" and "monofun f"
  shows "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
proof -
  obtain nn :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat" where
    f1: "Lub Y = Y (nn Y)"
    by (meson assms(1) finite_chain_def l42)
  then have "\<forall>n. f (Y n) \<sqsubseteq> f (Y (nn Y))"
    by (metis assms(1) assms(2) finite_chainE is_lub_rangeD1 lub_finch1 max_in_chainI3 monofunE)
  then show ?thesis
    using f1 by (simp add: lub_chain_maxelem)
qed 

lemma adm2cont: 
  fixes f:: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes "monofun f" and "\<And>k. adm (\<lambda>Y. (f Y)\<sqsubseteq>k)" 
  shows "cont f"
  apply(rule Cpo.contI2)    
  apply(auto simp add: assms)[1]
  by (metis (mono_tags) adm_def assms(2) is_ub_thelub)

lemma adm2adm_fst: assumes "adm P" 
  shows "adm (\<lambda>m. P (xs,m))"
proof (rule admI)
  fix Y
  assume "chain Y" and p_i: "\<forall>i. P (xs,Y i)"
  let ?Y = "\<lambda>i. (xs, Y i)"
  have "chain ?Y"
    by (simp add: \<open>chain Y\<close> po_class.chainE)
  hence "P (\<Squnion>i. ?Y i)" by(rule admD [OF \<open>adm P\<close>], simp add: p_i)
  moreover have "(\<Squnion>i. ?Y i) = (xs, \<Squnion>i. Y i)"
    apply(subst lub_prod [OF \<open>chain ?Y\<close>])
    by simp
  ultimately show  "P (xs, \<Squnion>i. Y i)"  
    by simp
qed

lemma adm2adm_snd: assumes "adm P" 
  shows "adm (\<lambda>m. P (m, xs))"
proof (rule admI)
  fix Y
  assume "chain Y" and p_i: "\<forall>i. P (Y i,xs)"
  let ?Y = "\<lambda>i. (Y i, xs)"
  have "chain ?Y"
    by (simp add: \<open>chain Y\<close> po_class.chainE)
  hence "P (\<Squnion>i. ?Y i)" by(rule admD [OF \<open>adm P\<close>], simp add: p_i)
  moreover have "(\<Squnion>i. ?Y i) = (\<Squnion>i. Y i, xs)"
    apply(subst lub_prod [OF \<open>chain ?Y\<close>])
    by simp
  ultimately show  "P (\<Squnion>i. Y i, xs)"  
    by simp
qed

primrec literate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  literate_0:  "literate 0 f s = []" |
  literate_Suc:"literate (Suc n) f s = s#(literate n f (f s))"

text \<open>Iterative conversion of @{term literate} result to a set\<close>
lemma literate_Suc2:
  "set (literate (Suc n) f s) = {s} \<union> set (literate n f (f s))"
by auto

lemma natl3: "{i. x \<le> i \<and> i < Suc n + x} = {x} \<union> {i. Suc x \<le> i \<and> i < Suc n + x}"
by auto

text \<open>Create set of natural numbers from k to n+k-1 by @{term literate}\<close>
lemma literatel1 [simp]: 
  "set (literate n Suc k) = {i. k \<le> i \<and> i < (n + k)}"
apply (rule_tac x="k" in spec)
apply (induct_tac n, simp)
apply (subst literate_Suc2)
apply (rule allI)
apply (erule_tac x="Suc x" in allE)
by (subst natl3, simp)

text \<open>A list of length @{term n} contains at most @{term n} different elements\<close>
lemma card_set_list_le_length: "card (set x) \<le> length x"
apply (induct_tac x, simp+)
by (simp add: card_insert_if)

text \<open>@{term "literate n"} creates lists with length @{term n}\<close>
lemma len_literate[simp]: "length (literate n f k) = n"
apply (rule_tac x="k" in spec)
by (induct_tac n, simp+)

lemma map_map_pair[simp]: "map snd (map (Pair k) a) = a"
by (induct_tac a, simp+)

text \<open>For a list @{term x}, each element in @{term "set x"} appears at some position in
  @{term x}\<close>
lemma from_set_to_nth: "xa \<in> set x \<Longrightarrow> \<exists>k. x!k = xa \<and> k < length x"
apply (simp add: atomize_imp)
apply (induct_tac x, simp+) 
apply (rule conjI, rule impI)
apply (rule_tac x="0" in exI, simp; fail)
apply (rule impI, simp)
apply (erule exE)
by (rule_tac x="Suc k" in exI, simp)

lemma filterl4: "\<lbrakk>\<And>x. Q x \<Longrightarrow> P x; filter P x = []\<rbrakk> \<Longrightarrow> filter Q x = []"
  by (simp add: atomize_imp, induct_tac x, auto)

lemma filterexn:
  assumes"filter P ls = x#xs"
  shows "\<exists>n. P (nth ls n) \<and> (\<forall>m<n. \<not>P (nth ls m)) \<and> n<length ls"
  using Cons_eq_filterD[where P=P and ys=ls and x=x and xs=xs] assms
  apply auto[1]
  by (metis add.commute add_0 in_set_conv_nth less_add_Suc1 nth_Cons_0 nth_append nth_append_length_plus)


lemma list_rinduct_lemma: "\<forall>y. length y = k \<and> (P [] \<and> (\<forall>x xs. P xs \<longrightarrow> P (xs @ [x]))) \<longrightarrow> P y"
apply (induct_tac k, simp)
apply (rule allI)
apply (rule impI)
apply (erule conjE)+
apply (erule_tac x="butlast y" in allE, auto)
apply (erule_tac x="last y" in allE)
apply (erule_tac x="butlast y" in allE, auto)
by (case_tac "y = []", auto)

lemma concat_nth:
  assumes "n < length (concat ls)"
  shows "\<exists>l1 \<in> set ls. \<exists>k \<le> n. concat ls ! n = l1 ! k \<and> k < length l1"
  using assms
  apply (induction ls arbitrary: n)
  apply (simp; fail)
  apply (case_tac "n < length a")
  apply (rule_tac x="a" in bexI)
  apply (rule_tac x="n" in exI)
  apply simp
  apply (simp add: nth_append; fail)
  apply (meson list.set_intros(1); fail)
  apply (simp add: nth_append)
  apply (rule disjI2)
  apply (subgoal_tac "\<exists>l1::'a list\<in>set ls. \<exists>k\<le>(n - length a). concat ls ! (n - length a) = l1 ! k \<and> k < length l1")
  apply (meson diff_le_self le_trans)
  by simp

lemma append_take_nth_drop_id:
  assumes "n < length xs"
  shows "take n xs @ [(xs ! n)] @ drop (Suc n) xs = xs"
  using assms
  apply (induction xs arbitrary: n)
  apply (simp; fail)
  apply simp
  by (metis Cons_nth_drop_Suc append_take_drop_id drop_Suc_Cons length_Cons)


lemma finite_subset1: "finite Y \<Longrightarrow> (\<forall>X. X \<subseteq> Y \<longrightarrow> finite X)"
  by (simp add: finite_subset)

lemma ex_new_if_finitel1:
  "\<lbrakk>finite Y; \<not> finite X\<rbrakk> \<Longrightarrow> \<exists>a. a \<in> X \<and> a \<notin> Y"
apply (rule ccontr, auto)
apply (subgoal_tac "X \<subseteq> Y")
by (frule_tac Y="Y" in finite_subset1, auto)

primrec
  getinj:: "'a set \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) set"
where
  "getinj A 0 = {(0,SOME x. x \<in> A)}" |
  "getinj A (Suc n) = {(Suc n, SOME x. x \<in> A \<and> x \<notin> (snd ` (getinj A n)))} \<union> getinj A n"

text \<open>The result of @{term "getinj A n"} and its projections on the first or
  second attribute are finite\<close>

lemma finite_getinjs[simp]: "finite (getinj A n)"
by (induct_tac n, simp+)

lemma finite_snd_getinjs[simp]: "finite (snd ` (getinj A n))"
by (induct_tac n, simp+)

lemma finite_fst_getinjs[simp]: "finite (fst ` (getinj A n))"
by (induct_tac n, simp+)

text \<open>@{term "getinj A n"} only contains entries for numbers up to @{term n}\<close>
lemma getinjs_l1: "\<forall>k. n < k \<longrightarrow> (k, x) \<notin> getinj A n"
by (induct_tac n, simp+)

text \<open>...especially, it contains no entry for @{term "n+1"}\<close>
lemma getinj_notin[simp]: "(Suc n,x) \<notin> getinj A n"
by (insert getinjs_l1 [of n x A], auto)

text \<open>Projecting to the second component is an injective function on results
  of @{term getinj}\<close>
lemma card_getinj_lemma[simp]: "\<not> finite A \<Longrightarrow> card (snd ` (getinj A n)) = card (getinj A n)"
apply (induct_tac n, simp+)
apply (rule someI2_ex)
apply (rule ex_new_if_finitel1)
by (rule finite_snd_getinjs, simp+)

lemma inj_on_getinj: "\<not> finite A \<Longrightarrow> inj_on snd (getinj A n)"
by (rule eq_card_imp_inj_on, simp+)

text \<open>@{term "getinj X n"} maps @{term n} to something\<close>
lemma getinj_ex[simp]: "\<exists>a. (n,a) \<in> getinj X n"
by (induct_tac n, simp+)

text \<open>For a fixed set @{term "A"}, @{term "getinj A i"} is a chain\<close>
lemma getinj_chain:
  "\<lbrakk>\<not> finite A; (j, x) \<in> getinj A j; j \<le> k\<rbrakk> \<Longrightarrow> (j, x) \<in> getinj A k"
apply (simp add: atomize_imp)
apply (induct_tac k, auto)
by (case_tac "j = Suc n", auto)

lemma inter_union_id:"(x \<union> y) \<inter> x = x"
  by blast

lemma emtpy_reduce[simp]: "(a \<in> (if A then B else {})) = (a \<in> B \<and> A)"
  by (meson empty_iff)


text \<open>The @{term "updis"} command lifts an arbitrary type to a
  discrete pointed partial order.\<close>
abbreviation
  updis :: "'a \<Rightarrow> 'a discr u"
    where "updis \<equiv> (\<lambda>a. up\<cdot>(Discr a))" 

definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

definition upApply2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApply2 f \<equiv> \<Lambda> a b. (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"


lemma updis_exists: assumes "x\<noteq>\<bottom>"
  obtains n where "updis n = x"
  by (metis Discr_undiscr Exh_Up assms)
    
    
    
lemma upapply_mono [simp]: "monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
apply (rule monofunI, auto)
by (metis (full_types, opaque_lifting) discrete_cpo upE up_below)

lemma upapply_lub: assumes "chain Y"
  shows "((\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (\<Squnion>i. Y i))
=(\<Squnion>i. (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (Y i))"
apply (rule finite_chain_lub)
by (simp_all add: assms chfin2finch)

lemma upapply_cont [simp]: "cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upapply_mono by blast

lemma upapply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by (simp add: upApply_def)

lemma upapply_insert: "upApply f\<cdot>a = (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"  
by(simp add: upApply_def)
    
lemma upapply_strict [simp]: "upApply f\<cdot>\<bottom> = \<bottom>"
by(simp add: upApply_def)

lemma upapply_nbot [simp]: "x\<noteq>\<bottom> \<Longrightarrow> upApply f\<cdot>x\<noteq>\<bottom>"
by(simp add: upApply_def)
    
lemma upapply_up [simp]: assumes "x\<noteq>\<bottom>" obtains a where "up\<cdot>a = upApply f\<cdot>x"
by(simp add: upApply_def assms)
  
lemma chain_nbot: assumes "chain Y" and  "(\<Squnion>i. Y i) \<noteq>\<bottom>"
  obtains n::nat where "(\<And>i. ((Y (i+n)) \<noteq>\<bottom>))"
  by (metis assms(1) assms(2) bottomI le_add2 lub_eq_bottom_iff po_class.chain_mono)

lemma upapply2_mono [simp]: 
  "monofun (\<lambda> b. (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x))))"
apply (rule monofunI, auto)
by (metis discrete_cpo upE up_below)

lemma upapply2_cont [simp]:
  "cont (\<lambda>b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: chfindom_monofun2cont)

lemma upapply2_mono2 [simp]: 
  "monofun (\<lambda>a. \<Lambda> b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
apply (rule monofunI)
apply (subst cfun_belowI, auto)
by (metis discrete_cpo upE up_below)

lemma upapply2_cont2 [simp]:
  "cont (\<lambda>a. \<Lambda> b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: chfindom_monofun2cont)

lemma upapply2_rep_eq [simp]: "upApply2 f\<cdot>(updis a)\<cdot>(updis b) = updis (f a b)"
by (simp add: upApply2_def)

lemma upapply2_insert: 
  "upApply2 f\<cdot>a\<cdot>b = (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: upApply2_def)

lemma upapply2_strict [simp]: "upApply2 f\<cdot>\<bottom> = \<bottom>"
by(simp add: upApply2_def)

lemma upapply2_nbot [simp]: "x\<noteq>\<bottom> \<Longrightarrow> y\<noteq>\<bottom> \<Longrightarrow> upApply2 f\<cdot>x\<cdot>y\<noteq>\<bottom>"
by(simp add: upApply2_def)

lemma upapply2_up [simp]: assumes "x\<noteq>\<bottom>" and "y\<noteq>\<bottom>" obtains a where "up\<cdot>a = upApply2 f\<cdot>x\<cdot>y"
by(simp add: upApply2_def assms)
 
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  thus ?thesis
    by force
qed  
  
lemma cont_below_f [simp]: "x \<sqsubseteq> y \<Longrightarrow> (\<Lambda> ya. f\<cdot>x\<cdot>ya) \<sqsubseteq> (\<Lambda> ya. f\<cdot>y\<cdot>ya)"
  by (simp add: cont_pref_eq1I eta_cfun)

lemma cont_below_chain [simp]:"\<forall>Y. chain Y \<longrightarrow> (\<Lambda> y. f\<cdot>(\<Squnion>i. Y i)\<cdot>y) \<sqsubseteq> (\<Squnion>i. \<Lambda> y. f\<cdot>(Y i)\<cdot>y)"
  apply(simp add: contlub_cfun_fun contlub_cfun_arg,auto)
  apply(subst contlub_lambda,auto)
  by (simp add: cfun.lub_cfun cont_pref_eq1I)

lemma cont_lam2cont[simp]:"cont (\<lambda>x. \<Lambda> y. f\<cdot>x\<cdot>y)"
  by(rule contI2, rule monofunI, simp+)

lemma contI2:
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes mono: "monofun f"
  assumes below: "\<And>Y. \<lbrakk>chain Y; chain (\<lambda>i. f (Y i));\<not>finite_chain Y;monofun f\<rbrakk> \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i))"
  shows "cont f"
  apply(rule contI2)
   apply(simp add: assms; fail)
  apply(case_tac "finite_chain Y")
  apply (simp add: finite_chain_lub mono)
  by(simp add: assms)


declare Cpo.cont_if[cont2cont del]
lemma cont_if2 [simp, cont2cont]: "(b \<Longrightarrow> cont f) \<Longrightarrow> (\<not>b \<Longrightarrow> cont g) \<Longrightarrow> cont (\<lambda>x. if b then f x else g x)"
  by (cases b) simp_all

lemma cont2cont_lambda [cont2cont]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont f"
  by (simp add: f) 

lemma cont_compose_mix:"cont f1 \<Longrightarrow> cont (\<lambda>x. f1 (f2\<cdot>x))"
  by(rule cont_compose[of f1],simp_all)

lemma cont2cont_const [cont2cont]: "cont (\<lambda>f. f a)"
  by simp

lemma comp_cont:
  assumes"cont f1"
  and "cont f2"
  shows "cont (f1 \<circ> f2)" 
  by(simp add: comp_def cont_compose assms)

lemma [cont2cont]:"cont f \<Longrightarrow> f\<in> cfun"
  by (simp add: cfun_def)

lemma discr_cont: "monofun f \<Longrightarrow> cont (\<lambda>x. g ((f x)::'a:: discrete_cpo))"
  apply(rule Cpo.contI2)
  apply(rule monofunI, insert monofunE[of f],auto)
  by (metis is_ub_thelub)

lemma discr_cont2: "cont f \<Longrightarrow> cont (\<lambda>x. g ((f x)::'a:: discrete_cpo))"
  by (simp add: cont2mono discr_cont)

lemma discr_cont3: "cont h \<Longrightarrow> cont f \<Longrightarrow> cont (\<lambda>x. ((h x)) ((f x)::'a:: discrete_cpo))"
  by (simp add: cont2cont_fun cont_apply)

lemma cont_compose_snd [cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x. f (snd x))"
  by (simp add: cont_compose)
  
lemma cont_compose_fst [cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x. f (fst x))"
  by (simp add: cont_compose)


fixrec example::"('a::pcpo \<rightarrow> 'a) \<rightarrow> 'a" where
"example\<cdot>f = f\<cdot>(example\<cdot>f)"

lemma "example = (\<mu> example. \<Lambda> f. f\<cdot>(example\<cdot>f))"
  oops

lemma "example\<cdot>f = (\<mu> example. f\<cdot>(example))"
  oops

lemma fix_const: assumes "\<And>x z. z\<cdot>x = g\<cdot>x\<cdot>(z\<cdot>x) \<Longrightarrow> g\<cdot>x\<cdot>(z\<cdot>x) \<sqsubseteq> z\<cdot>x"
  shows  "(\<mu> h. (\<Lambda> x . g\<cdot>x\<cdot>(h\<cdot>x))) = (\<Lambda> x. (\<mu> h. g\<cdot>x\<cdot>h))" 
  apply(rule fix_eqI)
  apply(rule cfun_eqI, auto)
   apply (metis Cfun.cfun.Rep_cfun_inverse fix_eq)
  apply(rule cfun_belowI, auto)
  apply(rule fix_least_below, auto)
  apply(rule assms(1))
  using cfun_eqI beta_cfun
proof -
fix z :: "'a \<rightarrow> 'b" and x :: 'a
  assume a1: "(\<Lambda> x. g\<cdot>x\<cdot>(z\<cdot>x)) = z"
  have "cont (\<lambda>a. g\<cdot>a\<cdot>(z\<cdot>a))"
    by auto
  then show "z\<cdot>x = g\<cdot>x\<cdot>(z\<cdot>x)"
    using a1 by (metis (no_types) beta_cfun)
qed 

lemma abs_cfun_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. cont (h x)"
shows "cont (\<lambda>x. Abs_cfun (h x))"
  by (simp add: assms(1) assms(2) cont2cont_LAM cont2cont_fun)

lemma fix_const': 
  assumes "\<And>x. cont (g x)" and "cont g"  
    and "\<And>x z. z\<cdot>x = g x (z\<cdot>x) \<Longrightarrow> g x (z\<cdot>x) \<sqsubseteq> z\<cdot>x" 
  shows  "(\<mu> h. (\<Lambda> x . g x (h\<cdot>x))) = (\<Lambda> x. (\<mu> h. g x h))" 
proof - 
  let ?g = "(\<Lambda> x y. g x y)"
  have "\<And> x y. ?g\<cdot>x\<cdot>y = g x y"
    apply(subst beta_cfun; simp add: assms)
    apply(rule abs_cfun_cont2cont)
    by (auto simp add: assms)
  moreover have "(\<mu> h. (\<Lambda> x . ?g\<cdot>x\<cdot>(h\<cdot>x))) = (\<Lambda> x. (\<mu> h. ?g\<cdot>x\<cdot>h))"
    apply(rule fix_const)
    by simp
  ultimately show ?thesis 
    by auto
qed

lemma fix_eqI_below:
  assumes fixed: "F\<cdot>x \<sqsubseteq> x"
    and least: "\<And>z. F\<cdot>z \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  shows "fix\<cdot>F = x"
  using fix_eq fix_least_below fixed local.least po_eq_conv by blast

thm lfp_rolling
lemma fix_rolling: "g\<cdot>(fix\<cdot>(f oo g)) = fix\<cdot>(g oo f)"
proof (rule below_antisym)
  have "fix\<cdot>(f oo g) \<sqsubseteq> f\<cdot>(fix\<cdot>(g oo f))"
    by (metis cfcomp2 fix_eq fix_least)
  thus "g\<cdot>(fix\<cdot>(f oo g)) \<sqsubseteq> fix\<cdot>(g oo f)"
    by (metis (no_types, lifting) cfcomp2 cont_pref_eq1I fix_eq)
  show "fix\<cdot>(g oo f) \<sqsubseteq> g\<cdot>(fix\<cdot>(f oo g))"
    apply(rule fix_least_below, simp)
    by (metis cfcomp2 fix_eq po_eq_conv)
qed

thm lfp_lfp
lemma fix_fix:"fix\<cdot>(\<Lambda> x. fix\<cdot>(f\<cdot>x)) = fix\<cdot>(\<Lambda> x. f\<cdot>x\<cdot>x)"
proof (rule below_antisym)
  show "fix\<cdot>(\<Lambda> x. fix\<cdot>(f\<cdot>x)) \<sqsubseteq> fix\<cdot>(\<Lambda> x. f\<cdot>x\<cdot>x)"
    apply(rule fix_least_below, simp)
    apply(rule fix_least_below)
    by(subst (3) fix_eq, simp)
  show "fix\<cdot>(\<Lambda> x. f\<cdot>x\<cdot>x) \<sqsubseteq> fix\<cdot>(\<Lambda> x. fix\<cdot>(f\<cdot>x))"
    apply(rule fix_least_below, simp)
    by (metis (no_types) below_refl cfcomp1 fix_eq fix_rolling)
qed

lemma fix_21: "fix\<cdot>(F oo F) = fix\<cdot>F"
  by (metis (no_types, lifting) cfcomp2 fix_eqI fix_least fix_rolling)

lemma fix_convert:
  fixes f::"'a::pcpo \<rightarrow> 'a"
   and a2b::"'a \<rightarrow> 'b::pcpo"
 assumes "b2a oo a2b = ID"
 shows "a2b\<cdot>(fix\<cdot>f) = fix\<cdot>(a2b oo f oo b2a) " 
proof -
  have "fix\<cdot>(f) = fix\<cdot>((b2a oo a2b) oo f)"
    by (simp add: assms)
  thus ?thesis 
    using assoc_oo fix_rolling
    by (metis fix_eq)
qed

lemma fix_reduce:
  fixes f::"'b::pcpo \<rightarrow> 'a::pcpo \<rightarrow> 'a"
   and  g::"'a \<rightarrow> 'b \<rightarrow>'b"
   and a2b::"'a \<rightarrow> 'b"
 assumes "\<And>a b. a2b\<cdot>(f\<cdot>b\<cdot>a) = b"
 shows "fix\<cdot>(\<Lambda> a. f\<cdot>(fix\<cdot>(g\<cdot>a))\<cdot>a) = 
            fix\<cdot>(\<Lambda> a . (f\<cdot>(g\<cdot>a\<cdot>(a2b\<cdot>a))\<cdot>a)) " (is "?L = ?R")
proof (rule below_antisym)
  show "?L \<sqsubseteq> ?R"
    apply(rule fix_least_below, simp)
    apply(subst (4) fix_eq, simp)
    apply(rule monofun_cfun_fun, rule monofun_cfun_arg)
    apply(subst fix_eq)
    apply(rule monofun_cfun_arg)
    apply(rule fix_least_below)
    apply(subst(3) fix_eq, simp)
    by(simp add: assms)

  show "?R \<sqsubseteq> ?L"
    apply(rule fix_least_below, simp)
    apply(subst (7) fix_eq, simp)
    apply(rule monofun_cfun_fun, rule monofun_cfun_arg)
    apply(subst (5) fix_eq)
    apply(rule monofun_cfun_arg)
    apply(subst(1) fix_eq, simp)
    by(simp add: assms)
qed

lemma cfun_arg_cong2: "x = y \<Longrightarrow> z=w\<Longrightarrow> 
  f\<cdot>x\<cdot>z = f\<cdot>y\<cdot>w"
  by simp

lemma oo_arg_cong: "x\<cdot>sb=y\<cdot>sb \<Longrightarrow> (f oo x)\<cdot>sb = (f oo y)\<cdot>sb"
  by simp

lemma oo_assoc: "(a oo b) oo c = a oo (b oo c)"
  using Cfun.cfun.Rep_cfun_inject by fastforce

theorem gfp_3roll: 
  assumes Rep_mono: "mono Rep" and f_mono: "mono f" and Abs_mono: "mono Abs"
    and rep_abs: "Rep o Abs o Rep = Rep" 
    and rep_inv_mono: "\<And>x y. Rep x \<le> Rep y \<Longrightarrow> x \<le> y"
  shows "gfp (Rep o f o Abs) =  Rep (gfp f)"
proof (rule order_antisym)
  have *:"mono (Rep o f o Abs)"
    apply(auto simp add: o_def mono_def)[1]
    by (simp add: assms(1) assms(2) assms(3) monoD)

  show "Rep (gfp f) \<le> gfp (Rep \<circ> f \<circ> Abs)"
    apply (rule gfp_upperbound) 
    apply(simp add: gfp_unfold[OF *, symmetric])
    apply(subst gfp_unfold[OF f_mono])
    apply(intro monoD[OF Rep_mono] gfp_upperbound monoD[OF f_mono])
    by (metis comp_apply order_refl rep_abs rep_inv_mono)

  have rep_abs2: "\<And>x. Rep (Abs ( Rep x)) = Rep x" 
    by (metis comp_apply rep_abs) 
  show "gfp (Rep o f o Abs) \<le>  Rep (gfp f)"
  proof (rule gfp_least)
    fix u
    assume u: "u \<le> (Rep \<circ> f \<circ> (Abs)) u"
    have "Abs u \<le> ((Abs) \<circ> Rep \<circ> f \<circ> (Abs)) u"
      using assms(3) mono_def u by auto
    hence "(Rep o Abs) u \<le> (Rep o (Abs) \<circ> Rep \<circ> f \<circ> (Abs)) u"
      using Rep_mono mono_def by fastforce
    hence "(Rep \<circ> f \<circ> (Abs)) u \<le> (Rep (gfp f))"
      apply (simp add: o_def)
      apply(intro monoD[OF Rep_mono] gfp_upperbound monoD[OF f_mono])
      apply(subst (asm) rep_abs2)
      by (simp add: rep_inv_mono)
    thus "u \<le> Rep (gfp f)"
      using u by auto
  qed
qed



lemma monofun_inv:
      assumes"surj f"
      and"monofun f"
      and "\<And>x y. \<not>(x \<sqsubseteq> y) \<Longrightarrow> \<not>(f x \<sqsubseteq> f y)"
      shows"monofun (inv f)"
using assms
proof(subst monofunI;simp_all)
  fix x y::'a
  assume below:"x \<sqsubseteq> y" 
  assume bij: "surj f"
  assume mono: "monofun f"
  from bij obtain a b where x: "x = f a" and y: "y = f b" 
    by(fastforce simp: bij_def surj_def)
  show "inv f x \<sqsubseteq> inv f y"
  proof (cases "a \<sqsubseteq> b")
    case True
    then show ?thesis
      apply(simp add: x y)
      using assms(3) below bij surj_f_inv_f x y by fastforce
  next
    case False
    then show ?thesis
      apply(cases "b \<sqsubseteq> a",auto)
      using below below_antisym mono monofunE x y apply fastforce
      apply(simp add: x y)
      using assms(3) below x y by blast
  qed
qed

lemma cont_inv[cont2cont]:
      assumes"surj f"
      and"cont f"
      and "\<And>x y. \<not>(x \<sqsubseteq> y) \<Longrightarrow> \<not>(f x \<sqsubseteq> f y)"
      shows"cont (inv f)"
  apply(rule Cpo.contI2)
  apply(rule monofun_inv,simp_all add: assms cont2mono; fail)
  using assms(1) assms(2) assms(3) cont2contlubE surj_f_inv_f 
  by fastforce

declare Cfun.cfun.Rep_cfun_inverse[simp]

lemma inv_on_def [simp]: "((inv Def) (Def msg)) = msg"
  by (meson f_inv_into_f lift.inject rangeI)


(*datatype 'm tsyn = Msg 'm ( "\<M> _" 65)| eps
text \<open> Introduce symbol @{text ~} for empty time-slots called eps. \<close>
syntax "@eps" :: "'a tsyn" ("~")
translations "~" == "CONST eps"

text \<open> Inverse of Msg.\<close>
fun inverseMsg :: "'a tsyn \<Rightarrow> 'a" where
  "inverseMsg eps = undefined" |
  "inverseMsg (Msg m) = m"

abbreviation invMsg :: "'a tsyn \<Rightarrow> 'a"  ("\<M>\<inverse> _") where 
  "invMsg \<equiv> inverseMsg"

text \<open> Prove that datatype tsyn is countable. Needed, since the domain-constructor defined
        to work for countable types.\<close>
instance tsyn :: (countable) countable
  by countable_datatype



fun tsynfun :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
"tsynfun f eps = eps" |
"tsynfun f (Msg x) = Msg (f x)"

thm option.simps(9)

lemma mapMsgToMsg: "tsynfun f (Msg x) = Msg (f x)"
  by auto *)


datatype timeType = TUntimed| TTOne | TTFin | TTLive | TTsyn




definition rnd ::"(natural \<times> natural) \<Rightarrow> 'a::random" where
"rnd seed = (fst (fst (Quickcheck_Random.random 1000 seed)))"


definition testPred::"(natural\<times> natural) \<Rightarrow> 
             ('a::random \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 
             ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b \<times> bool)" where
"testPred seed P spf = 
    (let random = rnd seed 
     in (random,spf random, P random (spf random)))"

lemma ranselect_zero : "nat_of_natural (fst (Random.range (1::natural) (snd p))) = (0::nat)"
  by (metis less_natural.rep_eq less_numeral_extra(1) less_one one_natural.rep_eq range)

lemma fun_eqI: "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  by auto

lemma the_elem_some_eq : 
  assumes "is_singleton(A)"
  shows "(SOME x. (x\<in>A)) = (the_elem A)"
  apply(simp add: the_elem_def)
  by (metis assms insert_not_empty is_singletonE singleton_iff some_in_eq the_elem_def the_elem_eq)


lemma forall2all:"((\<forall>n. P n) \<Longrightarrow> Q) \<equiv> ((\<And>n. P n) \<Longrightarrow> Q)"
  by presburger

lemma impL_split: "(\<And>x. P x \<or> Q x \<Longrightarrow> R x) \<equiv> (\<And>x. (P x \<longrightarrow> R x) \<and> (Q x \<longrightarrow> R x))"
  by presburger


lift_definition Fst :: "('a::cpo \<times> 'b::cpo) \<rightarrow> 'a" is "\<lambda>x. fst x"
  by (simp add: cfun_def) 

lift_definition Snd :: "('a::cpo \<times> 'b::cpo) \<rightarrow> 'b" is "\<lambda>p. snd p"
  by (simp add: cfun_def) 

lemma Fst_fst: "Fst\<cdot>(a, b) = fst (a, b)"
by (simp add: Fst_def)

lemma Fst_apply: "Fst\<cdot>(a, b) = a"
  by (simp add: Fst_def)

lemma Snd_fst: "Snd\<cdot>(a, b) = snd (a, b)"
by (simp add: Snd_def)

lemma Snd_apply: "Snd\<cdot>(a, b) = b"
  by (simp add: Snd_def)

lemma apsnd_subseth[simp]:
  assumes "\<And>x y. (x,y) \<in> S1 \<Longrightarrow> (f x,y) \<in> S2"
  and "(x,y) \<in> apsnd f2 ` S1"
  shows"(f x,y) \<in> apsnd f2 `S2"
  using assms image_iff by fastforce

lemma apfst_snd_image_commu:"apfst f ` apsnd g` A = apsnd g ` apfst f ` A"
  apply(simp add: image_comp)
  done

lemma fst_image_left_inverse [simp]:"fst ` (\<lambda>s. (s, y s)) ` Y = Y"
  by (simp add: image_image[of fst "\<lambda>uua. (uua, y uua)" Y])



definition nondet_comp  :: "(('Intern::cpo \<rightarrow> 'Out::cpo) set) \<Rightarrow> (('In::cpo \<rightarrow> 'Intern) set)
    \<Rightarrow> (('In \<rightarrow> 'Out) set)" where
"nondet_comp = (\<lambda> sps1 sps2 . {spf1 oo spf2 | spf1 spf2. 
                                spf1 \<in> sps1 \<and> spf2 \<in> sps2})"

abbreviation nondet_comp_abbr :: 
"(('Intern::cpo \<rightarrow> 'Out::cpo) set) \<Rightarrow> (('In::cpo \<rightarrow> 'Intern) set)
    \<Rightarrow> (('In \<rightarrow> 'Out) set)"  (infixr "ooo" 100)
where "f ooo g == nondet_comp f g"

lemma case_unit[simp]:"(case x of () \<Rightarrow> f) = f"
  by (simp add: case_unit_Unity)

lemma case_unit2[simp]:"(case () of x \<Rightarrow> f) = f"
  by blast


lemma chain_iterate2: "chain (\<lambda>i. iterate (n+i)\<cdot>F\<cdot>\<bottom>)"
  by (metis (no_types, lifting) iterate_Suc2 iterate_iterate minimal monofun_cfun_arg po_class.chainI)

lemma fix_def3: "fix\<cdot>F = (\<Squnion>i. iterate (n+i)\<cdot>F\<cdot>\<bottom>)"
  apply(subst add.commute)
  apply(subst iterate_iterate[symmetric])
  apply(rule below_antisym)
  apply(simp add: fix_def)
  apply(rule lub_mono)
  apply(rule chain_iterate)
  apply(subst iterate_iterate, subst add.commute, rule chain_iterate2)
  using monofun_cfun_arg apply blast
  apply(subst iterate_iterate, subst add.commute)
  apply(subst lub_below_iff)
  apply(rule chain_iterate2)
  using iterate_below_fix by blast

lemma fix_ind2: 
  assumes adm: "adm P"
  assumes base: "P (iterate n\<cdot>F\<cdot>\<bottom>)"
  assumes step: "\<And>i::nat. n \<le> i \<Longrightarrow> P (iterate i\<cdot>F\<cdot>\<bottom>) \<Longrightarrow> P (F\<cdot>(iterate i\<cdot>F\<cdot>\<bottom>))"
  shows "P (fix\<cdot>F)"
proof -
  have "n \<le> i \<Longrightarrow> P (iterate i\<cdot>F\<cdot>\<bottom>)" for i
    by (induction i rule: dec_induct) (simp add: base, simp add: step)
  then have "P (\<Squnion>i. (iterate (n+i)\<cdot>F\<cdot>\<bottom>))"
    by (simp add: adm admD chain_iterate2)
  then show "P (fix\<cdot>F)"
    by (simp add: fix_def3[symmetric])
qed

lemma parallel_fix_ind2:
  assumes adm: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes base: "P (iterate n\<cdot>F\<cdot>\<bottom>) (iterate n\<cdot>G\<cdot>\<bottom>)"
  assumes step: "\<And>i::nat. n \<le> i \<Longrightarrow> P (iterate i\<cdot>F\<cdot>\<bottom>) (iterate i\<cdot>G\<cdot>\<bottom>) \<Longrightarrow> P (F\<cdot>(iterate i\<cdot>F\<cdot>\<bottom>)) (G\<cdot>(iterate i\<cdot>G\<cdot>\<bottom>))"
  shows "P (fix\<cdot>F) (fix\<cdot>G)"
proof -
  from adm have adm': "adm (case_prod P)"
    unfolding split_def .
  have "n \<le> i \<Longrightarrow> P (iterate i\<cdot>F\<cdot>\<bottom>) (iterate i\<cdot>G\<cdot>\<bottom>)" for i
    by(induction i rule: dec_induct) (simp add: base, simp add: step)
  then have "\<And>i. case_prod P (iterate (n + i)\<cdot>F\<cdot>\<bottom>, iterate (n + i)\<cdot>G\<cdot>\<bottom>)"
    using le_add1 by blast
  then have "case_prod P (\<Squnion>i. (iterate (n + i)\<cdot>F\<cdot>\<bottom>, iterate (n + i)\<cdot>G\<cdot>\<bottom>))"
    by (simp add: adm admD chain_iterate2)
  then have "case_prod P (\<Squnion>i. iterate (n + i)\<cdot>F\<cdot>\<bottom>, \<Squnion>i. iterate (n + i)\<cdot>G\<cdot>\<bottom>)"
    by (simp add: lub_Pair chain_iterate2)
  then have "P (\<Squnion>i. iterate (n + i)\<cdot>F\<cdot>\<bottom>) (\<Squnion>i. iterate (n + i)\<cdot>G\<cdot>\<bottom>)"
    by simp
  then show "P (fix\<cdot>F) (fix\<cdot>G)"
    by (simp add: fix_def3[symmetric])
qed

lemma lub_below_lub:
assumes "\<And>i. \<exists>n. iterate i\<cdot>F\<cdot>\<bottom> \<sqsubseteq> iterate n\<cdot>G\<cdot>\<bottom>"
  shows "fix\<cdot>F \<sqsubseteq> fix\<cdot>G"
  apply(simp add: fix_def)
  apply(rule lub_below[OF chain_iterate])
  using assms(1) below_lub[OF chain_iterate] by blast

lemma lub_eq_lub:
assumes "\<And>i. \<exists>n. iterate i\<cdot>F\<cdot>\<bottom> \<sqsubseteq> iterate n\<cdot>G\<cdot>\<bottom>"
    and "\<And>i. \<exists>n. iterate i\<cdot>G\<cdot>\<bottom> \<sqsubseteq> iterate n\<cdot>F\<cdot>\<bottom>"
  shows "fix\<cdot>F = fix\<cdot>G"
  apply(rule below_antisym)
  apply(rule lub_below_lub[OF assms(1)])
  by(rule lub_below_lub[OF assms(2)])


end
