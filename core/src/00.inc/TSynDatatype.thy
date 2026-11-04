theory TSynDatatype
imports Classes

begin
default_sort type

(*

(* ----------------------------------------------------------------------- *)
  section \<open>Tsyn to Option\<close>
(* ----------------------------------------------------------------------- *)

type_synonym 'e tsyn = "'e option"

abbreviation "Msg \<equiv> Some"

abbreviation Eps :: "'a::type option" ("~") where "Eps \<equiv> None"

fun inverseMsg :: "'a::type option \<Rightarrow> 'a" where
"inverseMsg (Some a) = a"

*)

(*definition of tsyn datatype and lemmas analog to option datatype*)

datatype 'm tsyn = TSynMsg 'm | Eps ("\<sim>")


declare[[coercion_map map_tsyn]]

fun inverseMsg :: "'a tsyn \<Rightarrow> 'a" where
  "inverseMsg Eps = undefined" |
  "inverseMsg (TSynMsg m) = m"

abbreviation invMsg :: "'a tsyn \<Rightarrow> 'a"  ("\<M>\<inverse> _") where 
  "invMsg \<equiv> inverseMsg"

instance tsyn :: (countable) countable
  by countable_datatype

datatype_compat tsyn

lemma [case_names Eps Msg, cases type: tsyn]:
  "(y = Eps \<Longrightarrow> P) \<Longrightarrow> (\<And>a. y = TSynMsg a \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule tsyn.exhaust)

lemma [case_names Eps Msg, induct type: tsyn]:
  "P Eps \<Longrightarrow> (\<And>tsyn. P (TSynMsg tsyn)) \<Longrightarrow> P tsyn"
  by (rule tsyn.induct)


lemma not_Eps_eq [iff]: "x \<noteq> \<sim> \<longleftrightarrow> (\<exists>y. x = TSynMsg y)"
  by (induct x) auto

lemma not_Msg_eq [iff]: "(\<forall>y. x \<noteq> TSynMsg y) \<longleftrightarrow> x = Eps"
  by (induct x) auto

        
lemma comp_invMsg_Msg[simp]: "invMsg o TSynMsg = id"
by auto 


lemma inj_Msg [simp]: "inj_on TSynMsg A"
  by (rule inj_onI) simp

lemma case_tsynE:
  assumes c: "(case x of Eps \<Rightarrow> P | TSynMsg y \<Rightarrow> Q y)"
  obtains
    (Eps) "x = Eps" and P
  | (TSynMsg) y where "x = TSynMsg y" and "Q y"
  using c by (cases x) simp_all

lemma split_tsyn_all: "(\<forall>x. P x) \<longleftrightarrow> P Eps \<and> (\<forall>x. P (TSynMsg x))"
  by (auto intro: tsyn.induct)

lemma split_tsyn_ex: "(\<exists>x. P x) \<longleftrightarrow> P Eps \<or> (\<exists>x. P (TSynMsg x))"
  using split_tsyn_all[of "\<lambda>x. \<not> P x"] by blast

lemma UNIV_tsyn_conv: "UNIV = insert Eps (range TSynMsg)"
  by (auto intro: classical)

lemma rel_tsyn_Eps1 [simp]: "rel_tsyn P Eps x \<longleftrightarrow> x = Eps"
  by (cases x) simp_all

lemma rel_tsyn_Eps2 [simp]: "rel_tsyn P x Eps \<longleftrightarrow> x = Eps"
  by (cases x) simp_all

lemma tsyn_rel_Msg1: "rel_tsyn A (TSynMsg x) y \<longleftrightarrow> (\<exists>y'. y = TSynMsg y' \<and> A x y')"
by(cases y) simp_all

lemma tsyn_rel_Msg2: "rel_tsyn A x (TSynMsg y) \<longleftrightarrow> (\<exists>x'. x = TSynMsg x' \<and> A x' y)"
by(cases x) simp_all

lemma rel_tsyn_inf: "inf (rel_tsyn A) (rel_tsyn B) = rel_tsyn (inf A B)"
  (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<le> ?rhs" by (auto elim: tsyn.rel_cases)
  show "?rhs \<le> ?lhs" by (auto elim: tsyn.rel_mono_strong)
qed

lemma rel_tsyn_reflI:
  "(\<And>x. x \<in> set_tsyn y \<Longrightarrow> P x x) \<Longrightarrow> rel_tsyn P y y"
  by (cases y) auto

lemma TSynMsg_image_eq: "TSynMsg ` A = {x . (\<exists>y. x = TSynMsg y) \<and> inv TSynMsg x \<in> A}"
  by auto


lemma otsyn [dest]: "(\<forall>x\<in>set_tsyn A. P x) \<Longrightarrow> A = TSynMsg x \<Longrightarrow> P x"
  by simp

setup \<open>map_theory_claset (fn ctxt => ctxt addSD2 ("otsyn", @{thm otsyn}))\<close>

lemma elem_set [iff]: "(x \<in> set_tsyn xo) = (xo = TSynMsg x)"
  by (cases xo) auto

lemma set_empty_eq [simp]: "(set_tsyn xo = {}) = (xo = Eps)"
  by (cases xo) auto

lemma map_tsyn_case: "map_tsyn f y = (case y of Eps \<Rightarrow> Eps | TSynMsg x \<Rightarrow> TSynMsg (f x))"
  by (auto split: tsyn.split)

lemma map_tsyn_is_Eps [iff]: "(map_tsyn f opt = Eps) = (opt = Eps)"
  by (simp add: map_tsyn_case split: tsyn.split)

lemma Eps_eq_map_tsyn_iff [iff]: "Eps = map_tsyn f x \<longleftrightarrow> x = Eps"
by(cases x) simp_all

lemma map_tsyn_eq_Msg [iff]: "(map_tsyn f xo = TSynMsg y) = (\<exists>z. xo = TSynMsg z \<and> f z = y)"
  by (simp add: map_tsyn_case split: tsyn.split)

lemma map_tsyn_o_case_sum [simp]:
    "map_tsyn f \<circ> case_sum g h = case_sum (map_tsyn f \<circ> g) (map_tsyn f \<circ> h)"
  by (rule o_case_sum)

lemma map_tsyn_cong: "x = y \<Longrightarrow> (\<And>a. y = TSynMsg a \<Longrightarrow> f a = g a) \<Longrightarrow> map_tsyn f x = map_tsyn g y"
  by (cases x) auto

lemma map_tsyn_idI: "(\<And>y. y \<in> set_tsyn x \<Longrightarrow> f y = y) \<Longrightarrow> map_tsyn f x = x"
by(cases x)(simp_all)

functor map_tsyn: map_tsyn
  by (simp_all add: tsyn.map_comp fun_eq_iff tsyn.map_id)

(*lemma case_map_tsyn [simp]: "case_tsyn g h (map_tsyn f x) = case_tsyn g (h \<circ> f) x"
  by (cases x) simp_all*)

lemma Eps_notin_image_Msg [simp]: "Eps \<notin> TSynMsg ` A"
by auto

lemma notin_range_Msg: "x \<notin> range TSynMsg \<longleftrightarrow> x = Eps"
by(cases x) auto

lemma rel_tsyn_iff:
  "rel_tsyn R x y = (case (x, y) of (Eps, Eps) \<Rightarrow> True
    | (TSynMsg x, TSynMsg y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
  by (auto split: prod.split tsyn.split)


definition combine_tsyns :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn"
  where "combine_tsyns f x y = 
           (case x of Eps \<Rightarrow> y | TSynMsg x \<Rightarrow> (case y of Eps \<Rightarrow> TSynMsg x | TSynMsg y \<Rightarrow> TSynMsg (f x y)))"

lemma combine_tsyns_simps [simp]:
  "combine_tsyns f Eps y = y"
  "combine_tsyns f x Eps = x"
  "combine_tsyns f (TSynMsg a) (TSynMsg b) = TSynMsg (f a b)"
  by (simp_all add: combine_tsyns_def split: tsyn.splits)
  
lemma combine_tsyns_cases [case_names Eps1 Eps2 Msg]:
  "(x = Eps \<Longrightarrow> P x y) \<Longrightarrow> (y = Eps \<Longrightarrow> P x y) \<Longrightarrow> 
     (\<And>a b. x = TSynMsg a \<Longrightarrow> y = TSynMsg b \<Longrightarrow> P x y) \<Longrightarrow> P x y"
  by (cases x; cases y) simp_all

lemma combine_tsyns_commute: 
  "(\<And>x y. f x y = f y x) \<Longrightarrow> combine_tsyns f x y = combine_tsyns f y x"
  using combine_tsyns_cases[of x ]
  by (induction x y rule: combine_tsyns_cases) simp_all

lemma combine_tsyns_assoc:
  "(\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_tsyns f (combine_tsyns f x y) z =
     combine_tsyns f x (combine_tsyns f y z)"
  by (auto simp: combine_tsyns_def split: tsyn.splits)

lemma combine_tsyns_left_commute:
  "(\<And>x y. f x y = f y x) \<Longrightarrow> (\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_tsyns f y (combine_tsyns f x z) =
     combine_tsyns f x (combine_tsyns f y z)"
  by (auto simp: combine_tsyns_def split: tsyn.splits)

lemmas combine_tsyns_ac = 
  combine_tsyns_commute combine_tsyns_assoc combine_tsyns_left_commute


context
begin

qualified definition is_Eps :: "'a tsyn \<Rightarrow> bool"
  where  "is_Eps x \<longleftrightarrow> x = Eps"

lemma is_Eps_simps [simp]:
  "is_Eps Eps"
  "\<not> is_Eps (TSynMsg x)"
  by (simp_all add: is_Eps_def)

lemma is_Eps_code :
  "is_Eps Eps = True"
  "is_Eps (TSynMsg x) = False"
  by simp_all

lemma rel_tsyn_unfold:
  "rel_tsyn R x y \<longleftrightarrow>
   (is_Eps x \<longleftrightarrow> is_Eps y) \<and> (\<not> is_Eps x \<longrightarrow> \<not> is_Eps y \<longrightarrow> R (invMsg x) (invMsg y))"
  by (simp add: rel_tsyn_iff split: tsyn.split)

lemma rel_tsynI:
  "\<lbrakk> is_Eps x \<longleftrightarrow> is_Eps y; \<lbrakk> \<not> is_Eps x; \<not> is_Eps y \<rbrakk> \<Longrightarrow> P (invMsg x) (invMsg y) \<rbrakk>
  \<Longrightarrow> rel_tsyn P x y"
  by (simp add: rel_tsyn_unfold)

lemma is_Eps_map_tsyn [simp]: "is_Eps (map_tsyn f x) \<longleftrightarrow> is_Eps x"
  by (simp add: is_Eps_def)

lemma invMsg_map_tsyn: "\<not> is_Eps x \<Longrightarrow> invMsg (map_tsyn f x) = f (invMsg x)"
  by (auto simp add: is_Eps_def)


qualified primrec bind :: "'a tsyn \<Rightarrow> ('a \<Rightarrow> 'b tsyn) \<Rightarrow> 'b tsyn"
where
  bind_lzero: "bind Eps f = Eps"
| bind_lunit: "bind (TSynMsg x) f = f x"

lemma is_Eps_bind: "is_Eps (bind f g) \<longleftrightarrow> is_Eps f \<or> is_Eps (g (invMsg f))"
  by (cases f) simp_all

lemma bind_runit[simp]: "bind x TSynMsg = x"
  by (cases x) auto

lemma bind_assoc[simp]: "bind (bind x f) g = bind x (\<lambda>y. bind (f y) g)"
  by (cases x) auto

lemma bind_rzero[simp]: "bind x (\<lambda>x. Eps) = Eps"
  by (cases x) auto

qualified lemma bind_cong: "x = y \<Longrightarrow> (\<And>a. y = TSynMsg a \<Longrightarrow> f a = g a) \<Longrightarrow> bind x f = bind y g"
  by (cases x) auto

lemma bind_split: "P (bind m f) \<longleftrightarrow> (m = Eps \<longrightarrow> P Eps) \<and> (\<forall>v. m = TSynMsg v \<longrightarrow> P (f v))"
  by (cases m) auto

lemma bind_split_asm: "P (bind m f) \<longleftrightarrow> \<not> (m = Eps \<and> \<not> P Eps \<or> (\<exists>x. m = TSynMsg x \<and> \<not> P (f x)))"
  by (cases m) auto

lemmas bind_splits = bind_split bind_split_asm

lemma bind_eq_Msg_conv: "bind f g = TSynMsg x \<longleftrightarrow> (\<exists>y. f = TSynMsg y \<and> g y = TSynMsg x)"
  by (cases f) simp_all

lemma bind_eq_Eps_conv: "bind a f = Eps \<longleftrightarrow> a = Eps \<or> f (invMsg a) = Eps"
by(cases a) simp_all

lemma map_tsyn_bind: "map_tsyn f (bind x g) = bind x (map_tsyn f \<circ> g)"
  by (cases x) simp_all

lemma bind_tsyn_cong:
  "\<lbrakk> x = y; \<And>z. z \<in> set_tsyn y \<Longrightarrow> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  by (cases y) simp_all

lemma bind_tsyn_cong_simp:
  "\<lbrakk> x = y; \<And>z. z \<in> set_tsyn y =simp=> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  unfolding simp_implies_def by (rule bind_tsyn_cong)

lemma bind_tsyn_cong_code: "x = y \<Longrightarrow> bind x f = bind y f"
  by simp

lemma bind_map_tsyn: "bind (map_tsyn f x) g = bind x (g \<circ> f)"
by(cases x) simp_all

lemma set_bind_tsyn [simp]: "set_tsyn (bind x f) = (\<Union>((set_tsyn \<circ> f) ` set_tsyn x))"
by(cases x) auto

lemma map_conv_bind_tsyn: "map_tsyn f x = bind x (TSynMsg \<circ> f)"
by(cases x) simp_all

end

setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm bind_tsyn_cong_code})\<close>


context
begin

qualified definition these :: "'a tsyn set \<Rightarrow> 'a set"
  where "these A = invMsg ` {x \<in> A. x \<noteq> Eps}"

lemma these_empty [simp]: "these {} = {}"
  by (simp add: these_def)

lemma these_insert_Eps [simp]: "these (insert Eps A) = these A"
  by (auto simp add: these_def)

lemma these_insert_Msg [simp]: "these (insert (TSynMsg x) A) = insert x (these A)"
proof -
  have "{y \<in> insert (TSynMsg x) A. y \<noteq> Eps} = insert (TSynMsg x) {y \<in> A. y \<noteq> Eps}"
    by auto
  then show ?thesis by (simp add: these_def)
qed

lemma in_these_eq: "x \<in> these A \<longleftrightarrow> TSynMsg x \<in> A"
proof
  assume "TSynMsg x \<in> A"
  then obtain B where "A = insert (TSynMsg x) B" by auto
  then show "x \<in> these A"
    by simp
next
  assume "x \<in> these A"
  then show "TSynMsg x \<in> A" by (auto simp add: these_def)
qed

lemma these_image_Msg_eq [simp]: "these (TSynMsg ` A) = A"
  by(auto simp add: these_def,intro image_eqI,auto)
  
lemma Msg_image_these_eq: "TSynMsg ` these A = {x\<in>A. x \<noteq> Eps}"
  by (auto simp add: these_def,intro image_eqI,auto)

lemma these_empty_eq: "these B = {} \<longleftrightarrow> B = {} \<or> B = {Eps}"
  by (auto simp add: these_def)

lemma these_not_empty_eq: "these B \<noteq> {} \<longleftrightarrow> B \<noteq> {} \<and> B \<noteq> {Eps}"
  by (auto simp add: these_empty_eq)

end

lemma finite_range_Msg: "finite (range (TSynMsg :: 'a \<Rightarrow> 'a tsyn)) = finite (UNIV :: 'a set)"
  by (auto dest: finite_imageD intro: inj_Msg)



context includes lifting_syntax
begin

lemma tsyn_bind_transfer [transfer_rule]:
  "(rel_tsyn A ===> (A ===> rel_tsyn B) ===> rel_tsyn B)
    TSynDatatype.bind TSynDatatype.bind"
  unfolding rel_fun_def split_tsyn_all by simp

lemma pred_tsyn_parametric [transfer_rule]:
  "((A ===> (=)) ===> rel_tsyn A ===> (=)) pred_tsyn pred_tsyn"
  by (rule rel_funI)+ (auto simp add: rel_tsyn_unfold TSynDatatype.is_Eps_def dest: rel_funD)

end



lemma finite_tsyn_UNIV [simp]:
  "finite (UNIV :: 'a tsyn set) = finite (UNIV :: 'a set)"
  by (auto simp add: UNIV_tsyn_conv elim: finite_imageD intro: inj_Msg)

instance tsyn :: (finite) finite
  by standard (simp add: UNIV_tsyn_conv)



lemma equal_Eps_code_unfold :
  "HOL.equal x Eps \<longleftrightarrow> TSynDatatype.is_Eps x"
  "HOL.equal Eps = TSynDatatype.is_Eps"
  by (auto simp add: equal TSynDatatype.is_Eps_def)





instantiation tsyn:: (type) discrete_cpo
begin
definition "((\<sqsubseteq>) :: 'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_tsyn_def)
end

instantiation tsyn:: (type) tlen
begin
  fun tlen_tsyn:: "'a tsyn \<Rightarrow> lnat" where
  "tlen_tsyn _ = 1" 

instance 
  apply(intro_classes)
   apply (simp add: cont2mono)
  apply(rule exI, simp add: lnzero_def one_def)
  done
end

instance tsyn:: (type) tlen_one
  apply(intro_classes)
  by (simp)
  
end