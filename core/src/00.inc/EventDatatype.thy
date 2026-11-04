theory EventDatatype
imports Classes

begin


default_sort type

datatype 'm event = EventMsg 'm | Tick ("\<surd>")

declare[[coercion_map map_event]]

instance event :: (countable) countable
  apply(countable_datatype)
  done



lemma inveventid[simp]:"inv EventMsg o EventMsg = id"
  apply(rule inv_o_cancel)
  by (meson event.inject injI)

lemma event_inv[simp]:"inv EventMsg (EventMsg e) = e"
  using inveventid
  by (simp add: pointfree_idE)

lemma mapevent_surjI:"surj f \<Longrightarrow> surj (map_event f)"
  apply(rule surjI [where f="map_event (inv f)"])
  apply(case_tac x; simp)
  by (simp add: surj_f_inv_f)


instantiation event::(type) discrete_cpo 
begin

definition "((\<sqsubseteq>) :: 'a event \<Rightarrow> 'a event \<Rightarrow> bool) = (=)"

instance
  by standard (simp add: below_event_def)
end

instantiation event::(type) tlen
begin
  fun tlen_event::"'a::type event \<Rightarrow> lnat" where
  "tlen_event Tick = 1" |
  "tlen_event (EventMsg _)= 0" 

instance 
  apply(intro_classes)
   apply (simp add: cont2mono)
  by(rule exI[where x=Tick], simp add: lnzero_def one_def)
  
end

lemma tlen_event_le_one[simp]:"#\<^sub>\<surd> (msg::'m event) \<le> (1::lnat)"
  by(cases msg; simp)


fun inverseEventMsg :: "'a event \<Rightarrow> 'a" where
  "inverseEventMsg Tick = undefined" |
  "inverseEventMsg (EventMsg m) = m"

abbreviation invEventMsg :: "'a event \<Rightarrow> 'a" where 
  "invEventMsg \<equiv> inverseEventMsg"

datatype_compat event

lemma [case_names Tick EventMsg, cases type: event]:
  "(y = Tick \<Longrightarrow> P) \<Longrightarrow> (\<And>a. y = EventMsg a \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule event.exhaust)

lemma [case_names Tick EventMsg, induct type: event]:
  "P Tick \<Longrightarrow> (\<And>event. P (EventMsg event)) \<Longrightarrow> P event"
  by (rule event.induct)


lemma not_Tick_eq [iff]: "x \<noteq>Tick\<longleftrightarrow> (\<exists>y. x = EventMsg y)"
  by (induct x) auto

lemma not_Event_eq [iff]: "(\<forall>y. x \<noteq> EventMsg y) \<longleftrightarrow> x = Tick"
  by (induct x) auto

        
lemma comp_invEventMsg_EventMsg[simp]: "invEventMsg o EventMsg = id"
by auto 


lemma inj_EventMsg [simp]: "inj_on EventMsg A"
  by (rule inj_onI) simp

lemma case_eventE:
  assumes c: "(case x of Tick \<Rightarrow> P | EventMsg y \<Rightarrow> Q y)"
  obtains
    (Tick) "x = Tick" and P
  | (EventMsg) y where "x = EventMsg y" and "Q y"
  using c by (cases x) simp_all

lemma split_event_all: "(\<forall>x. P x) \<longleftrightarrow> P Tick \<and> (\<forall>x. P (EventMsg x))"
  by (auto intro: event.induct)

lemma split_event_ex: "(\<exists>x. P x) \<longleftrightarrow> P Tick \<or> (\<exists>x. P (EventMsg x))"
  using split_event_all[of "\<lambda>x. \<not> P x"] by blast

lemma UNIV_event_conv: "UNIV = insert Tick (range EventMsg)"
  by (auto intro: classical)

lemma rel_event_Tick1 [simp]: "rel_event P Tick x \<longleftrightarrow> x = Tick"
  by (cases x) simp_all

lemma rel_event_Tick2 [simp]: "rel_event P x Tick \<longleftrightarrow> x = Tick"
  by (cases x) simp_all

lemma event_rel_EventMsg1: "rel_event A (EventMsg x) y \<longleftrightarrow> (\<exists>y'. y = EventMsg y' \<and> A x y')"
by(cases y) simp_all

lemma event_rel_EventMsg2: "rel_event A x (EventMsg y) \<longleftrightarrow> (\<exists>x'. x = EventMsg x' \<and> A x' y)"
by(cases x) simp_all

lemma rel_event_inf: "inf (rel_event A) (rel_event B) = rel_event (inf A B)"
  (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<le> ?rhs" by (auto elim: event.rel_cases)
  show "?rhs \<le> ?lhs" by (auto elim: event.rel_mono_strong)
qed

lemma rel_event_reflI:
  "(\<And>x. x \<in> set_event y \<Longrightarrow> P x x) \<Longrightarrow> rel_event P y y"
  by (cases y) auto



lemma oevent [dest]: "(\<forall>x\<in>set_event A. P x) \<Longrightarrow> A = EventMsg x \<Longrightarrow> P x"
  by simp

setup \<open>map_theory_claset (fn ctxt => ctxt addSD2 ("oevent", @{thm oevent}))\<close>

lemma elem_set [iff]: "(x \<in> set_event xo) = (xo = EventMsg x)"
  by (cases xo) auto

lemma set_empty_eq [simp]: "(set_event xo = {}) = (xo = Tick)"
  by (cases xo) auto

lemma map_event_case: "map_event f y = (case y of Tick \<Rightarrow> Tick | EventMsg x \<Rightarrow> EventMsg (f x))"
  by (auto split: event.split)

lemma map_event_is_Tick [iff]: "(map_event f opt = Tick) = (opt = Tick)"
  by (simp add: map_event_case split: event.split)

lemma Tick_eq_map_event_iff [iff]: "Tick = map_event f x \<longleftrightarrow> x = Tick"
by(cases x) simp_all

lemma map_event_eq_EventMsg [iff]: "(map_event f xo = EventMsg y) = (\<exists>z. xo = EventMsg z \<and> f z = y)"
  by (simp add: map_event_case split: event.split)

lemma map_event_o_case_sum [simp]:
    "map_event f \<circ> case_sum g h = case_sum (map_event f \<circ> g) (map_event f \<circ> h)"
  by (rule o_case_sum)

lemma map_event_cong: "x = y \<Longrightarrow> (\<And>a. y = EventMsg a \<Longrightarrow> f a = g a) \<Longrightarrow> map_event f x = map_event g y"
  by (cases x) auto

lemma map_event_idI: "(\<And>y. y \<in> set_event x \<Longrightarrow> f y = y) \<Longrightarrow> map_event f x = x"
by(cases x)(simp_all)

functor map_event: map_event
  by (simp_all add: event.map_comp fun_eq_iff event.map_id)

(*lemma case_map_event [simp]: "case_event g h (map_event f x) = case_event g (h \<circ> f) x"
  by (cases x) simp_all*)

lemma Tick_notin_image_Event [simp]: "Tick \<notin> EventMsg ` A"
by auto

lemma notin_range_Event: "x \<notin> range EventMsg \<longleftrightarrow> x = Tick"
by(cases x) auto

lemma rel_event_iff:
  "rel_event R x y = (case (x, y) of (Tick, Tick) \<Rightarrow> True
    | (EventMsg x, EventMsg y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
  by (auto split: prod.split event.split)


definition combine_events :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a event \<Rightarrow> 'a event \<Rightarrow> 'a event"
  where "combine_events f x y = 
           (case x of Tick \<Rightarrow> y | EventMsg x \<Rightarrow> (case y of Tick \<Rightarrow> EventMsg x | EventMsg y \<Rightarrow> EventMsg (f x y)))"

lemma combine_events_simps [simp]:
  "combine_events f Tick y = y"
  "combine_events f x Tick = x"
  "combine_events f (EventMsg a) (EventMsg b) = EventMsg (f a b)"
  by (simp_all add: combine_events_def split: event.splits)
  
lemma combine_events_cases [case_names Tick1 Tick2 EventMsg]:
  "(x = Tick \<Longrightarrow> P x y) \<Longrightarrow> (y = Tick \<Longrightarrow> P x y) \<Longrightarrow> 
     (\<And>a b. x = EventMsg a \<Longrightarrow> y = EventMsg b \<Longrightarrow> P x y) \<Longrightarrow> P x y"
  by (cases x; cases y) simp_all

lemma combine_events_commute: 
  "(\<And>x y. f x y = f y x) \<Longrightarrow> combine_events f x y = combine_events f y x"
  using combine_events_cases[of x ]
  by (induction x y rule: combine_events_cases) simp_all

lemma combine_events_assoc:
  "(\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_events f (combine_events f x y) z =
     combine_events f x (combine_events f y z)"
  by (auto simp: combine_events_def split: event.splits)

lemma combine_events_left_commute:
  "(\<And>x y. f x y = f y x) \<Longrightarrow> (\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_events f y (combine_events f x z) =
     combine_events f x (combine_events f y z)"
  by (auto simp: combine_events_def split: event.splits)

lemmas combine_events_ac = 
  combine_events_commute combine_events_assoc combine_events_left_commute


context
begin

qualified definition is_Tick :: "'a event \<Rightarrow> bool"
  where  "is_Tick x \<longleftrightarrow> x = Tick"

lemma is_Tick_simps [simp]:
  "is_Tick Tick"
  "\<not> is_Tick (EventMsg x)"
  by (simp_all add: is_Tick_def)

lemma is_Tick_code :
  "is_Tick Tick = True"
  "is_Tick (EventMsg x) = False"
  by simp_all

lemma rel_event_unfold:
  "rel_event R x y \<longleftrightarrow>
   (is_Tick x \<longleftrightarrow> is_Tick y) \<and> (\<not> is_Tick x \<longrightarrow> \<not> is_Tick y \<longrightarrow> R (invEventMsg x) (invEventMsg y))"
  by (simp add: rel_event_iff split: event.split)

lemma rel_eventI:
  "\<lbrakk> is_Tick x \<longleftrightarrow> is_Tick y; \<lbrakk> \<not> is_Tick x; \<not> is_Tick y \<rbrakk> \<Longrightarrow> P (invEventMsg x) (invEventMsg y) \<rbrakk>
  \<Longrightarrow> rel_event P x y"
  by (simp add: rel_event_unfold)

lemma is_Tick_map_event [simp]: "is_Tick (map_event f x) \<longleftrightarrow> is_Tick x"
  by (simp add: is_Tick_def)

lemma invEventMsg_map_event: "\<not> is_Tick x \<Longrightarrow> invEventMsg (map_event f x) = f (invEventMsg x)"
  by (auto simp add: is_Tick_def)


qualified primrec bind :: "'a event \<Rightarrow> ('a \<Rightarrow> 'b event) \<Rightarrow> 'b event"
where
  bind_lzero: "bind Tick f = Tick"
| bind_lunit: "bind (EventMsg x) f = f x"

lemma is_Tick_bind: "is_Tick (bind f g) \<longleftrightarrow> is_Tick f \<or> is_Tick (g (invEventMsg f))"
  by (cases f) simp_all

lemma bind_runit[simp]: "bind x EventMsg = x"
  by (cases x) auto

lemma bind_assoc[simp]: "bind (bind x f) g = bind x (\<lambda>y. bind (f y) g)"
  by (cases x) auto

lemma bind_rzero[simp]: "bind x (\<lambda>x. Tick) = Tick"
  by (cases x) auto

qualified lemma bind_cong: "x = y \<Longrightarrow> (\<And>a. y = EventMsg a \<Longrightarrow> f a = g a) \<Longrightarrow> bind x f = bind y g"
  by (cases x) auto

lemma bind_split: "P (bind m f) \<longleftrightarrow> (m = Tick \<longrightarrow> P Tick) \<and> (\<forall>v. m = EventMsg v \<longrightarrow> P (f v))"
  by (cases m) auto

lemma bind_split_asm: "P (bind m f) \<longleftrightarrow> \<not> (m = Tick \<and> \<not> P Tick \<or> (\<exists>x. m = EventMsg x \<and> \<not> P (f x)))"
  by (cases m) auto

lemmas bind_splits = bind_split bind_split_asm

lemma bind_eq_EventMsg_conv: "bind f g = EventMsg x \<longleftrightarrow> (\<exists>y. f = EventMsg y \<and> g y = EventMsg x)"
  by (cases f) simp_all

lemma bind_eq_Tick_conv: "bind a f = Tick \<longleftrightarrow> a = Tick \<or> f (invEventMsg a) = Tick"
by(cases a) simp_all

lemma map_event_bind: "map_event f (bind x g) = bind x (map_event f \<circ> g)"
  by (cases x) simp_all

lemma bind_event_cong:
  "\<lbrakk> x = y; \<And>z. z \<in> set_event y \<Longrightarrow> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  by (cases y) simp_all

lemma bind_event_cong_simp:
  "\<lbrakk> x = y; \<And>z. z \<in> set_event y =simp=> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  unfolding simp_implies_def by (rule bind_event_cong)

lemma bind_event_cong_code: "x = y \<Longrightarrow> bind x f = bind y f"
  by simp

lemma bind_map_event: "bind (map_event f x) g = bind x (g \<circ> f)"
by(cases x) simp_all

lemma set_bind_event [simp]: "set_event (bind x f) = (\<Union>((set_event \<circ> f) ` set_event x))"
by(cases x) auto

lemma map_conv_bind_event: "map_event f x = bind x (EventMsg \<circ> f)"
by(cases x) simp_all

end

setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm bind_event_cong_code})\<close>


context
begin

qualified definition these :: "'a event set \<Rightarrow> 'a set"
  where "these A = invEventMsg ` {x \<in> A. x \<noteq> Tick}"

lemma these_empty [simp]: "these {} = {}"
  by (simp add: these_def)

lemma these_insert_Tick [simp]: "these (insert Tick A) = these A"
  by (auto simp add: these_def)

lemma these_insert_EventMsg [simp]: "these (insert (EventMsg x) A) = insert x (these A)"
proof -
  have "{y \<in> insert (EventMsg x) A. y \<noteq> Tick} = insert (EventMsg x) {y \<in> A. y \<noteq> Tick}"
    by auto
  then show ?thesis by (simp add: these_def)
qed

lemma in_these_eq: "x \<in> these A \<longleftrightarrow> EventMsg x \<in> A"
proof
  assume "EventMsg x \<in> A"
  then obtain B where "A = insert (EventMsg x) B" by auto
  then show "x \<in> these A"
    by simp
next
  assume "x \<in> these A"
  then show "EventMsg x \<in> A" by (auto simp add: these_def)
qed

lemma these_image_EventMsg_eq [simp]: "these (EventMsg ` A) = A"
  by(auto simp add: these_def,intro image_eqI,auto)
  
lemma EventMsg_image_these_eq: "EventMsg ` these A = {x\<in>A. x \<noteq> Tick}"
  by (auto simp add: these_def,intro image_eqI,auto)

lemma these_empty_eq: "these B = {} \<longleftrightarrow> B = {} \<or> B = {Tick}"
  by (auto simp add: these_def)

lemma these_not_empty_eq: "these B \<noteq> {} \<longleftrightarrow> B \<noteq> {} \<and> B \<noteq> {Tick}"
  by (auto simp add: these_empty_eq)

end

lemma finite_range_EventMsg: "finite (range (EventMsg :: 'a \<Rightarrow> 'a event)) = finite (UNIV :: 'a set)"
  by (auto dest: finite_imageD intro: inj_EventMsg)



context includes lifting_syntax
begin

lemma event_bind_transfer [transfer_rule]:
  "(rel_event A ===> (A ===> rel_event B) ===> rel_event B)
    EventDatatype.bind EventDatatype.bind"
  unfolding rel_fun_def split_event_all by simp

lemma pred_event_parametric [transfer_rule]:
  "((A ===> (=)) ===> rel_event A ===> (=)) pred_event pred_event"
  by (rule rel_funI)+ (auto simp add: rel_event_unfold EventDatatype.is_Tick_def dest: rel_funD)

end



lemma finite_event_UNIV [simp]:
  "finite (UNIV :: 'a event set) = finite (UNIV :: 'a set)"
  by (auto simp add: UNIV_event_conv elim: finite_imageD intro: inj_EventMsg)

instance event :: (finite) finite
  by standard (simp add: UNIV_event_conv)



lemma equal_Tick_code_unfold :
  "HOL.equal x Tick \<longleftrightarrow> EventDatatype.is_Tick x"
  "HOL.equal Tick = EventDatatype.is_Tick"
  by (auto simp add: equal EventDatatype.is_Tick_def)


end
