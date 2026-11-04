theory SBElement
  imports Channel
begin

declare %invisible[[show_types]]
declare %invisible[[show_consts]]

default_sort %invisible chan

                                              text\<open>\label{sec:sbelem}\<close>

text\<open>Before we define the \acrfull{sb} datatype, we define a type for 
stream bundle elements. The difference between both types is, that
\glspl{sb} map channels to streams but a stream bundle element maps
channels to a single message.\\
A stream bundle element is a function from a @{class chan} type 
to a message @{type M} in @{const ctype} and quite useful in our 
later theories. But how can we define a non partial function, if the 
domain of our type is empty? Then the function can never map to any 
message and would be partial. To still retain the totality property
in all possible cases, we define a stream bundle element as some total 
function, if the domain is not empty, and as nothing (@{const None})
if the domain is empty. The totality leads to shorter proofs because
less cases have to be checked.\<close>

fun sbElem_well :: "('cs \<Rightarrow> M) option \<Rightarrow> bool" where
"sbElem_well    None    = chDomEmpty TYPE('cs)" |
"sbElem_well (Some sbe) = (\<forall>c. sbe c \<in> ctype(Rep c))" 

text\<open>Predicate @{const sbElem_well} exactly describes our 
requirements. The @{type option} type in our predicate allows us to 
have the (@{const None}) function, iff the domain of our channel 
type is empty. For all non-empty domains, a total function is a 
sbElem, iff it only maps to messages in the @{const ctype} of the 
channel. With those preparations we now define the sbElem type:\<close>

typedef 'cs sbElem ("(_\<^sup>\<surd>)"     [1000] 999     ) =
        "{f::('cs \<Rightarrow> M) option. sbElem_well f}"
proof(cases "chDomEmpty(TYPE('cs))")
  case True
  then show ?thesis
    apply(rule_tac x=None in exI)
    by (simp add: chDom_def)
next
  case False
  then have "\<forall>c\<in>(range (Rep::'cs\<Rightarrow>channel)). ctype c \<noteq> {}"
    using cEmpty_def chDom_def chan_botsingle by blast
  then have "sbElem_well 
             (Some(\<lambda>(c::'cs). (SOME m. m \<in> ctype (Rep c))))"
    apply(simp add: sbElem_well.cases,auto)
    by (simp add: some_in_eq)
  then show ?thesis
    by blast
qed

text\<open>The suffix \<open>(_\<^sup>\<surd>)\<close> abbreviates \<open>'cs sbElem\<close> to \<open>'cs\<^sup>\<surd>\<close>.\<close>


text\<open>The order of @{type sbElem}s then has to be a discrete one. 
Else its order would be inconsistent to our prefix order on streams 
and also the resulting \gls{sb} order.\<close>

instantiation  sbElem::(chan) discrete_cpo
begin
  definition below_sbElem::"'cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<surd> \<Rightarrow> bool" where
  "below_sbElem sbe1 sbe2 \<equiv> sbe1 = sbe2"

  instance
    by(standard, simp add: below_sbElem_def)
end


lemma sbe_eqI:"Rep_sbElem sbe1 = Rep_sbElem sbe2 \<Longrightarrow> sbe1 = sbe2"
  by (simp add: Rep_sbElem_inject)

lemma sbelemwell2fwell[simp]:"Rep_sbElem sbe = f \<Longrightarrow> sbElem_well f"
  using Rep_sbElem by auto

                                    text\<open>\label{sub:sbeprop}\<close>

lemma sbtypeempty_sbewell:"chDomEmpty TYPE ('cs) 
                          \<Longrightarrow> sbElem_well (None::('cs \<Rightarrow> M) option)"
  by(simp add: chDom_def)

lemma sbtypeempty_notsbewell:"chDomEmpty TYPE ('cs) 
                           \<Longrightarrow> \<not>sbElem_well (Some (f::'cs \<Rightarrow> M))"
  by(simp add: chDom_def)

lemma sbe_emptyiff: fixes sbe :: "'cs\<^sup>\<surd>"
  shows "Rep_sbElem sbe = None \<longleftrightarrow> chDomEmpty TYPE('cs)"
  apply auto[1]
  apply (metis equals0D sbElem_well.simps(1) sbelemwell2fwell)
  by (metis sbElem_well.elims(1) sbelemwell2fwell sbtypeempty_notsbewell)

text\<open>The following three theorems describe the behaviour of the 
@{type sbElem} type for empty and non-empty domains. Hence, they 
verify the desired properties of our type.\<close>

theorem sbtypeepmpty_sbenone[simp]:
  fixes sbe::"'cs\<^sup>\<surd>"
  assumes "chDomEmpty TYPE ('cs)"
  shows "sbe = Abs_sbElem None"
  using assms
  apply(simp add: chDom_def)
  apply(rule sbe_eqI)
  by (metis Diff_eq_empty_iff not_Some_eq Rep_sbElem mem_Collect_eq 
      chDom_def sbtypeempty_notsbewell)

text\<open>In case of the empty domain, any @{type sbElem} is 
@{const None}. Hence, we now have to look at the behaviour for 
non-empty domains.\<close>

theorem sbtypefull_none[simp]:
  fixes sbe::"'cs\<^sup>\<surd>"
  assumes "\<not>chDomEmpty TYPE ('cs)"
  shows "Rep_sbElem sbe \<noteq> None"
  using sbElem_well.simps(1) assms sbelemwell2fwell by blast

text\<open>First we show that a @{type sbElem} with a non-empty domain never is 
@{const None}. Thus, it is easy to show that there always exists a
total function, that is an @{type sbElem}, if the domain is empty. 
It follows directly from the non-emptiness of a type.\<close>

theorem sbtypenotempty_somesbe:
  assumes "\<not>chDomEmpty TYPE ('cs)"
  shows "\<exists>f::'cs \<Rightarrow> M. sbElem_well (Some f)"
  using assms sbElem_well.simps(1) sbelemwell2fwell by blast



setup_lifting %invisible type_definition_sbElem
                                           text\<open>\label{sub:sbefun}\<close>

definition sbegetch::"'e \<Rightarrow> 'c\<^sup>\<surd> \<Rightarrow> M"where 
"sbegetch c = (\<lambda> sbe. if (Rep c\<in> chDom TYPE ('c)) 
                then ((the (Rep_sbElem sbe)) (Abs (Rep c))) 
                else if (ctype (Rep c) = {}) then undefined else 
                SOME out. out \<in> ctype (Rep c))"

lemma sbegetch_ctype: 
  assumes "Rep (c::'e) \<in> chDom TYPE ('d)" 
  and "\<not>chDomEmpty(TYPE('d))"
  shows "sbegetch c (sbe2::'d\<^sup>\<surd>) \<in> ctype ((Rep::'e \<Rightarrow> channel) c)"
  using assms apply(simp add: sbegetch_def,auto)
  by (metis assms(2) option.collapse rep_reduction 
      sbElem_well.simps(2) sbelemwell2fwell sbtypefull_none)

lemma sbegetch_well[simp]: assumes"ctype (Rep c) \<noteq> {}"
  shows"sbegetch c sbe \<in> ctype (Rep c)"
  apply(simp add: sbegetch_def,auto simp add: assms)
  apply (metis empty_iff sbegetch_def sbegetch_ctype)
  by (simp add: assms some_in_eq)

lemma sbegetch_insert:
  fixes sbe :: "'a\<^sup>\<surd>"
  assumes "Rep c \<in> chDom TYPE('a)"
  shows "sbegetch c sbe = (the (Rep_sbElem sbe)) (Abs (Rep c))"
  by (simp add: sbegetch_def assms)


lift_definition sbeConvert::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>"is
"(\<lambda>sbe. if chDom TYPE('d) = {} then None else (Some (\<lambda>c. sbegetch c sbe)))"
  by auto

lemma sberestrict_getch:
  assumes"Rep (c::'c) \<in> chDom TYPE ('d)"
  and "\<not>(chDomEmpty TYPE('c))"
  shows "sbegetch c ((sbeConvert::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>) sbe) = sbegetch c sbe"
  using assms
  apply(simp add: sbeConvert.rep_eq sbegetch_def)
  using dom2ctypenempty by auto  


lift_definition sbeUnion::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>"is
"(\<lambda>sbe1 sbe2. if chDom TYPE ('e) = {} then None else (Some(\<lambda> c. 
if (Rep c \<in> chDom TYPE ('c)) 
    then sbegetch c sbe1 
    else  sbegetch c sbe2)))"
  by simp

lemma sbeunion_getchfst2[simp]:
  assumes "Rep (c::'e) \<in> chDom TYPE('c)"
  and "\<not>(chDomEmpty TYPE('e))"
  shows "sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) 
       = sbegetch c sbe1"
  apply(simp add: sbeUnion.rep_eq sbegetch_def)
  by (auto simp add: assms)

lemma sbeunion_getchsnd2:
  assumes "Rep (c::'e) \<in> chDom TYPE('d)"
  and "Rep c \<notin> chDom TYPE ('c)"
  and "\<not>(chDomEmpty TYPE('e))"
shows"sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) = 
      sbegetch c sbe2"
  apply(simp add: sbeUnion.rep_eq sbegetch_def)
  by (auto simp add: assms)
 

definition sbeRenameCh::"('cs1 \<Rightarrow> 'cs2) \<Rightarrow> 'cs2\<^sup>\<surd>  \<Rightarrow> 'cs1\<^sup>\<surd>" where
"sbeRenameCh f = (\<lambda> sbe.  Abs_sbElem  ( if (\<forall>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)) 
          then Some (\<lambda>c. sbegetch (f c) sbe)
          else None))" 

lemma sberenamech_rep: 
  fixes f::"'a \<Rightarrow> 'b"
  assumes "\<not>chDomEmpty TYPE ('b)"
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "(Rep_sbElem (sbeRenameCh f sbe)) = Some (\<lambda>c. sbegetch (f c) sbe)"
  apply (simp add: assms sbeRenameCh_def)
  apply (rule Abs_sbElem_inverse)
  apply (rule CollectI,simp)
  apply (rule allI)
  apply (case_tac "ctype (Rep (f c)) = {}")
  apply (simp add: assms; fail)
  using assms(2) sbegetch_well by blast

lemma sberenamech_getch[simp]: 
  fixes f::"'a \<Rightarrow> 'b"
  assumes "\<not>chDomEmpty TYPE ('b)"
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  shows "sbegetch c (sbeRenameCh f sbe)  = sbegetch (f c) sbe"
  apply (simp add: sbeRenameCh_def assms sbegetch_insert)
  apply (subst sbegetch_insert)
  apply (metis assms(1) assms(2) chdom_in dom2ctypeempty dom2ctypenempty empty_subsetI subset_antisym)
  apply (subst Abs_sbElem_inverse)
  apply (rule CollectI,simp add: assms)
  apply (metis abs_rep_id assms(1) assms(2) chdom_in dom2ctypenempty in_mono sbegetch_def sbegetch_well)
  by simp

lemma sberenamecompfg:
  fixes  g :: "'b \<Rightarrow> 'c"
  and f :: "'a \<Rightarrow> 'b"
  assumes "\<not>chDomEmpty TYPE ('c)"
  assumes "\<And>c. ctype (Rep (f c)) \<subseteq> ctype (Rep c)"
  and"\<And>c. ctype (Rep (g c)) \<subseteq> ctype (Rep c)"
  shows"sbeRenameCh f o sbeRenameCh g = sbeRenameCh(g o f)"
  apply (rule fun_eqI)
  apply (rule sbe_eqI,simp)
  apply (subst sberenamech_rep)
  using assms(1) assms(3) apply force
  apply (simp add: assms; fail)
  apply (simp add: assms sberenamech_rep)
  apply (subst sberenamech_rep)
  apply (simp add: assms; fail)
  using assms(2) assms(3) apply auto[1]
  by simp

lemma sberename_id_surj:
  fixes f ::" 'b \<Rightarrow> 'a"
  assumes "surj f"
  and "\<And>c. ctype (Rep (f c)) = ctype (Rep c)"
  and "chDom TYPE('a) \<noteq> {}"
  shows "sbeRenameCh (inv f) o sbeRenameCh f = id"
  apply (subst sberenamecompfg)
  apply (simp_all add: assms)
  apply (metis assms(1) assms(2) equalityE surj_f_inv_f)
  by (simp add: comp_def assms surj_f_inv_f sbeRenameCh_def sbegetch_def Rep_sbElem_inverse id_def)

lemma sberename_id_inj:
  fixes f ::" 'b \<Rightarrow> 'a"
  assumes "inj f"
  and "\<And>c. ctype (Rep (inv f c)) = ctype (Rep c)"
  and "chDom TYPE('b) \<noteq> {}"
  shows "sbeRenameCh f o sbeRenameCh (inv f) = id"
  apply (subst sberenamecompfg)
  apply (simp_all add: assms)
  apply (metis assms(1) assms(2) inv_f_f order_refl)
  apply(rule fun_eqI,rule sbe_eqI)
  by (simp add: sberenamech_rep assms sbegetch_insert)



lemma sbenotnone[simp]: "chDom TYPE('a) \<noteq> {} \<Longrightarrow> (Rep_sbElem (sbe::'a\<^sup>\<surd>)) \<noteq> None"
  by (simp add: sbe_emptyiff)

lemma sbenotnone2[simp]: "chDom TYPE('a) \<noteq> {} \<Longrightarrow> \<exists>y. Rep_sbElem (sbe::'a\<^sup>\<surd>) = Some y"
  apply(subgoal_tac " Rep_sbElem sbe \<noteq> None") 
  apply blast
  by simp


definition sbelist::"'cs \<Rightarrow> 'cs::{chan}\<^sup>\<surd> \<Rightarrow> msg list"where
"sbelist c sbe = m2list (sbegetch c sbe)"

lemma[code]:"sbelist (c::'cs::{chan}) sbe = m2list (if (Rep c\<in> chDom TYPE ('cs)) 
                then ((the (Rep_sbElem sbe)) c) else undefined)" 
  apply(auto simp add: sbelist_def sbegetch_def)[1]
  by (metis chdom_in dom2ctypeempty ex_in_conv)


end
