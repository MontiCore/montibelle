theory BroyDatatypes 

imports Main "HOL-Datatype_Examples.TLList" "stream.Stream" "bundle.SB"
begin

default_sort "{cpo,conc}"
definition semRum96::"('state\<times>'out) set \<Rightarrow> (('state \<times> 'in) \<rightarrow> 'out) set \<Rightarrow> ('in \<rightarrow>'out) set" where
"semRum96 initConfig H = {g | g. \<exists>h\<in>H. \<exists>sInit outInit. (sInit,outInit) \<in> initConfig 
                                      \<and> (\<forall>input. g\<cdot>input = outInit \<Zcat>\<Zcat>h\<cdot>(sInit,input))}"

definition semOur::"('state\<times>'out) set \<Rightarrow> ('state \<Rightarrow> (('in \<rightarrow> 'out) set))
  \<Rightarrow> ('in \<rightarrow> 'out) set" where
"semOur initConfig G = {(\<Lambda> sb. initOut \<Zcat>\<Zcat> g\<cdot>sb) | initOut initState g.
                    (initState,initOut) \<in> initConfig 
                      \<and> g\<in>G initState}"

definition mapF::"(('state \<times> 'in) \<rightarrow> 'out) set
            \<Rightarrow> ('state \<Rightarrow> (('in \<rightarrow> 'out) set))" where
"mapF H state =  {( \<Lambda> input. h\<cdot>(state,input)) | h. h\<in>H}"

lemma f_def2: "mapF A state =  (\<lambda> h. \<Lambda> input. h\<cdot>(state,input)) ` A"
  using mapF_def apply auto
  done

lemma h1: "semOur init (mapF h) \<subseteq> semRum96 init h"
  unfolding semRum96_def semOur_def mapF_def
  apply auto
  by auto

lemma h2: fixes h::"(('state \<times> 'in) \<rightarrow> 'out) set"
  shows "semRum96 init h \<subseteq> semOur init (mapF h)"
  unfolding semRum96_def semOur_def f_def2
  apply (auto simp add: image_iff)
proof -
  fix x::"('in \<rightarrow> 'out)"
  fix  ha sInit outInit
  assume as1: "(sInit, outInit) \<in> init" and as2: "\<forall>input. x\<cdot>input = outInit\<Zcat>\<Zcat>ha\<cdot>(sInit, input)"
    and "ha \<in> h" 
  show "\<exists>initOut initState spf.
          (x = (\<Lambda> sb. initOut\<Zcat>\<Zcat>spf\<cdot>sb) 
             \<and> (initState, initOut) \<in> init 
          \<and> (\<exists>x\<in>h. spf = (\<Lambda> input. x\<cdot>(initState, input))))" 
    apply(intro exI[where x=outInit] exI[where x=sInit] exI[where x="(\<Lambda> input. ha\<cdot>(sInit, input))"])
    apply auto
    apply(rule cfun_eqI, simp)
    using as1 as2 apply auto
    using \<open>ha \<in> h\<close> by auto
qed

theorem "semOur init (mapF h) = semRum96 init h"
  using h1 h2 by blast












default_sort type


text\<open>Im Paper: \<open>TS[M] = (\<nat>\<^sub>+ \<Rightarrow> M*)\<close>\<close>

type_synonym 'm TS = "nat \<Rightarrow> 'm list"



text \<open>Im Paper: \<open>ST[M] = (\<nat>\<^sub>+ \<Rightarrow> M) \<union> \<Union>n\<in>\<N>.([1:n] \<Rightarrow> M)\<close>\<close>

typedef 'm ST = "{f::(nat \<Rightarrow> 'm option) | f. \<forall>n. \<exists>x. f n = Some x} \<union> (\<Union>n. {f::nat \<Rightarrow> 'm option| f. (\<forall>m<n. \<exists>x. f m = Some x) \<and> (\<forall>m\<ge>n. f m = None)})"
  by auto

setup_lifting type_definition_ST


type_synonym 'm ST_1 = "nat \<Rightarrow> 'm option" 

definition st_1__well::"'m ST_1 \<Rightarrow> bool" where
"st_1__well f \<equiv> \<forall>n. f n = None \<longrightarrow> (\<forall>m. m>n \<longrightarrow> f m = None)"


typedef 'm ST_1' = "{f::'m ST_1 | f. st_1__well f}"
  by (auto simp add: st_1__well_def)

setup_lifting type_definition_ST_1'



lemma [simp]:"Rep_ST ST n = None \<Longrightarrow> n < m \<Longrightarrow> Rep_ST ST m = None"
  apply(insert Rep_ST[of ST],auto)
  apply (metis option.distinct(1))
  by (metis dual_order.strict_trans not_le_imp_less option.distinct(1))


lemma "st_1__well (Rep_ST_1' st)"
  using Rep_ST_1' by auto

lemma [simp]:"(\<forall>n. \<exists>x. Rep_ST_1' ST_1' n = Some x) \<or>
       (\<exists>x. (\<forall>m<x. \<exists>x. Rep_ST_1' ST_1' m = Some x) \<and> (\<forall>m\<ge>x. Rep_ST_1' ST_1' m = None))"
  apply(insert Rep_ST_1'[of ST_1'],simp add: st_1__well_def)
  apply(auto)
  apply(induct_tac n,auto)
  apply (metis gr_implies_not_zero neq0_conv not_None_eq)
  by (metis le_neq_implies_less linorder_neqE_nat not_less_eq option.exhaust)

lemma st1_eqI: assumes"Rep_ST_1' x = Rep_ST_1' y"
  shows "x = y"
  using Rep_ST_1'_inject assms by auto

lift_definition stmapping::"'m ST_1' \<Rightarrow> 'm ST" is
"\<lambda>m. (Rep_ST_1' m)"
  by simp

lift_definition invstmapping::"'m ST \<Rightarrow> 'm ST_1'" is
"\<lambda>m. (Rep_ST m)"
  by (auto simp add: st_1__well_def)

lemma stmapping_bij[simp]:"bij stmapping"
  apply(rule bijI)
  apply(rule injI)
  apply (metis Rep_ST_1'_inverse stmapping.rep_eq)
  apply(rule surjI[where f="invstmapping"])
  by (simp add: Rep_ST_inverse invstmapping.rep_eq stmapping.abs_eq)

lemma invst[simp]:"inv stmapping = invstmapping"
  apply(rule inj_imp_inv_eq)
  apply (simp add: bij_is_inj)
  apply rule
  by (simp add: Rep_ST_inverse invstmapping.rep_eq stmapping.abs_eq)

lemma invstmapping_bij[simp]:"bij invstmapping"
  using bij_imp_bij_inv stmapping_bij by fastforce

lemma invinvst[simp]:"inv invstmapping = stmapping"
  using inv_inv_eq stmapping_bij by fastforce




type_synonym 'm ST_2 = "'m llist"




type_synonym 'm ST_3 = "'m::countable stream"

definition st_3__2__st_1::"'m::countable ST_3 \<Rightarrow> 'm ST_1" where
"st_3__2__st_1 stream index \<equiv> if(Fin index < #stream) then Some (snth index stream)
                                                      else None"



definition tsValues::"'m TS \<Rightarrow> 'm set" where
"tsValues f \<equiv> \<Union>n. set (f n)"

definition tsb_well :: "('c::chan \<Rightarrow> M TS) \<Rightarrow> bool" where
"tsb_well f \<equiv> \<forall>c. tsValues (f c) \<subseteq> ctype (Rep c)"

typedef 'c::chan tsb 
         = "{f::('c::chan \<Rightarrow> M TS). tsb_well f}"
  by (auto simp add: ctype_def tsValues_def tsb_well_def)
 

type_synonym ('m_in,'m_out) sps_1 = "'m_in ST_1 \<Rightarrow> ('m_out ST_1 set)"






text\<open>
\<^enum> Broy verwendet \<open>\<N>\<^sub>+\<close>, in dem die \<open>0\<close> nicht vorkommt anstatt die normalen \<open>nat\<close>
\<close>

end