<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Datatype.ftl" as datatype>
<#t><#import "../helper/Type.ftl" as type>
<#t><#import "../helper/Tuple.ftl" as tuple>
<#t><#import "../helper/Channel.ftl" as channelHelp>
<#t><#import "../helper/Configuration.ftl" as config>
<#t><#import "../helper/State.ftl" as state>
<#t><#import "../helper/Output.ftl" as output>
<#t>
<#t>
<#t><#-- @ftlvariable name="tc"         type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"    type="Boolean" -->
<#t><#-- @ftlvariable name="th"         type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"        type="montibelle.focus._ast.ASTRefinement" -->
<#t>
<#t><#-- @ftlvariable name="rough"      type="montibelle.focus._symboltable.SpecificationSymbol" -->
<#t><#-- @ftlvariable name="refined"    type="montibelle.focus._symboltable.AutomatonSymbol" -->
<#t><#-- @ftlvariable name="refinedAst" type="montibelle.focus._ast.ASTEventAutomaton" -->
<#t><#-- @ftlvariable name="trans"      type="montibelle.focus._ast.ASTTransition"-->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#assign roughName = ref.rough.theorySymbol.filename>
<#t><#assign refinedName = ref.refined.theorySymbol.filename>
<#t><#assign roughInputFName = ref.rough.input.theorySymbol.filename>
<#t><#assign roughOutputFName = ref.rough.output.theorySymbol.filename>
<#t>
<#t><#assign rough = ref.rough>
<#t><#assign refined = ref.refined>
<#t><#assign refinedAst = ref.refined.astNode>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen *) Smart_Isabelle.Smart_Isabelle
              ${ref.rough.theorySymbol.importFrom(ref.theorySymbol)} <#rt>
              <#lt>${ref.refined.theorySymbol.importFrom(ref.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin

                                                                                 
declare [[names_short = false]]


<#macro tranStart trans generic=false>
<#-- @ftlvariable name="trans"       type="montibelle.focus._ast.ASTTransition"
     @ftlvariable name="generic"     type="Boolean" -->
(StateConstr <#if generic>state<#else>Substate.${trans.start}</#if><#rt>
  <#list refinedAst.states.stateVariableList as var>
    <#lt> ${var.pattern}<#rt>
  </#list>
  <#lt>)<#rt>
</#macro>

(* channel lemmas *)

<#t><#assign not_lemmas = [] />
<#list rough.input.channels + rough.output.channels as c>
  <#list ref.datatypes.astNode.channelTypes as t>
    <#if typePrinter.print(t.symType) != typePrinter.print(c.typeSymbol.symType)>
      <#t><#assign not_lemma = "not_${c.localName}_${typePrinter.print(t.symType)}" />
      <#t><#assign not_lemmas = not_lemmas + [ not_lemma ] />
lemma ${not_lemma}: "Rep_msgWithChan z \<noteq> (${c.localName}, ${type.constructor(t)} x)"
  by(cases z,case_tac x;auto simp add: well_def Abs_msgWithChan_inverse)

    </#if>
  </#list>
</#list>
<#t>
<#list rough.input.channels as c>
lemma[simp]:"${roughInputFName}.buildSB (${rough.input.channels?map(ch -> ch.pattern)?join(', ')}) <#rt>
  <#lt>${c.localName} = (Rep_cfun (smap <@type.buildSBEConstructor c.typeSymbol/>)) ${c.pattern}"
  by(simp add: ${roughInputFName}.buildSB_def)

</#list>
<#list rough.output.channels as c>
lemma[simp]:"${roughOutputFName}.buildSB (${rough.output.channels?map(ch -> ch.pattern)?join(', ')}) <#rt>
  <#lt>${c.localName} = (Rep_cfun (smap <@type.buildSBEConstructor c.typeSymbol/>)) ${c.pattern}"
  by(simp add: ${roughOutputFName}.buildSB_def)

</#list>
<#list rough.input.channels + rough.output.channels as c>
lemma ${c.localName}_imp_${typePrinter.print(c.typeSymbol.symType)}:
  assumes "fst (Rep_msgWithChan a) = ${c.localName}"
  shows "\<exists>m. Rep_msgWithChan a = (${c.localName}, ${type.constructor(c.typeSymbol)} m)"
  by(metis msg.exhaust assms prod.collapse<#list not_lemmas as nl> ${nl}</#list>)

</#list>

(* input channel abbreviations *)

<#list rough.input.channels as chan>
abbreviation ${chan.localName}Abbr::"${roughInputFName}.channels\<^sup>\<Omega> \<Rightarrow> ${type.timedType(chan.typeSymbol)} stream" where
  "${chan.localName}Abbr sb \<equiv> ${tuple.split(rough.input.channels?size, "(${roughInputFName}.sbgetter\\<cdot>sb)")?split(',')[chan?index]}"

abbreviation ${chan.localName}_efilter::"${roughInputFName}.channels msgWithChan event stream \<rightarrow> ${type.timedType(chan.typeSymbol)} stream" where
  "${chan.localName}_efilter \<equiv> (emap (inv ${type.constructor(chan.typeSymbol)})) oo (eventFilter ${chan.localName})"

definition ${chan.localName}_sfilter::"${roughInputFName}.channels msgWithChan stream \<Rightarrow> ${typePrinter.print(chan.typeSymbol.symType)} stream" where
  "${chan.localName}_sfilter s = smap (inv ${type.constructor(chan.typeSymbol)})\<cdot><#rt>
  <#lt>(smap snd\<cdot>({m. fst m = ${chan.localName}} \<ominus> (smap Rep_msgWithChan\<cdot>s)))"

definition ${chan.localName}f::"${roughInputFName}.channels msgWithChan list \<Rightarrow> ${typePrinter.print(chan.typeSymbol.symType)} list" where
  "${chan.localName}f = (\<lambda>ls. map ((inv ${type.constructor(chan.typeSymbol)}) o snd) <#rt>
  <#lt>(filter (\<lambda>m. fst m = ${chan.localName}) (map Rep_msgWithChan ls)))"

</#list>

(* lemmas over abbreviations *)

<#list rough.input.channels as chan>
lemma ${chan.localName}f_empty[simp]:"${chan.localName}f [] = []"
  by(simp add: ${chan.localName}f_def)

  <#list rough.input.channels as chan2>
lemma ${chan.localName}f_${chan2.localName}[simp]:
  assumes "Rep_msgWithChan a = (${chan2.localName}, ${type.constructor(chan2.typeSymbol)} m)"
  shows "${chan.localName}f (a#ls) = <#if chan2.typeSymbol.name == chan.typeSymbol.name>m # </#if>${chan.localName}f ls"
  by(simp add: assms ${chan.localName}f_def)

  </#list>
lemma ${chan.localName}_sfilter2filter:
  assumes "#s < \<infinity>"
  shows "${chan.localName}_sfilter s = <(${chan.localName}f (s2list s))>"
  apply(simp add: ${chan.localName}_sfilter_def ${chan.localName}f_def)
  apply(induction s rule: finind3)
  by(simp_all add: assms)

</#list>

(* filter_input_noop lemmas *)

lemma efilter_input_noop:
  "efilter (\<lambda>(c,m). <#list rough.input.channels as chan>(c = ${chan.localName})<#sep> \<or> </#list>)
    \<cdot>(emap Rep_msgWithChan\<cdot>i) = emap Rep_msgWithChan\<cdot>i"
  apply(induction i,simp_all)
  apply(case_tac a;simp)
  apply(case_tac aa;case_tac y;case_tac ab;simp)
  by (simp add: Abs_msgWithChan_inverse2)+

lemma efilter_input_noop2:
  "(efilter (\<lambda>m. <#list rough.input.channels as chan>(fst m = ${chan.localName})<#sep> \<or> </#list>)
    \<cdot>(emap Rep_msgWithChan\<cdot>i)) = (emap Rep_msgWithChan\<cdot>i)"
  using efilter_input_noop by(simp add: case_prod_beta')

lemma sfilter_input_noop:
  "\<forall>t. {m. <#list rough.input.channels as chan>(fst m = ${chan.localName})<#sep> \<or> </#list>}
  \<ominus> smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i) = smap Rep_msgWithChan\<cdot>(esnth t\<cdot>i)"
  by(simp add: efilter_input_noop2 smap_esnth filter_esnth)


(* input eq lemmas *)

<#list rough.input.channels as chan>
lemma ${chan.localName}_prefix_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "${chan.localName}_efilter\<cdot>i \<sqsubseteq> ${chan.localName}Abbr sb"
proof(-)
  have h1: "emap (inv ${type.constructor(chan.typeSymbol)})\<cdot><#rt>
  <#lt>(emap ${type.constructor(chan.typeSymbol)}\<cdot>(${chan.localName}Abbr<#rt>
  <#lt> sb)) = (${chan.localName}Abbr sb)"
      by(simp add: emaps2emap)

  obtain <#list rough.input.channels as i>x${i?counter} </#list>where ab_def: <#rt>
    <#lt>"sb = ${roughInputFName}.sbsetter\<cdot>(<#list rough.input.channels as i>x${i?counter}<#sep>,</#list>)"
    by(metis ${roughInputFName}.SB.set_get prod.exhaust_sel)
  have "(sb \<^enum> ${chan.localName}) = (smap (${type.prefix(chan.typeSymbol.timingSymbol)?split('o')[0..1]?join('o')})\<cdot><#rt>
    <#lt>(emap ${type.constructor(chan.typeSymbol)}\<cdot>(${chan.localName}Abbr sb)))"
    apply(simp add: ab_def)
    apply(induction x${chan?counter};simp)
    by(case_tac a;simp)
  then have "emap snd\<cdot>(efilter (\<lambda>(c, m). c = ${chan.localName})\<cdot><#rt>
    <#lt>(emap Rep_msgWithChan\<cdot>i)) \<sqsubseteq> emap ${type.constructor(chan.typeSymbol)}\<cdot>(${chan.localName}Abbr sb)"
    using assms ssplit_prefixsb[where sb=sb]
    by(metis M.inject(2) M_timed.inject(3) comp_eq_dest_lhs smapnotbelow somechannotempty)
  then show ?thesis
    apply(simp add: eventFilter_def)
    using h1 by(metis monofun_cfun_arg)
qed

lemma ${chan.localName}_evalues_subset:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  shows "eValues\<cdot>(${chan.localName}_efilter\<cdot>i) \<subseteq> eValues\<cdot>(${chan.localName}Abbr sb)"
  apply(subst set_monofun_cfun; simp_all)
  using assms ${chan.localName}_prefix_eq by simp

lemma ${chan.localName}_esnth_eq:
  assumes "uSplit\<cdot>i \<sqsubseteq> sb"
  and "#\<^sub>\<surd> i = \<infinity>"
  shows "\<forall>t. (esnth t\<cdot>(${chan.localName}Abbr sb)) = ${chan.localName}_sfilter (esnth t\<cdot>i)"
proof(-)
  obtain <#list rough.input.channels as i>x${i?counter} </#list>where ab_def: "sb = <#rt>
    <#lt>${roughInputFName}.sbsetter\<cdot>(<#list rough.input.channels as i>x${i?counter}<#sep>,</#list>)"
    by(metis ${roughInputFName}.SB.set_get prod.exhaust_sel)
  have "${chan.localName}Abbr sb = emap (inv ${type.constructor(chan.typeSymbol)})\<cdot><#rt>
    <#lt>(smap (${type.prefix(chan.typeSymbol.timingSymbol)?split('o')[0..1]?reverse?map(t -> "inv ${t?trim}")?join(" \\<circ> ")})\<cdot><#rt>
    <#lt>(sb \<^enum> ${chan.localName}))"
    apply(simp add: ab_def)
    apply(induction x${chan?counter};simp)
    by(case_tac a;simp)
  then show ?thesis
    apply(simp add: ${chan.localName}_sfilter_def)
    apply(subst ssplit_esnth_eq[where sb=sb])
    by(simp_all add: assms smap_esnth)
qed

</#list>

(* ticksb output lemmas *)

lemma sbsetter_ticksb:"${roughOutputFName}.sbsetter\<cdot>(<#list rough.output.channels as chan>\<up>Tick<#sep>, </#list>) = ticksb"
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb: "${roughOutputFName}.sbgetter\<cdot>ticksb = (<#list rough.output.channels as chan>\<up>Tick<#sep>, </#list>)"
  apply(subst(2) ${roughOutputFName}.SB.get_set[symmetric])
  apply(rule cfun_arg_cong)
  apply(rule sb_rep_eqI)
  apply(simp add: ticksb.rep_eq)
  by (case_tac c;simp)

lemma sbgetter_ticksb2[simp]: "${roughOutputFName}.sbgetter\<cdot>(ticksb \<Zcat>\<Zcat> s) =
  (<#list rough.output.channels as chan>\<up>Tick<#sep>, </#list>) \<Zcat>\<Zcat> ${roughOutputFName}.sbgetter\<cdot>s"
  by(simp add: sbgetter_ticksb conc_sb_def getter_conc2sbconc[symmetric])


(* usplit out lemmas *)

<#list rough.output.channels as chan>
lemma usplit_event_sbsetter_${chan.localName}_list:
  "uSplit\<cdot>(smap EventMsg\<cdot>(smap ${channelHelp.constructor(chan)}\<cdot>(<ls>))) =
    ${roughOutputFName}.sbsetter\<cdot>(<#list rough.output.channels as chan2><#rt>
    <#lt><#if chan.name == chan2.name>smap EventMsg\<cdot>(<ls>)<#else>\<epsilon></#if><#sep>, </#list>)"
  apply(rule sb_rep_eqI)
  apply(induction ls;simp)
  apply(subst demerge_estep_rep[where cs= ${chan.localName} and m="${type.constructor(chan.typeSymbol)} a"])
  apply(simp_all add: ${channelHelp.constructor(chan)}.rep_eq)
  by(case_tac c,simp_all)

lemma usplit_event_sbsetter_${chan.localName}:
  "uSplit\<cdot>(\<up>(EventMsg (${channelHelp.constructor(chan)} a)) \<Zcat> s<#---->) =
    ${roughOutputFName}.sbsetter\<cdot>(<#list rough.output.channels as chan2><#if chan.name == chan2.name>\<up><#rt>
    <#lt>(EventMsg a)<#else>\<epsilon></#if><#sep>, </#list>) \<Zcat>\<Zcat> (uSplit\<cdot>s)<#rt>
    <#lt><#---->"
  using usplit_event_sbsetter_${chan.localName}_list[where ls="[a]"] apply simp
  by(simp add: usplit_conc)?

</#list>
lemma somethingexists[simp]:
  "<#list rough.input.channels as chan>(\<exists>m${chan?counter}::${typePrinter.print(chan.typeSymbol.symType)}. <#rt>
  <#lt>Rep_msgWithChan aa = (${chan.localName}, ${type.constructor(chan.typeSymbol)} m${chan?counter}))<#sep> \<or>
   </#list>"
  apply(auto)?
  apply(cases aa;case_tac y;case_tac a;case_tac b;simp add: well_def)?
  <#if not_lemmas?has_content>
  using<#list not_lemmas as nl> ${nl}</#list>
  </#if>
  apply(metis (full_types) msg.exhaust ${roughInputFName}.channels.exhaust surj_pair)?
  apply(blast+)?
  by((<#list rough.input.channels as chan>subst<#if !chan?is_first>(asm)</#if> <#rt>
  <#lt>Abs_msgWithChan_inverse, simp_all add: well_def<#sep>, </#list>)+)?


(* automaton transition lemmas *)

<#list refinedAst.initialList as init>
lemma init${init?index}_nda:"autInitConfig\<cdot>(behavior.eaut <@para.pattern refined/>) = <#rt>
  <#lt>{(<@state.new init.state/>, <#if refined.isStrong()>ticksb<#else>bottom</#if>)}"
  apply(simp add:behavior.config_def)
  by(simp add: eventGen.ndaInitConfigC_def initialConfigs_def EventLocale.outconv_def)

lemma init${init?index}_da:
  assumes "da \<in> (behavior.daset <@para.pattern refined/>)"
  shows "\<exists>foo. (dautInitConfig da) = ((<@state.new init.state/>, foo), <#if refined.isStrong()>ticksb<#else>bottom</#if>)"
proof(-)
  have "apfst fst (dautInitConfig da) = (<@state.new init.state/>, <#if refined.isStrong()>ticksb<#else>bottom</#if>)"
    using init${init?index}_nda nda2da_init eventGen.daset_def assms by<#if refined.isStrong()>(metis singleton_iff)<#else> fastforce</#if>
  then show ?thesis
    by(metis eq_fst_iff snd_conv tuple_to_apfst)
qed

</#list>
<#if refinedAst.eventTransitionList?has_content || refinedAst.tickTransitionsList?has_content>
  <#list refinedAst.eventTransitions as chan, transitions>
    <#assign done = []>
    <#list transitions as trans>
      <#if !done?seq_contains(trans)>
      <#assign duplicates = transitions?filter(t -> trans.start == t.start)?filter(t -> trans.guard == t.guard)>
      <#assign done = done + duplicates?filter(t -> t != trans)>
lemma transitionE${chan?index}${trans?index}_nda:
  assumes "Rep_msgWithChan m = (${chan.localName}, ${type.constructor(chan.typeSymbol)} ${chan.pattern})"
  and "${trans.guard}"
  <#if (duplicates?size > 1)>
  shows "((autTransition\<cdot>(behavior.eaut <@para.pattern refined/>)) (<@tranStart trans/>) (EventMsg m)) =
         {<#list duplicates as d_trans>(<@state.new d_trans.result.state/>,<#rt>
         <#lt> ${roughOutputFName}.sbsetter\<cdot>(<#list refined.output.channels as chan2><#rt>
         <#lt><#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list d_trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else>\<up><#rt>
         <#lt>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))<#sep>, </#list>}"
  <#else>
  shows "((autTransition\<cdot>(behavior.eaut <@para.pattern refined/>)) (<@tranStart trans/>) (EventMsg m)) =
         {(<@state.new trans.result.state/>, ${roughOutputFName}.sbsetter\<cdot><#rt>
         <#lt>(<#list refined.output.channels as chan2><#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))}"
  </#if>
  apply(simp add: behavior.transition_def)
  apply(simp add: EventLocale.outconv_def behavior.ndaTransition_eventC_def)
  using assms <#if (trans.result.outputList?size == 0)>by(simp)<#else><#rt>
  <#lt><#list rough.output.channels as chan2>usplit_event_sbsetter_${chan2.localName}<#rt>
  <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
  <#lt><#if out.isIsListValue()>_list</#if></#if></#list><#sep> </#list> apply(simp)
  apply(simp add: conc_sb_def setter_conc2sbconc[symmetric] conc_prod_apply)?
    (* autosledgi *) sorry</#if>

lemma transitionE${chan?index}${trans?index}_da:
  assumes "da \<in> (behavior.daset <@para.pattern refined/>)"
  and "Rep_msgWithChan m = (${chan.localName}, ${type.constructor(chan.typeSymbol)} ${chan.pattern})"
  and "${trans.guard}"
  <#if (duplicates?size > 1)>
  shows "\<exists>bar. dautTransition da (<@tranStart trans/>, foo) (EventMsg m) \<in>
         {<#list duplicates as d_trans>((<@state.new d_trans.result.state/>, bar), <#rt>
         <#lt>${roughOutputFName}.sbsetter\<cdot>(<#list refined.output.channels as chan2><#rt>
         <#lt><#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list d_trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))<#sep>, </#list>}"
  <#else>
  shows "\<exists>bar. dautTransition da (<@tranStart trans/>, foo) (EventMsg m) =
         ((<@state.new trans.result.state/>, bar), ${roughOutputFName}.sbsetter\<cdot><#rt>
         <#lt>(<#list refined.output.channels as chan2><#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))"
  </#if>
proof(-)
  <#if (duplicates?size > 1)>
  have "apfst fst (dautTransition da (<@tranStart trans/>, foo) (EventMsg m)) \<in>
        {<#list duplicates as d_trans>(<@state.new d_trans.result.state/>, ${roughOutputFName}.sbsetter\<cdot>(<#rt>
        <#lt><#list refined.output.channels as chan2><#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
        <#lt><#list d_trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
        <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
        <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))<#sep>, </#list>}"
  <#else>
  have "apfst fst (dautTransition da (<@tranStart trans/>, foo) (EventMsg m)) =
          (<@state.new trans.result.state/>, ${roughOutputFName}.sbsetter\<cdot><#rt>
          <#lt>(<#list refined.output.channels as chan2><#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
          <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
          <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
          <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>))"
  </#if>
    using transitionE${chan?index}${trans?index}_nda nda2da_trans eventGen.daset_def assms by fastforce
  then show ?thesis
    by (metis (no_types, lifting) fst_conv insert_iff prod.collapse singletonD snd_conv tuple_to_apfst)
qed

      </#if>
    </#list>
  </#list>
<#t>
  <#assign done = []>
  <#list refinedAst.tickTransitionsList as trans>
    <#if !done?seq_contains(trans)>
      <#assign duplicates = refinedAst.tickTransitionsList?filter(t -> trans.start == t.start)?filter(t -> trans.guard == t.guard)>
      <#assign done = done + duplicates?filter(t -> t != trans)>
lemma tick${trans?index}_nda:
  assumes "${trans.guard}"
        <#if (duplicates?size > 1)>
  shows "((autTransition\<cdot>(behavior.eaut <@para.pattern refined/>)) (<@tranStart trans/>) Tick) =
         {<#rt>
          <#list duplicates as d_trans><#t>
            <#lt>(<@state.new d_trans.result.state/>, ${roughOutputFName}.sbsetter\<cdot>((<#rt>
            <#list refined.output.channels as chan2><#t>
              <#lt>\<up>(Tick)<#rt>
              <#sep>, </#sep>
            </#list><#t>
            <#lt>) \<Zcat>\<Zcat> (<#rt>
            <#list refined.output.channels as chan2>
              <#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)>
                <#list d_trans.result.outputList as out>
                  <#if out.channelSymbol.name == chan2.name>
                    <#if out.isIsListValue()>
                      <#lt>(smap EventMsg\<cdot>(<${out.value}>))<#rt>
                    <#else>
                      <#lt>\<up>(EventMsg ${out.value})<#rt>
                    </#if>
                  </#if>
                </#list>
              <#else>
                <#lt>\<epsilon><#rt>
              </#if>
              <#sep>, </#sep>
            </#list><#t>
            <#lt>)))
            <#sep>, </#sep>
          </#list>}"
        <#else>
  shows "((autTransition\<cdot>(behavior.eaut <@para.pattern refined/>)) (<@tranStart trans/>) Tick) =
         {(<@state.new trans.result.state/>, ${roughOutputFName}.sbsetter\<cdot>((<#rt>
          <#list refined.output.channels as chan2><#t>
            <#lt>\<up>(Tick)<#rt>
            <#sep>, </#sep><#t>
          </#list><#t>
          <#lt>) \<Zcat>\<Zcat> (<#rt>
          <#list refined.output.channels as chan2><#t>
            <#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#t>
              <#list trans.result.outputList as out><#t>
                <#if out.channelSymbol.name == chan2.name><#t>
                  <#if out.isIsListValue()><#t>
                    <#lt>(smap EventMsg\<cdot>(<${out.value}>))<#rt>
                  <#else><#t>
                    <#lt>\<up>(EventMsg ${out.value})<#rt>
                  </#if><#t>
                </#if><#t>
              </#list><#t>
            <#else><#t>
              <#lt>\<epsilon><#rt>
            </#if><#t>
            <#sep>, </#sep><#t>
          </#list><#t>
          <#lt>)))}"
        </#if>
  apply(simp add: behavior.transition_def)
  apply(simp add: assms EventLocale.outconv_def behavior.ndaTransition_tickC_def)
  using assms sbsetter_ticksb <#if (trans.result.outputList?size == 0)>by(simp)<#else><#rt>
  <#lt><#list rough.output.channels as chan2>usplit_event_sbsetter_${chan2.localName}<#rt>
  <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
  <#lt><#if out.isIsListValue()>_list[where ls="${out.value}"]<#else><#rt>
  <#lt>[where a="${out.value}" and s=\<epsilon>]</#if></#if></#list><#sep> </#list> apply(simp)
  using conc_sb_def
    (* autosledgi *) sorry</#if>

lemma tick${trans?index}_da:
  assumes "da \<in> (behavior.daset <@para.pattern refined/>)"
  assumes "${trans.guard}"
  <#if (duplicates?size > 1)>
  shows "\<exists>bar. dautTransition da (<@tranStart trans/>, foo) Tick \<in>
         {<#list duplicates as d_trans>((<@state.new d_trans.result.state/>, bar), <#rt>
         <#lt>${roughOutputFName}.sbsetter\<cdot>((<#list refined.output.channels as chan2>\<up>(Tick)<#sep>, </#list>) <#rt>
         <#lt>\<Zcat>\<Zcat> (<#list refined.output.channels as chan2><#rt>
         <#lt><#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list d_trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>)))<#sep>, </#list>}"
  <#else>
  shows "\<exists>bar. dautTransition da (<@tranStart trans/>, foo) Tick =
         ((<@state.new trans.result.state/>, bar), ${roughOutputFName}.sbsetter\<cdot><#rt>
         <#lt>((<#list refined.output.channels as chan2>\<up>(Tick)<#sep>, </#list><#rt>
         <#lt>) \<Zcat>\<Zcat> (<#list refined.output.channels as chan2><#rt>
         <#lt><#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>)))"
  </#if>
proof(-)
  <#if (duplicates?size > 1)>
  have "apfst fst (dautTransition da (<@tranStart trans/>, foo) Tick) \<in>
         {<#list duplicates as d_trans>(<@state.new d_trans.result.state/>, <#rt>
         <#lt>${roughOutputFName}.sbsetter\<cdot>((<#list refined.output.channels as chan2><#rt>
         <#lt>\<up>(Tick)<#sep>, </#list>) \<Zcat>\<Zcat> (<#list refined.output.channels as chan2><#rt>
         <#lt><#if d_trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list d_trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>)))<#sep>, </#list>}"
  <#else>
  have "apfst fst (dautTransition da (<@tranStart trans/>, foo) Tick) =
         ((<@state.new trans.result.state/>), ${roughOutputFName}.sbsetter\<cdot><#rt>
         <#lt>((<#list refined.output.channels as chan2>\<up>(Tick)<#sep>, </#list>)<#rt>
         <#lt> \<Zcat>\<Zcat> (<#list refined.output.channels as chan2><#rt>
         <#lt><#if trans.result.outputList?map(x -> x.channelSymbol.name)?seq_contains(chan2.name)><#rt>
         <#lt><#list trans.result.outputList as out><#if out.channelSymbol.name == chan2.name><#rt>
         <#lt><#if out.isIsListValue()>(smap EventMsg\<cdot>(<${out.value}>))<#else><#rt>
         <#lt>\<up>(EventMsg ${out.value})</#if></#if></#list><#else>\<epsilon></#if><#sep>, </#list>)))"
  </#if>
  using tick${trans?index}_nda nda2da_trans eventGen.daset_def assms by fastforce
then show ?thesis
  by (metis Pair_inject prod.collapse tuple_to_apfst)
qed

    </#if>
  </#list>
</#if>

<#list rough.output.channels as chan>
lemma getch_to_getter_${chan?counter}:
  "(out \<^enum> ${chan.localName})
 = (Rep_cfun (smap <@type.buildSBEConstructor chan.typeSymbol/>)) <#rt>
  <#lt>(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>(out))")?split(', ')[chan?index]})"
  proof -
    obtain <#list rough.output.channels as o>s${o?counter} </#list>
      where s_def: "(<#list rough.output.channels as o>s${o?counter}<#sep>,</#list>) = ${roughOutputFName}.sbgetter\<cdot>(out)"
      using prod.collapse by blast
    have setter_def:"out = SB.setter\<cdot>(<#list rough.output.channels as o>s${o?counter}<#sep>,</#list>)"
      by(simp add: s_def)
    show ?thesis
      apply(subst setter_def)
      apply(subst SB.setter_getch)
      apply(subst buildSB_def)
      apply(subst channelsChan.simps(${chan?counter}))
      using s_def by (metis fst_conv snd_conv)
  qed

</#list>
lemma svalues_getch_subset_sbvalues:
"\<And> c::channels. sValues\<cdot>(out \<^enum> c) \<subseteq> (snd ` sbValues\<cdot>(out))"
  apply(case_tac c)
  proof -
<#list rough.output.channels as chan>
    fix c assume c_def: "c = ${chan.localName}"
    have "Pair ${chan.localName} ` sValues\<cdot>
            ((Rep_cfun (smap <@type.buildSBEConstructor chan.typeSymbol/>))
              (${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>(out))")?split(', ')[chan?index]}))
          \<subseteq> sbValues\<cdot>(out)"
      apply(simp add: getch_to_getter_${chan?counter}[symmetric])
      apply(rule subsetI)
      apply(subst sbValues_def)
      apply(subst Abs_cfun_inverse2)
      using sbvalues_cont apply blast
      apply(subst Union_iff)
      using chdom_in somechannotempty by blast

    thus "sValues\<cdot>(out \<^enum> c) \<subseteq> (snd ` sbValues\<cdot>(out))"
    apply(subst c_def)
    apply(simp add:getch_to_getter_${chan?counter}[symmetric])
    by (metis (mono_tags, lifting) image_subset_iff snd_conv subsetI)
  <#sep>
  next
</#list>
  qed

lemma getter_preserves_no_tick:
  assumes "\<And> m. m \<in> (snd ` sbValues\<cdot>(out)) \<Longrightarrow> #\<^sub>\<surd> m = 0"
    shows "<#list rough.output.channels as chan><#rt>
             <#lt>Tick \<notin> sValues\<cdot><#rt>
             <#lt>(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>out)")?split(', ')[chan?index]})<#rt>
             <#lt><#sep> \<and>
           </#list>"
  apply auto
  proof -
<#list rough.output.channels as chan>
    assume tick: "Tick \<in> sValues\<cdot>(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>out)")?split(', ')[chan?index]})"
    hence "(${type.prefix(chan.typeSymbol.timingSymbol)?split('o ')[0..1]?join('(')}(Tick))) \<in> sValues\<cdot>(out \<^enum> ${chan.localName})"
      apply(subst getch_to_getter_${chan?counter})
      by(simp add: smap_sValues)
    hence "(${type.prefix(chan.typeSymbol.timingSymbol)?split('o ')[0..1]?join('(')}(Tick))) \<in> (snd ` sbValues\<cdot>(out))"
      using svalues_getch_subset_sbvalues by blast
    with assms show False
      by (metis tlen_M.simps(2) tlen_M_timed.simps(1) tlen_event.elims tlent)
  <#sep>
  next
</#list>
  qed

lemma getter_preserves_len_finite:
  assumes "\<And>c. #(out \<^enum> c) < \<infinity>"
    shows "<#list rough.output.channels as chan><#rt>
             <#lt>#(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>out)")?split(', ')[chan?index]}) < \<infinity><#rt>
             <#lt><#sep> \<and>
           </#list>"
  apply(rule conjI)?
<#list rough.output.channels as chan>
  <#if chan?is_last>by<#else>apply</#if>(metis assms getch_to_getter_${chan?counter} slen_smap)
</#list>

lemma no_tick_from_eventgen:
  assumes "da \<in> (behavior.daset <@para.pattern refined/>)"
    shows "<#list rough.output.channels as chan><#rt>
             <#lt>Tick \<notin> sValues\<cdot><#rt>
             <#lt>(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>(snd (multTransitionsInOne da (StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}, foo) (map EventMsg (s2list (eshdts\\<cdot>i))))))", "; ")?split('; ')[chan?index]})<#rt>
             <#lt><#sep> \<and>
           </#list>"
  apply(rule conjI)?
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne <#rt>
         <#lt>da (StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}<#rt>
         <#lt>, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list <#rt>
         <#lt>(eshdts\<cdot>i))" and param="<@para.pattern refined/>"])
  apply(simp_all add:assms)
  apply(subst getter_preserves_no_tick[where out="(snd (multTransitionsInOne da <#rt>
         <#lt>(StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
  apply(simp_all add:assms)?
  apply(subst behavior.mult_da_event_transitions_no_tick[where ls="(s2list <#rt>
         <#lt>(eshdts\<cdot>i))" and param="<@para.pattern refined/>"])?
  by(simp_all add:assms)?

lemma not_inf_from_eventgen:
  assumes "da \<in> (behavior.daset <@para.pattern refined/>)"
    shows "<#list rough.output.channels as chan>#(${tuple.split(rough.output.channels?size, "(${roughOutputFName}.sbgetter\\<cdot>(snd (multTransitionsInOne da (StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}, foo) (map EventMsg (s2list (eshdts\\<cdot>i))))))", "; ")?split('; ')[chan?index]}) < \<infinity><#sep>
    \<and> </#list>"
  apply(rule conjI)?
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne <#rt>
         <#lt>da (StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])
  apply(simp_all add:assms)
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list <#rt>
         <#lt>(eshdts\<cdot>i))" and param="<@para.pattern refined/>"])
  using assms apply blast apply simp+
  apply(subst getter_preserves_len_finite[where out="(snd (multTransitionsInOne <#rt>
         <#lt>da (StateConstr state ${refinedAst.states.stateVariableList?map(v -> v.name)?join(' ')}, foo) (map EventMsg (s2list (eshdts\<cdot>i)))))"])?
  apply(simp_all add:assms)?
  apply(subst behavior.mult_da_event_transitions_not_inf[where ls="(s2list (eshdts\<cdot>i))" and param="<@para.pattern refined/>"])?
  using assms apply blast? by (simp+)?


                                                                                              
                                                                                              
method admissibility_wrapup uses definitions =
  (simp_all add: SetPcpo.less_set_def[symmetric] eventFilter_def eValues_def
      )

strategy SolveSubgoals =
    Ors[
      User <admissibility_wrapup>,
      Repeat(Ors[Fastforce,Hammer])
    ]

                                                                                              
                   
strategy AdmRules = Ors[User <rule adm_imp>, User <rule adm_all>, User <rule adm_imp>,
    User <rule adm_below, User <rule adm_eq, User <rule adm_subst>, User <rule adm_not_below>]

strategy AdmStrat = Thens[Repeat(Ors[AdmRules,Simp]), SolveSubgoals, IsSolved]

<#list 1..rough.predicatesLen as pred>
lemma predicate_${pred?index}_llr:
  assumes "spf \<in> ${refinedName}.Sps <@para.pattern refined/>"
      and "wellformed (${roughInputFName}.sbgetter\<cdot>sb)"
    shows "<#rt>
  <#list 1..rough.assumptionsLen><#t>
    <#items as assm><#t>
      <#lt>assumption_${assm?index} <@para.pattern rough/> <#rt>
      <#lt>(${roughInputFName}.sbgetter\<cdot>sb) (${roughOutputFName}.sbgetter\<cdot>(spf\<cdot>sb))<#rt>
      <#lt><#sep> \<and>
      <#lt>           </#sep><#rt>
    </#items><#t>
    <#lt> \<longrightarrow>
  </#list>
  <#lt>           predicate_${pred?index} <@para.pattern rough/> <#rt>
  <#lt>(${roughInputFName}.sbgetter\<cdot>sb) (${roughOutputFName}.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: ${refinedName}.Sps_def behavior.Sem_def)
  apply(rule bundlemergepred[where SPS="eSem (behavior.eaut <@para.pattern rough/>)"])
  apply(simp)
  <#if rough.assumptionsLen?? && (rough.assumptionsLen?number > 0)>
  apply(simp add:<#list 1..rough.assumptionsLen as assm> assumption_${assm?index}_def</#list> predicate_${pred?index}_def)
  <#else>
  apply(simp add: predicate_${pred?index}_def)
  </#if>
  apply(simp add: case_prod_beta)?
  (* autosledgi *) sorry<#sep>

</#list>


lemma causality_llr:
  assumes "spf \<in> ${refinedName}.Sps <@para.pattern refined/>"
    shows "causality (${roughInputFName}.sbgetter\<cdot>sb) (${roughOutputFName}.sbgetter\<cdot>(spf\<cdot>sb))"
  apply(simp add: causality_def <#if rough.strong>strong<#else>weak</#if>pred_def)
  using assms by(metis<#rt>
<#if refined.parameters?size == 0><#t>
  <#lt> case_unit<#rt>
</#if>
<#if rough.strong><#t>
  <#lt> behavior.sem_strong ${refinedName}.Sps_def strong2pred strongpred_def<#rt>
<#else>
  <#lt> ${refinedName}.Sps_def eventGen.sem_weak weak_def<#rt>
</#if>)

lemma wholePredicate_llr:
  assumes "spf \<in> ${refinedName}.Sps <@para.pattern refined/>"
    shows "wholePredicate <@para.pattern rough/> (${roughInputFName}.sbgetter\<cdot>sb) (${roughOutputFName}.sbgetter\<cdot>(spf\<cdot>sb))"
  using assms apply(simp add: wholePredicate_def)
  by(simp add:<#list 1..rough.predicatesLen as pred> predicate_${pred?index}_llr</#list> causality_llr)

(* General refinement skeleton *)
lemma refinement[simp]: "${refinedName}.Sps <@para.pattern refined/> \<subseteq> ${roughName}.Sps <@para.pattern rough/>"
  by(simp add: ${roughName}.Sps_def subsetI wholePredicate_llr)


end
