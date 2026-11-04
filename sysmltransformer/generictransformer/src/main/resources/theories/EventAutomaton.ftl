<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Comprehension.ftl" as compr>
<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/State.ftl" as state>
<#t><#import "helper/Configuration.ftl" as transition>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="aut"      type="montibelle.focus._ast.ASTEventAutomaton" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
<#t>
<#t>${tc.signature("comment", "th", "aut")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) eventcomponent.EventLocale
    (* Gen  *) ${import.datatype(aut.symbol)} ${aut.states.theorySymbol.importFrom(aut.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


<#if aut.eventTransitions?has_content || aut.tickTransitionsListCompleted?has_content>
section \<open>Helper-Function for each transition to allow transition overlap\<close>
  <#list aut.eventTransitions as channel, transitions>

subsection \<open>Event on ${channel.name}\<close>
    <#list transitions as trans>
      <#assign index = "${channel?index}${trans?index}"><#t>

(* ${trans.documentation} *)
fun guard_${index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> ${typePrinter.print(channel.typeSymbol.symType)} \<Rightarrow> bool" where
"guard_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern} = (s = Substate.${trans.start} \<and> (${trans.guard}))"

fun expression_${index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
${typePrinter.print(channel.typeSymbol.symType)} \<Rightarrow> (State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"expression_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern} = {
    <@transition.eventResult trans.result/>${compr.transition(trans)}
}"

fun transitionH_${index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
${typePrinter.print(channel.typeSymbol.symType)} \<Rightarrow> (State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"transitionH_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern} =
    (if (guard_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern}) then (<#rt>
expression_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern}<#rt>
) else {})"
    </#list>
  </#list>
  <#list aut.tickTransitionsListCompleted>


subsection \<open>Tick Transitions\<close>
    <#items as trans>

(* ${trans.documentation} *)
fun guardT_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> bool" where
"guardT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> = (s = Substate.${trans.start} \<and> (${trans.guard}))"

fun expressionT_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"expressionT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> = {
    <@transition.eventResult trans.result/>${compr.transition(trans)}
}"

fun transitionTH_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"transitionTH_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> =
    (if (guardT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/>) then (<#rt>
expressionT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/><#rt>
) else {})"
    </#items>
  </#list>
</#if>


section \<open>Automaton definition\<close>

fun eventTransition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
  <#lt>(${aut.inputBundleSymbol.theorySymbol.filename}.channels \<times> msg) \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
<#if aut.eventTransitions?has_content>
  <#list aut.eventTransitions as channel, transitions>
"eventTransition para state (${channel.localName}, ${type.constructor(channel.typeSymbol)} ${channel.pattern}) =
    <#list transitions as trans>
    transitionH_${channel?index}${trans?index} para state ${channel.pattern}<#rt>
      <#lt><#sep> \<union>${'\n'}</#sep><#rt>
    </#list>"<#t>
    <#sep><#lt> | ${"\n"}<#rt></#sep><#rt>
  </#list>
  <#if aut.needsCatchAll>
    <#if (aut.eventTransitions?size > 0)>
 |
    </#if>
"eventTransition _ _ _ = {}"
  <#else>

  </#if>
<#else>
"eventTransition _ _ _ = {}"
</#if>

fun tickTransition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"tickTransition para state =
<#if aut.tickTransitionsListCompleted?has_content>
  <#list aut.tickTransitionsListCompleted as trans>
    transitionTH_${trans?index} para state<#rt>
    <#sep><#lt> \<union>
    </#sep>
  </#list>
<#else>
  <#lt> {}<#rt>
</#if>"

definition initialConfigs :: "<@para.type aut.symbol/> \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) set" where
"initialConfigs  \<equiv> \<lambda> <@para.pattern aut.symbol/> . <#rt>{
<#list aut.initialList as config>
  <#lt><@transition.eventResult config/>${compr.initial(config)}<#rt>
  <#sep>} \<union> {</#sep><#t>
</#list><#lt>}"

interpretation behavior:
    eventGen
      eventTransition
      tickTransition
      initialConfigs
      <#if aut.isStrongCausal()>True<#else>False</#if>                                                  
  apply(unfold_locales)
  done

                        
ML \<open>structure ${aut.theorySymbol.filename} = struct
<#list aut.eventTransitions as channel, transitions>
  val ${channel.name}_transitionList = [
  <#list transitions as trans>
    <#assign index = "${channel?index}${trans?index}"><#t>
    ("${trans.documentation}", @{term guard_${index}}, @{term expression_${index}}, @{term transitionH_${index}})<#sep>,
  </#list>
  <#lt>]
  val tick_transitionList = [
  <#list aut.tickTransitionsListCompleted as trans>
    ("${trans.documentation}", @{term guardT_${trans?index}}, @{term expressionT_${trans?index}}, @{term transitionTH_${trans?index}})<#sep>,
  </#list>
  <#lt>]
</#list>
end\<close>

definition Sps :: "<@para.type aut.symbol/> \<Rightarrow> <#rt>
(${aut.inputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega> \<rightarrow> ${aut.outputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern aut.symbol/>. behavior.Sem <@para.pattern aut.symbol/>"


end
