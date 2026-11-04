<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Type.ftl" as type>
<#t><#import "../helper/State.ftl" as state>
<#t><#import "../helper/Configuration.ftl" as transition>
<#t><#import "../helper/Channel.ftl" as chan>
<#t><#import "../helper/Datatype.ftl" as datatype>
<#t><#import "../helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"      type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment" type="Boolean" -->
<#t><#-- @ftlvariable name="th"      type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="aut"     type="montibelle.focus._ast.ASTEventAutomaton" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
<#t>${tc.signature("comment", "th", "aut")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) component.EventExecLocale
    (* Gen  *) ${aut.theorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.inputBundleSymbol.codeTheorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.outputBundleSymbol.codeTheorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.inputBundleSymbol.theorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.outputBundleSymbol.theorySymbol.importFrom(aut.codeTheorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


section \<open>Executable automaton\<close>

<#if aut.eventTransitions?has_content || aut.tickTransitionsListCompleted?has_content>
  <#list aut.eventTransitions as channel, transitions>
subsection \<open>Event on ${channel.name}\<close>
    <#list transitions as trans>
      <#assign index = "${channel?index}${trans?index}"><#t>

fun executableExpression_${index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
${typePrinter.print(channel.typeSymbol.symType)} \<Rightarrow> (State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableExpression_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern} = <#rt>
    <#lt>[<@transition.eventResult trans.result/>]"

fun executableTransitionH_${index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
${typePrinter.print(channel.typeSymbol.symType)} \<Rightarrow> (State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableTransitionH_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern} =
    (if (guard_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern}) then (<#rt>
executableExpression_${index} <@para.pattern aut.symbol/> <@state.pattern aut/> ${channel.pattern}<#rt>
) else [])"
    </#list>
  </#list>
  <#list aut.tickTransitionsListCompleted>


subsection \<open>Tick Transitions\<close>

    <#items as trans>
fun executableExpressionT_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableExpressionT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> = <#rt>
    <#lt>[<@transition.eventResult trans.result/>]"

fun executableTransitionTH_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableTransitionTH_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> =
    (if (guardT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/>) then (<#rt>
executableExpressionT_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/><#rt>
) else [])"

    </#items>
  </#list>
</#if>

subsection \<open>Automaton definition\<close>

fun executableEventTransition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
  <#lt>(${aut.inputBundleSymbol.theorySymbol.filename}.channels \<times> msg) \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
<#if aut.eventTransitions?has_content>
  <#list aut.eventTransitions as channel, transitions>
"executableEventTransition para state (${channel.localName}, ${type.constructor(channel.typeSymbol)} ${channel.pattern}) =
    <#list transitions as trans>
    executableTransitionH_${channel?index}${trans?index} para state ${channel.pattern}<#rt>
      <#lt><#sep> @${'\n'}</#sep><#rt>
    </#list>"<#t>
    <#sep><#lt> | ${"\n"}<#rt></#sep><#rt>
  </#list>
  <#if aut.needsCatchAll && false><#---->
    <#if (aut.eventTransitions?size > 0)>
 |
    </#if>
"executableEventTransition _ _ _ = []"
  <#else>

  </#if>
<#else>
"executableEventTransition _ _ _ = []"
</#if>

fun executableTickTransition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableTickTransition para state =
<#if aut.tickTransitionsList?has_content>
  <#list aut.tickTransitionsList as trans>
    executableTransitionTH_${trans?index} para state<#rt>
    <#sep><#lt> @
    </#sep>
  </#list>
<#else>
  <#lt> []<#rt>
</#if>"

definition executableInitialConfigs :: "<@para.type aut.symbol/> \<Rightarrow> <#rt>
  <#lt>(State \<times> (${aut.outputBundleSymbol.theorySymbol.filename}.channels msgWithChan) list) list" where
"executableInitialConfigs  \<equiv> \<lambda> <@para.pattern aut.symbol/> . <#rt>[
<#list aut.initialList as config>
  <#lt><@transition.eventResult config/><#rt>
  <#sep> , </#sep><#t>
</#list><#lt>]"

global_interpretation executableBehavior:
    eventExecGen
      executableEventTransition
      executableTickTransition
      executableInitialConfigs
      <#if aut.isStrongCausal()>True<#else>False</#if>                                                  
      defines execsem = executableBehavior.rndSem
    and laut = executableBehavior.lsaut
    and transition = executableBehavior.transition
    and ndatransition = executableBehavior.ndaTransition
    and eventtransition = executableBehavior.ndaTransition_eventC
    and ticktransition = executableBehavior.ndaTransition_tickC
    and config = executableBehavior.config
    and configC = executableBehavior.ndaInitConfigC
  done


section \<open>Code export\<close>

<#if aut.outputBundleSymbol.channels?has_content>
fun sb2stream::"${aut.outputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega><#rt>
 <#lt> \<Rightarrow> <@datatype.streamTypes aut.outputBundleSymbol/>" where
"sb2stream a = ${aut.outputBundleSymbol.theorySymbol.filename}.sbgetter\<cdot>a"
<#else>
fun sb2stream::"${aut.outputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega> \<Rightarrow> unit" where
"sb2stream a = ()"
</#if>

export_code "execsem" "${aut.inputBundleSymbol.theorySymbol.filename}.sbsetter" "sb2stream" in Scala <#rt>
<#lt>module_name ${aut.theorySymbol.filename}_scalaExec <#rt>
<#lt>file_prefix "${aut.theorySymbol.filename}_scalaExec" (case_insensitive)


end
