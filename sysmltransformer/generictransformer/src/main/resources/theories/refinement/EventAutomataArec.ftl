<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t>
<#t><#-- @ftlvariable name="tc"        type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"   type="Boolean" -->
<#t><#-- @ftlvariable name="th"        type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"       type="montibelle.focus._ast.ASTRefinement" -->
<#t>
<#t><#-- @ftlvariable name="rough" type="montibelle.focus._symboltable.EventAutomatonSymbol" -->
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#assign roughName = ref.rough.theorySymbol.filename>
<#t><#assign refinedName = ref.refined.theorySymbol.filename>
<#t>
<#t><#assign rough = ref.rough>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) automaton.AREC
    (* Gen  *) ${ref.rough.theorySymbol.importFrom(ref.theorySymbol)} <#rt>
<#lt>${ref.refined.theorySymbol.importFrom(ref.theorySymbol)}<#rt>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


<#list rough.eventTransitions as channel, transitions>
ML_val \<open>checkStateRefinement @{context}
  @{term "(\<lambda> p state sbe. <#list transitions as transition>${roughName}.transitionH_${channel?index}${transition?index} p state sbe<#sep> \<union> </#list>)"}
  @{term "paramMap"}
  @{term "stateMap"}
  ${refinedName}.${channel.name}_transitionList \<close>
</#list>
<#list rough.tickTransitions>

ML_val \<open>checkStateRefinement_tick @{context}
  @{term "(\<lambda> p state. <#items as transition>${roughName}.transitionTH_${transition?index} p state<#sep> \<union> </#items>)"}
  @{term "paramMap"}
  @{term "stateMap"}
  ${refinedName}.tick_transitionList \<close>
</#list>


end
