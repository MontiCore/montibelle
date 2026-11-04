<#macro pattern aut>
<#---->
<#-- @ftlvariable name="aut"       type="montibelle.focus._ast.ASTAutomaton"-->
<#-- @ftlvariable name="state"     type="String"-->
  <#lt>(StateConstr s<#rt>
  <#list aut.states.stateVariableList as var>
    <#lt> ${var.pattern}<#rt>
  </#list>
  <#lt>)<#rt>
</#macro>

<#macro new state unlift=false>
<#---->
<#-- @ftlvariable name="state" type="montibelle.focus._ast.ASTState" -->
  <#t>StateConstr Substate.${state.name}
  <#list state.variableValueList as var>
    <#if var.isComprehension>
      <#lt> ${var.definitionDefinition.pattern}<#rt>
    <#elseif unlift>
      <#lt> ((unlift ${var.value}))<#rt>
    <#else>
      <#lt> (${var.value})<#rt>
    </#if>
  </#list>
</#macro>

<#macro newNoPattern state channels generic=false>
<#---->
<#-- @ftlvariable name="state"    type="montibelle.focus._ast.ASTState"
     @ftlvariable name="channels" type="java.util.List<montibelle.focus._symboltable.ChannelSymbol>"
     @ftlvariable name="generic"  type="Boolean"-->
  <#t>StateConstr <#if generic>state<#else>Substate.${state.name}</#if>
  <#list state.variableValues as var>
    <#if var.isComprehension()>
      <#lt> ${var.variable.pattern}<#rt>
    <#else>
      <#lt> <#assign v = var.value><#list channels as c><#assign v = v?replace(c.pattern, "m${c?counter}")></#list>(${v})<#rt>
    </#if>
  </#list>
</#macro>
