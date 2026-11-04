<#t><#import "Channel.ftl" as channel>
<#t><#import "Parameter.ftl" as para>
<#t><#import "Datatype.ftl" as datatype>

<#function inputType comp>
<#-- @ftlvariable name="comp" type="montibelle.focus._symboltable.CompositionSymbol" -->
  <#local res = "(">
  <#list comp.allSpses as inst>
    <#if !inst?is_last>
      <#local res += "(" + inst.input.theorySymbol.filename + ".channels \\<union> ">
    <#else>
      <#local res += inst.input.theorySymbol.filename + ".channels)">
      <#break >
    </#if>
  </#list>
  <#if comp.allSpses?size gt 1>
    <#list comp.allSpses?size-2..0 as stoppingIndex>
      <#local res += " - ">
      <#list comp.allSpses as inst>
        <#if stoppingIndex <= inst?index>
          <#local res += inst.output.theorySymbol.filename + ".channels">
          <#if inst?index == comp.allSpses?size-1>
            <#local res += ")">
          <#else>
            <#local res += " \\<union> ">
          </#if>
        </#if>
      </#list>
    </#list>
  </#if>
  <#return res>
</#function>

<#function outputType comp>
<#-- @ftlvariable name="comp" type="montibelle.focus._symboltable.CompositionSymbol" -->
  <#local res = "">
  <#list comp.allSpses as inst>
    <#if inst?is_first>
      <#local res += "(">
    </#if>
    <#local res += inst.output.theorySymbol.filename + ".channels">
    <#if !inst?is_last>
      <#local res += " \\<union> ">
    <#else>
      <#local res += ")">
    </#if>
  </#list>
  <#return res>
</#function>
