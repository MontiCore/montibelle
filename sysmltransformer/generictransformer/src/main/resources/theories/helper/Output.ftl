<#import "Type.ftl" as t>
<#import "Channel.ftl" as c>

<#macro values outputs>
<#---->
<#-- @ftlvariable name="outputs" type="java.util.List<montibelle.focus._ast.ASTOutput>" -->
  <#if outputs?has_content>
    <#list outputs>
      <#lt>(<#rt>
      <#items as out>
        <#if out.isComprehension>
          <#lt>${out.channelSymbol.pattern}<#rt>
        <#else>
          <#lt>${out.value}<#rt>
        </#if>
        <#sep>, </#sep><#t>
      </#items>
      <#lt>)<#rt>
    </#list>
  <#else>
    <#t>()
    </#if><#t>
</#macro>

<#macro eventValues outputs>
<#---->
<#-- @ftlvariable name="outputs" type="java.util.List<montibelle.focus._ast.ASTOutput>" -->
  <#if outputs?has_content>
    <#list outputs>
        <#items as out>
        <#if out.isComprehension>
          <#lt>(${c.constructor(out.channelSymbol)} ${out.channelSymbol.pattern})<#rt>
        <#else>
          <#if out.isListValue>
            <#lt>(map ${c.constructor(out.channelSymbol)} (${out.value}))<#rt>
          <#else>
            <#lt>[(${c.constructor(out.channelSymbol)} (${out.value}))]<#rt>
          </#if>
        </#if>
        <#sep> @ </#sep><#t>
      </#items>
    </#list>
  <#else>
    <#t>[]
    </#if><#t>
</#macro>
