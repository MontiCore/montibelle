<#macro type channels>
<#---->
<#-- @ftlvariable name="channels"  type="java.util.List<montibelle.transformer.generic.meta.bundle.channel.IChannel>" -->
  <#if channels?size==1>
    <#lt><#if channels[0].type.eventBased>event<#else>tsyn</#if>[${scalaType(channels[0].type.name)}]<#rt>
  <#else>
    <#lt>(<#if channels[0].type.eventBased>event<#else>tsyn</#if>[${scalaType(channels[0].type.name)}], <@type channels[1..channels?size-1]/>)<#rt>
  </#if>
</#macro>

<#function scalaType type>
<#---->
<#-- @ftlvariable name="type" type="String" -->
  <#switch type>
    <#case "bool">
      <#return "Boolean">
      <#break>
    <#case "string">
      <#return "List[char]">
      <#break>
    <#default>
    <#return type>
  </#switch>
</#function>
