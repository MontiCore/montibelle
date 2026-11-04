<#import "Timing.ftl" as t>
<#import "Tuple.ftl" as tuple>

<#macro comment>
(*
 * DO NOT MODIFY! This file was generated. Consider changing the model itself.
 *
 * Generated on ${.now} by @project.artifactId@ @project.version@
 *)
</#macro>

<#macro seperatorRows index lines = 1>
<#-- @ftlvariable name="index" type="int" -->
<#-- @ftlvariable name="lines" type="int" -->
  <#list 1..lines as x>
    <#if index!=0>

    </#if>
  </#list>
</#macro>

<#macro in_eqLemma index is_last>
<#-- @ftlvariable name="index" type="int" -->
<#-- @ftlvariable name="is_last" type="Boolean" -->
  <#compress>
    <#if (index == 0 )>
      (sb \<uplus>\<^sub>- spf\<cdot>sb)
    <#elseif !is_last>
      ((<@in_eqLemma (index-1), is_last />\<star>\<^sub>2)\<uplus>\<^sub>- ((spf\<cdot>sb)<#list 1..index as x>\<star>\<^sub>2</#list>))
    <#else>
      <@in_eqLemma (index-1), !is_last/>\<star>\<^sub>2
    </#if>
  </#compress>
</#macro>

