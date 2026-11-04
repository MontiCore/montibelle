<#t>
<#t><#-- @ftlvariable name="sessions" type="java.util.List<montibelle.transformer.generic.sessions.ISession>" -->
<#t>
<#t>${tc.signature("sessions")}
<#t>
<#list sessions as session>
  <#if session.chapter?has_content>
chapter ${session.chapter}

  </#if>
session "${session.name}"<#rt>
  <#if session.groups?has_content>
    <#lt> (<#rt>
    <#list session.groups as group>
      ${group}<#t>
      <#sep> </#sep><#t>
    </#list><#t>
    )<#t>
  </#if>
  <#if session.dir?has_content>
    <#lt> in "${session.dir}"<#rt>
  </#if>
  <#lt> = <#if session.parent?has_content>"${session.parent}" +</#if>
  <#if session.description?has_content>
    description {*
      ${session.description}
    *}
  </#if>
  <#if session.options?has_content>
    options [<#rt>
    <#list session.options as option>
      ${option.name}<#t>
      <#if option.value?has_content>
        =${option.value}<#t>
      </#if>
      <#sep>,</#sep><#t>
    </#list>
    <#lt>]
  </#if>
  <#if session.importSessions?has_content>
    sessions<#list session.importSessions as session> "${session}"</#list>
  </#if>
  <#if session.theories?has_content>
    <#list session.theories as theory>
    theories<#rt>
      <#if theory.options?has_content>
        <#lt> [<#rt>
        <#list theory.options as option>
          ${option.name}<#t>
          <#if option.value?has_content>
            =${option.value}<#t>
          </#if>
          <#sep>,</#sep><#t>
        </#list>
        <#lt>]
      <#else>
      <#---->

      </#if>
      <#list theory.theoryEntries as entry>
        <#if entry.name?contains("/")>
        "${entry.name}"<#if entry.global> (global)</#if>
        <#else>
        ${entry.name}<#if entry.global> (global)</#if>
        </#if>
      </#list>
    </#list>
  </#if>
  <#if session.documentFiles?has_content>
    <#list session.documentFiles as files>
    document_files<#if files.base_dir?has_content> ("${files.base_dir}")</#if>
      <#list files.files as f>
        "${f}"
      </#list>
    </#list>
  </#if>
  <#if session.exportFiles?has_content>
    <#list session.exportFiles as files>
    export_files<#if files.target_dir?has_content> (in "${files.target_dir}")</#if><#if files.prune?has_content> [${files.prune}]</#if>
      <#list files.patterns as p>
        "${p}"
      </#list>
    </#list>
  </#if>

</#list>
