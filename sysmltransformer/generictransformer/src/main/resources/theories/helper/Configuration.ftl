<#import "State.ftl" as state>
<#import "Output.ftl" as output>

<#macro result configuration unlift=false>
<#---->
<#-- @ftlvariable name="configuration"  type="montibelle.focus._ast.ASTConfiguration" -->
    <#t>(
    <#lt><@state.new configuration.state unlift=unlift/>, <#rt>
    <#lt><@output.values configuration.outputList/><#rt>
    <#t>)
</#macro>

<#macro eventResult configuration>
<#---->
<#-- @ftlvariable name="configuration"  type="montibelle.focus._ast.ASTConfiguration" -->
    <#t>(
    <#lt><@state.new configuration.state/>, <#rt>
    <#lt><@output.eventValues configuration.outputList/><#rt>
    <#t>)
</#macro>
