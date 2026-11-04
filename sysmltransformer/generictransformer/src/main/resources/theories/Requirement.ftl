<#t><#import "helper/Macros.ftl" as macro>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="req"       type="montibelle.focus._ast.ASTRequirement" -->
<#t>
<#t>${tc.signature("comment", "th", "req")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
<#assign containsStreamCodegen = req.guarantee?contains("sreachableStates")>
<#if !containsStreamCodegen>
  <#list req.assumptionsList as ass>
    <#if ass?contains("eValues")>
      <#assign containsStreamCodegen = true>
    </#if>
  </#list>
</#if>
  imports
<#if containsStreamCodegen>
    (* Core *) stream.StreamCodegen
</#if>
    (* Gen  *) ${req.subjectSymbol.theorySymbol.importFrom(req.theorySymbol)}
<#compress>
<#---->
<#assign containsExecsem = false>
<#if req.guarantee?contains("execsem")>
  <#assign containsExecsem = true>
</#if>
<#list req.assumptionsList as ass>
  <#if ass?contains("execsem")>
    <#assign containsExecsem = true>
  </#if>
</#list>
</#compress>
<#if containsExecsem><#t>
               ${req.subjectSymbol.theorySymbol.importFrom(req.theorySymbol)
                  ?replace("sps_", "code_")
                  ?replace("def_", "code_")}
</#if><#t>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>
begin

lemma ${req.name}:
  <#list req.assumptionsList as ass>
  assumes "${ass?replace("\\\\", "\\")}"
  </#list>
    shows "${req.guarantee?replace("\\\\", "\\")}"
  <#list req.proofStartHintList as proofStart>
  ${proofStart?replace("\\\\", "\\")}
  </#list>
  (* autosledgi *) oops

end
