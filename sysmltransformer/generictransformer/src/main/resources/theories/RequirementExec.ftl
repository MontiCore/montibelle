<#t><#import "helper/Macros.ftl" as macro>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="req"      type="montibelle.focus._ast.ASTRequirement" -->
<#t>
<#t>${tc.signature("comment", "th", "req")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen  *) ${req.subjectSymbol.theorySymbol.importFrom(req.theorySymbol)}
               ${req.subjectSymbol.getCodeTheoryName()} <#---->
               ${req.subjectSymbol.input.theory} <#---->
               ${req.subjectSymbol.output.theory}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>
begin

lemma ${req.name}:
  assumes "${req.subjectSymbol.output.theorySymbol.filename}.sbgetter\<cdot>
             (${req.getSubjectSymbol().getCodeTheorySymbol().getFilename()}.execsem ((), (x, y), z, s)
             (${req.subjectSymbol.input.theorySymbol.filename}.sbsetter\<cdot>${(req.subjectSymbol.input.channels?first.pattern)!})) = ${(req.subjectSymbol.output.channels?first.pattern)!}"
  <#list req.assumptionsList as ass>
  assumes "${ass?replace("\\\\", "\\")}"
  </#list>
    shows "${req.guarantee?replace("\\\\", "\\")}"
  <#list req.proofStartHintList as proofStart>
  ${proofStart?replace("\\\\", "\\")}
  </#list>
  (* autosledgi *) oops

end
