<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Import.ftl" as importType>
<#t><#-- @ftlvariable name="tc"         type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"    type="Boolean" -->
<#t><#-- @ftlvariable name="th"         type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="function"   type="montibelle.focus._ast.ASTFocusFunction" -->
<#t><#-- @ftlvariable name="constants"   type="montibelle.transformer.generic.Constants" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>${tc.signature("comment", "th", "function", "constants")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
    (* Gen  *)${importType.datatypeImports(th, function, constants)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin

fun ${function.getName()}:: "<#list function.getParameterList() as p>${typePrinter.print(p.symbol.symType)}<#sep> => </#sep></#list><#if function.getParameterList()?size gt 0> => </#if>${typePrinter.print(function.symbol.symType)}" where
"${function.getName()} <#list function.getParameterList() as p>${p.getName()}<#sep> </#sep></#list> = ${function.getString()}"

end
