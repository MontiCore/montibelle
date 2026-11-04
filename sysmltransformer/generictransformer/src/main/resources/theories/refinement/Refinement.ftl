<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"      type="montibelle.focus._ast.ASTRefinement" -->
<#t>
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#assign roughName = ref.rough.theorySymbol.filename>
<#t><#assign refinedName = ref.refined.theorySymbol.filename>
<#t>
<#t><#assign rough = ref.rough>
<#t><#assign refined = ref.refined>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen *) ${ref.rough.theorySymbol.importFrom(ref.theorySymbol)} ${ref.refined.theorySymbol.importFrom(ref.theorySymbol)}<#rt>
<#lt><#list ref.transitiveRefinements as t> ${t.theorySymbol.importFrom(ref.theorySymbol)}</#list>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


(* General refinement skeleton *)
lemma refinement[simp]: "${refinedName}.Sps <@para.pattern refined/> \<subseteq> ${roughName}.Sps <@para.pattern rough/>"
  (* autosledgi *) oops


end
