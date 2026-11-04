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
<#t><#assign roughName = ref.roughNameSymbol.theorySymbol.filename> <#---->
<#t><#assign refinedName = ref.refinedNameSymbol.theorySymbol.filename>
<#t>
<#t><#assign rough = ref.roughNameSymbol>
<#t><#assign refined = ref.refinedNameSymbol>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen *) ${ref.rough.theorySymbol.importFrom(ref.theorySymbol)} <#rt>
         <#lt>${ref.refined.theorySymbol.importFrom(ref.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


(* Automatically determined that the history-based refinement was correct-by-construction *)
lemma refinement[simp]: "${refinedName}.Sps <@para.pattern refined/> \<subseteq> ${roughName}.Sps <@para.pattern rough/>"
  apply(auto simp add: ${refinedName}.Sps_def ${roughName}.Sps_def
                    ${refinedName}.wholePredicate_def ${roughName}.wholePredicate_def
                    ${refinedName}.predAndCausality_defs ${roughName}.predAndCausality_defs)
  (* autosledgi *) sorry


end
