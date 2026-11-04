<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Datatype.ftl" as datatype>
<#t>
<#t><#-- @ftlvariable name="tc"        type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="c"         type="montibelle.focus._ast.ASTConnectors" -->
<#t>
<#t>${tc.signature("comment", "th", "c")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) sps.SPSFun
    (* Gen  *) ${import.datatype(c.symbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


lift_definition connector :: "<@datatype.streamTypes c.inputBundleSymbol/> \<rightarrow> <@datatype.streamTypes c.outputBundleSymbol/>" is
"\<lambda> <@datatype.pattern c.inputBundleSymbol/>. (<#list c.outputBundleSymbol.channels as out>${c.map?api.get(out).pattern}<#sep>, </#list>)"
  by(intro cont2cont)

definition Sps :: "<@para.type c.symbol/> \<Rightarrow> <#rt>
(${c.inputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega> \<rightarrow> ${c.outputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern c.symbol/>. { ${c.outputBundleSymbol.theorySymbol.filename}.SB.setter oo connector oo ${c.inputBundleSymbol.theorySymbol.filename}.SB.getter }"


end
