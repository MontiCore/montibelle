<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="para"     type="montibelle.focus._ast.ASTDatatypes" -->
<#t><#-- @ftlvariable name="constants" type="montibelle.transformer.generic.Constants" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>${tc.signature("comment", "th", "para", "constants")}
<#t>
<#t><#assign types = para.getChannelTypes()>
<#t><#assign functions = para.getSymbol().getFunctionsList()>
<#t><#assign enums = para.enums>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype
<#if enums?has_content || functions?has_content>
    (* Gen  *)<#list enums as enum> ${enum.name}</#list><#list functions as function> ${function}</#list>
</#if>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


default_sort type

<#if para.structs?has_content>

section \<open>User-defined Datatypes\<close>
  <#list para.structs as struct>

datatype ${struct.name} = ${struct.name}Constr <#rt>
    <#lt><#list struct.fields as field>(* ${field.name} = *) "${typePrinter.print(field.symType)}"<#sep> </#list>
    <#assign allCountable = true>
    <#list struct.getFields() as field>
      <#if !constants.isTypeCountable(field.symType)>
        <#assign allCountable = false>
      </#if>
    </#list>

    <#if allCountable>
instance ${struct.name}::countable
by(countable_datatype)
    </#if>
    <#list struct.fields as field>

fun ${struct.name}_get_${field.name} :: "${struct.name} => ${typePrinter.print(field.symType)}" where
"${struct.name}_get_${field.name} (${struct.name}Constr<#list struct.fields as f> ${f.pattern}</#list>) = ${field.pattern}"
    </#list>
  </#list>

</#if>

section \<open>Channel and Message Datatypes\<close>

datatype msgType = <#list types as t>${type.msgType(t)}<#sep> |</#list> | TNone

datatype channel = CH string timeType msgType

datatype msg =
<#list types as t>
  ${type.constructor(t)} "${typePrinter.print(t.symType)}"<#sep> |
</#list>


instance msg :: countable
  by(countable_datatype)

fun cName ::"channel \<Rightarrow> string"where
"cName (CH name _ _ ) = name"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime (CH _ tt _) = tt"

fun cType :: "channel \<Rightarrow> msgType" where
"cType (CH _ _ mt) = mt"

fun cMsgt :: "msgType \<Rightarrow> msg set" where
<#list types as t>
"cMsgt ${type.msgType(t)} = range ${type.constructor(t)}" |
</#list>
"cMsgt TNone = {}"

lemma [simp]:
  assumes "cMsgt x = cMsgt y"
    shows "x = y"
  apply(insert assms)
  by(cases x; cases y; simp; blast+)

fun cMsg :: "channel \<Rightarrow> msg set" where
"cMsg (CH _ _ mt) = cMsgt mt"
<#list types as t>

lemma ${type.constructor(t)}_inj[simp]: "inj ${type.constructor(t)}"
  by (simp add: inj_def)

lemma ${type.constructor(t)}_tsyn_inj[simp]: "inj (map_tsyn ${type.constructor(t)})"
  by (simp add: tsyn.inj_map)
</#list>

theorem cmsgempty_ex:"\<exists>c. cMsg c = {}"
  apply(rule_tac x="(CH _ _ TNone)" in exI)
  by(simp)


end
