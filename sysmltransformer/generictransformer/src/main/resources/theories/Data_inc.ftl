<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="para"     type="montibelle.focus._ast.ASTDataInc" -->
<#t>
<#t>${tc.signature("comment", "th", "para")}
<#t>
<#t><#assign types = para.getChannelTypes()>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) bundle.SB inc.Classes bundlelocale.SBEGen bundlelocale.SBGen
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


default_sort type


section \<open>Helpers for Expression Printing\<close>

                                                     
definition minus_lnat:: "lnat \<Rightarrow> lnat \<Rightarrow> lnat" (infixl "-" 65)  where
"minus_lnat ln1 ln2 \<equiv> if (ln1 = \<infinity>)
                      then (\<infinity>)
                      else if ((ln1 > ln2) \<or> (ln1 = ln2))
                           then Fin ((inv Fin) ln1 - (inv Fin) ln2)
                           else undefined"

                                                                                                                        
                                      
fun removeAll::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"removeAll xs [] = xs" |
"removeAll xs (y#ys) = removeAll (remove1 y xs) ys"

definition symmetricDifference::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"symmetricDifference a b = (a - b) \<union> (b - a)"

                                                                              
definition sFilter2 :: "('a::countable \<Rightarrow> bool) \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"sFilter2 P = sfilter (Collect P)"

definition toneFilter2 :: "('a::countable \<Rightarrow> bool) \<Rightarrow> 'a tone stream \<rightarrow> 'a tone stream" where
"toneFilter2 P = toneFilter (Collect P)"

definition tsynFilter2 :: "('a::countable \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynFilter2 P = tsynFilter (Collect P)"

section \<open>Channel Type Information\<close>

text\<open>General ctype information for simp\<close>
lemma cmsg_empty: "cMsg c = {} \<longleftrightarrow> cType c = TNone"
  by(cases c; case_tac x3;simp)

lemma cempty[simp]: "cEmpty = {c. cType c = TNone}"
  using ctype_empty_iff cEmpty_def cmsg_empty by simp
<#list types as t>

lemma ${t.name}_ran[simp]: <#rt>
  <#if t.timingSymbol.isTimeSyncronous()>
"range (Timed o Tsyn o (map_tsyn) ${type.constructor(t)}) = ctype (CH ${t.name} TTsyn ${type.msgType(t)})"
  apply(auto simp add: ctype_def)
  by (metis tsyn.simps(8) range_eqI)
  <#elseif t.timingSymbol.isStrictlyTimeSyncronous()>
"range (Timed o TOne o ${type.constructor(t)}) = ctype (CH ${t.name} TTOne ${type.msgType(t)})"
  by(auto simp add: ctype_def)
  <#elseif t.timingSymbol.isEventBased()>
"range (Timed o TLive o (map_event) ${type.constructor(t)}) = ctype (CH ${t.name} TTLive ${type.msgType(t)})"
  apply(auto simp add: ctype_def)
  by (metis event.simps(8) rangeI)
  </#if>
</#list>


end
