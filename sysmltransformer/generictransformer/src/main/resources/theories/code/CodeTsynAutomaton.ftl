<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Comprehension.ftl" as compr>
<#t><#import "../helper/Datatype.ftl" as datatype>
<#t><#import "../helper/State.ftl" as state>
<#t><#import "../helper/Configuration.ftl" as transition>
<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Import.ftl" as import>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="aut"      type="montibelle.focus._ast.ASTAutomaton" --><#t>
<#t>
<#t>${tc.signature("comment", "th", "aut")}
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) ${aut.theorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.states.theorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.inputBundleSymbol.codeTheorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.outputBundleSymbol.codeTheorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.inputBundleSymbol.theorySymbol.importFrom(aut.codeTheorySymbol)} <#rt>
<#lt>${aut.outputBundleSymbol.theorySymbol.importFrom(aut.codeTheorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin

section \<open>Executable automaton\<close>
<#list aut.transitionList as trans>

(* ${trans.documentation} *)
fun executableExpression_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) list" where
"executableExpression_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.pattern aut.input.symbol/> = [
    <@transition.result configuration=trans.result unlift=true/>${compr.transition(trans)}
]"

fun executableTransitionH_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) list" where
"executableTransitionH_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.pattern aut.input.symbol/> =
(if (guard_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.parameter aut.input.symbol/>) then (<#rt>
executableExpression_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.parameter aut.input.symbol/><#rt>
) else [])"
</#list>

definition executableTransition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) list" where
"executableTransition para state input =<#rt>
    <#if aut.transitionList?size=0>
        <#lt> []<#rt>
    <#else>

        <#list aut.transitionList as trans>
    executableTransitionH_${trans?index} para state input<#rt>
            <#sep><#lt> @
            </#sep>
        </#list>
    </#if>"
    <#if aut.isStrongCausal()>

definition executableInitialConfigs :: "<@para.type aut.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) list" where
"executableInitialConfigs  \<equiv> \<lambda> <@para.pattern aut.symbol/> . <#rt>
        <#if aut.initialList?has_content>
        <#list aut.initialList as config>
            <#lt>[<@transition.result configuration=config unlift=true/>${compr.initial(config)}]<#rt>
            <#sep> @ </#sep><#t>
        </#list>
        <#else> []
        </#if>"
    <#else>

definition executableInitialStates :: "<@para.type aut.symbol/> \<Rightarrow> State list" where
"executableInitialStates \<equiv> \<lambda> <@para.pattern aut.symbol/>. <#rt>
        <#list aut.initialList as config>
            <#lt>[<@state.new state=config.state unlift=true/>${compr.initial(config)}]<#rt>
            <#sep> @ </#sep><#t>
        </#list>"
    </#if>

global_interpretation executableBehavior:
    <#if aut.isStrongCausal()>
    tsExecStrongGen
      executableTransition
      executableInitialConfigs
      ${aut.input.theorySymbol.filename}.buildSBE
      ${aut.output.theorySymbol.filename}.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: ${aut.input.theorySymbol.filename}.SBE.c_empty ${aut.output.theorySymbol.filename}.SBE.c_empty)
    <#else>
    tsExecWeakGen
      executableTransition
      executableInitialStates
      ${aut.input.theorySymbol.filename}.buildSBE
      ${aut.output.theorySymbol.filename}.buildSBE
    defines semExec = executableBehavior.rndSem
  by%visible(unfold_locales; simp_all add: ${aut.input.theorySymbol.filename}.SBE.c_empty ${aut.output.theorySymbol.filename}.SBE.c_empty)
    </#if>

                                                                                         
(* export_code "semExec" in Scala module_name ${aut.name}_scalaExec file_prefix "${aut.name}_scalaExec" (case_insensitive) *)

end
