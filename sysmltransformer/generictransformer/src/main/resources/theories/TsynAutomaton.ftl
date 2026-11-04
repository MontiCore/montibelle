<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Comprehension.ftl" as compr>
<#t><#import "helper/Datatype.ftl" as datatype>
<#t><#import "helper/State.ftl" as state>
<#t><#import "helper/Configuration.ftl" as transition>
<#t>
<#t><#-- @ftlvariable name="tc"      type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment" type="Boolean" -->
<#t><#-- @ftlvariable name="th"      type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="aut"     type="montibelle.focus._ast.ASTAutomaton" -->
<#t>
<#t>${tc.signature("comment", "th", "aut")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) tscomponent.TsLocale tscomponent.TsExecLocale expressions.TSynExpressions
    (* Gen  *) ${import.datatype(aut.symbol)} ${aut.states.theorySymbol.importFrom(aut.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin

                                                             
fun liftedPair :: "('a::type tsyn \<times> 'b::type tsyn) \<Rightarrow> ('a \<times> 'b) tsyn" where
"liftedPair (TSynMsg a, TSynMsg b) = TSynMsg (a, b)" |
"liftedPair _                      = Eps"

                                                             
fun liftedList :: "'a::type tsyn list \<Rightarrow> 'a list tsyn" where
"liftedList []                = TSynMsg []" |
"liftedList (Eps # _)         = Eps" |
"liftedList (TSynMsg a # as)  = liftedApplyTwo Cons (TSynMsg a) (liftedList as)"

<#if aut.transitionList?size !=0>
section \<open>Helper-Function for each transition to allow transition overlap\<close>
<#list aut.transitionList as trans>

(* ${trans.documentation} *)
fun guard_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <@datatype.types aut.input.symbol/> \<Rightarrow> bool" where
"guard_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.pattern aut.input.symbol/> = (s = Substate.${trans.start} \<and> (${trans.guard}))"

fun expression_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) set" where
"expression_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.pattern aut.input.symbol/> = {
    <@transition.result configuration=trans.result unlift=true/>${compr.transition(trans)}
}"

fun transitionH_${trans?index} :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) set" where
"transitionH_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.pattern aut.input.symbol/> =
(if (guard_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.parameter aut.input.symbol/>) then (<#rt>
expression_${trans?index} <@para.pattern aut.symbol/> <@state.pattern aut/> <@datatype.parameter aut.input.symbol/><#rt>
) else {})"
</#list>


</#if>
section \<open>Automaton definition\<close>

definition transition :: "<@para.type aut.symbol/> \<Rightarrow> State \<Rightarrow> <#rt>
<@datatype.types aut.input.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) set" where
"transition para state input =<#rt>
<#if aut.transitionList?size=0>
  <#lt> {}<#rt>
<#else>

    <#list aut.transitionList as trans>
    transitionH_${trans?index} para state input<#rt>
    <#sep><#lt> \<union>
    </#sep>
    </#list>
</#if>"
<#if aut.isStrongCausal()>

definition initialConfigs :: "<@para.type aut.symbol/> \<Rightarrow> (State \<times> <@datatype.types aut.output.symbol/>) set" where
"initialConfigs  \<equiv> \<lambda> <@para.pattern aut.symbol/> . <#rt>
    <#if aut.initialList?has_content>
    <#list aut.initialList as config>
        <#lt>{<@transition.result configuration=config unlift=true/>${compr.initial(config)}}<#rt>
        <#sep> \<union> </#sep><#t>
    </#list>"
    <#else> {}"
    </#if>
<#else>

definition initialStates :: "<@para.type aut.symbol/> \<Rightarrow> State set" where
"initialStates \<equiv> \<lambda> <@para.pattern aut.symbol/>. <#rt>
    <#list aut.initialList as config>
        <#lt>{<@state.new state=config.state unlift=true/>${compr.initial(config)}}<#rt>
        <#sep> \<union> </#sep><#t>
    </#list>"
</#if>

interpretation behavior:
<#if aut.isStrongCausal()>
    tsStrongGen
      transition
      initialConfigs
      ${aut.input.theorySymbol.filename}.buildSBE
      ${aut.output.theorySymbol.filename}.buildSBE
  by%visible(unfold_locales; simp_all add: ${aut.input.theorySymbol.filename}.SBE.c_empty ${aut.output.theorySymbol.filename}.SBE.c_empty)
<#else>
    tsWeakGen
      transition
      initialStates
      ${aut.input.theorySymbol.filename}.buildSBE
      ${aut.output.theorySymbol.filename}.buildSBE
  by%visible(unfold_locales; simp_all add: ${aut.input.theorySymbol.filename}.SBE.c_empty ${aut.output.theorySymbol.filename}.SBE.c_empty)
</#if>

                        
ML \<open>structure ${aut.theorySymbol.filename} = struct
  val transitionList  = [
<#list aut.transitionList as trans>
    ("${trans.documentation}", @{term guard_${trans?index}}, @{term expression_${trans?index}}, @{term transitionH_${trans?index}})<#sep>,
</#list>]
end\<close>

definition Sps :: "<@para.type aut.symbol/> \<Rightarrow> <#rt>
(${aut.input.theorySymbol.filename}.channels\<^sup>\<Omega> \<rightarrow> ${aut.output.theorySymbol.filename}.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern aut.symbol/>. behavior.Sem <@para.pattern aut.symbol/>"

end
