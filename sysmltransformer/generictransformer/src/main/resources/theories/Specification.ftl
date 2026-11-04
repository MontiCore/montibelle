<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Datatype.ftl" as datatype>
<#t>
<#t><#-- @ftlvariable name="tc"         type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="spec"       type="montibelle.focus._ast.ASTSpecification" -->
<#t>
<#t>${tc.signature("comment", "th", "spec")}
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) sps.SPSComp<#if spec.inputBundleSymbol.timing.eventBased> stream.EventStream</#if>
    (* Gen  *) ${import.datatype(spec.symbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


<#list spec.assumptions as ass>
definition assumption_${ass?index} :: "<@para.type spec.symbol/> \<Rightarrow> <@datatype.streamTypes spec.inputBundleSymbol/> <#rt>
\<Rightarrow> <@datatype.streamTypes spec.outputBundleSymbol/> \<Rightarrow> bool" where
"assumption_${ass?index} \<equiv> \<lambda> <@para.pattern spec.symbol/> <@datatype.pattern spec.inputBundleSymbol/> <@datatype.pattern spec.outputBundleSymbol/> .
    (${ass})"

</#list>
<#list spec.predicates as pred>
definition predicate_${pred?index} :: "<@para.type spec.symbol/> \<Rightarrow> <@datatype.streamTypes spec.inputBundleSymbol/> <#rt>
\<Rightarrow> <@datatype.streamTypes spec.outputBundleSymbol/> \<Rightarrow> bool" where
"predicate_${pred?index} \<equiv> \<lambda> <@para.pattern spec.symbol/> <@datatype.pattern spec.inputBundleSymbol/> <@datatype.pattern spec.outputBundleSymbol/> .
    <@datatype.letPattern spec.inputBundleSymbol/><@datatype.letPattern spec.outputBundleSymbol/>(${pred})"

</#list>
definition causality :: "<@datatype.streamTypes spec.inputBundleSymbol/> \<Rightarrow> <@datatype.streamTypes spec.outputBundleSymbol/> \<Rightarrow> bool" where
"causality \<equiv> \<lambda> <@datatype.pattern spec.inputBundleSymbol/> <@datatype.pattern spec.outputBundleSymbol/> .
    <#if spec.isStrongCausal()>strongpred<#else>weakpred</#if> <@datatype.pattern spec.inputBundleSymbol/> <@datatype.pattern spec.outputBundleSymbol/>"

text \<open>Bundle all constraints of the component for refinement relations\<close>
lemmas predAndCausality_defs = <#list spec.predicates as pred>predicate_${pred?index}_def </#list>causality_def

definition wholePredicate :: "<@para.type spec.symbol/> \<Rightarrow> <@datatype.streamTypes spec.inputBundleSymbol/> <#rt>
\<Rightarrow> <@datatype.streamTypes spec.outputBundleSymbol/> \<Rightarrow> bool" where
"wholePredicate para input output = (
  ((wellformed input<#list spec.assumptions as ass>\<and> assumption_${ass?index} para input output</#list>)
      <#if spec.predicates?has_content>\<longrightarrow> (<#list spec.predicates as pred>predicate_${pred?index} para input output<#sep> \<and> </#list>)<#else>\<longrightarrow> True</#if>)
  \<and> (causality input output))"

definition Sps :: "<@para.type spec.symbol/> \<Rightarrow> <#rt>
(${spec.inputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega> \<rightarrow> ${spec.outputBundleSymbol.theorySymbol.filename}.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern spec.symbol/>. {spf | spf. \<forall>sb.
wholePredicate <@para.pattern spec.symbol/> (${spec.inputBundleSymbol.theorySymbol.filename}.SB.getter\<cdot>sb) (${spec.outputBundleSymbol.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>sb))}"


end
