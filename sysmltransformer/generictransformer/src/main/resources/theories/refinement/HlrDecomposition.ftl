 <#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Datatype.ftl" as sb>
<#t>
<#t><#-- @ftlvariable name="tc"      type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment" type="Boolean" -->
<#t><#-- @ftlvariable name="th"      type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"     type="montibelle.focus._ast.ASTRefinement" -->
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#-- @ftlvariable name="rough"   type="montibelle.focus._symboltable.SpecificationSymbol" -->
<#t><#-- @ftlvariable name="refined" type="montibelle.focus._symboltable.CompositionSymbol" -->
<#t><#assign rough = ref.rough>
<#t><#assign refined = ref.refined>
<#t><#assign roughName = ref.rough.theorySymbol.filename>
<#t><#assign refinedName = refined.theorySymbol.filename>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Gen  *) ${ref.rough.theorySymbol.importFrom(ref.theorySymbol)} ${refined.theorySymbol.importFrom(ref.theorySymbol)}
               <#list refined.parts as inst>${inst.theorySymbol.importFrom(ref.theorySymbol)} </#list>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


section \<open>Refinement\<close>

text \<open>Assume that the constraints for all parts of the refined component are met.
      Attempt to show that each constraint of the rough component is met as a result.\<close>

<#list 0..<rough.predicatesLen as i>
lemma pred_${i}:
  <#list refined.parts as inst>
  assumes "${inst.sps.theorySymbol.filename}.wholePredicate <@para.value inst/> <#rt>
    <#if inst.input.channels?has_content>
      <#lt> (${inst.inputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.input/>)<#rt>
    <#else>
      <#lt><@sb.parameter inst.input/><#rt>
    </#if>
    <#if inst.output.channels?has_content>
      <#lt> (${inst.outputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.output/>)<#rt>
    <#else>
      <#lt><@sb.parameter inst.output/><#rt>
    </#if>"
  </#list>
      and "wellformed <@sb.pattern ref.rough.input/>"
  <#list 0..<rough.assumptionsLen as i>
      and "${roughName}.assumption_${i} <@para.pattern ref.rough/> <@sb.pattern ref.rough.input/> <@sb.pattern ref.rough.output/>"
  </#list>
<#list refined.connectors.channelMappings as output>
      and "${output.keyChannel.pattern} = ${output.valueChannel.pattern}"
  </#list>
    shows "${roughName}.predicate_${i} <@para.pattern ref.rough/> <@sb.pattern ref.rough.input/> <@sb.pattern ref.rough.output/>"
  apply(insert assms(1-${refined.parts?size+1+rough.assumptionsLen}), <#rt>
  <#lt>simp add: assms(${refined.parts?size+1+rough.assumptionsLen+1}-${refined.parts?size+1+rough.assumptionsLen+refined.connectors.channelMappings?size}))
  apply(simp add:<#list refined.parts as inst> ${inst.sps.theorySymbol.filename}.wholePredicate_def</#list><#rt>
  <#lt> ${roughName}.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add:<#list refined.parts as part> ${part.inputMap.theorySymbol.filename}.connector.rep_eq ${part.outputMap.theorySymbol.filename}.connector.rep_eq</#list>)?
  <#lt>  (* ${rough.name} assumptions, predicates, causality *)
  <#lt>  apply(simp add:<#if (rough.assumptionsLen > 0)><#list 0..<rough.assumptionsLen as i> ${roughName}.assumption_${i}_def</#list></#if><#if (rough.predicatesLen > 0)><#list 0..<rough.predicatesLen as i> ${roughName}.predicate_${i}_def</#list></#if> ${roughName}.causality_def)?
  <#list refined.parts as inst>
  <#lt>  (* ${inst.sps.name} assumptions, predicates, causality *)
  <#lt>  apply(simp add:<#if (inst.sps.assumptionsLen > 0)><#list 0..<inst.sps.assumptionsLen as i> ${inst.sps.theorySymbol.filename}.assumption_${i}_def</#list></#if><#if (inst.sps.predicatesLen > 0)><#list 0..<inst.sps.predicatesLen as i> ${inst.sps.theorySymbol.filename}.predicate_${i}_def</#list></#if> ${inst.sps.theorySymbol.filename}.causality_def)?
  </#list>
                              
  apply(simp add: weakpred_def strongpred_def wellformed_stream_def tlen_prod_def)?
  apply(simp add: len_stream_def[symmetric])?
  (* autosledgi *) sorry

</#list>
lemma causality:
<#list refined.parts as inst>
  assumes "${inst.sps.theorySymbol.filename}.causality <#rt>
  <#if inst.input.channels?has_content>
    <#lt> (${inst.inputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.input/>)<#rt>
  <#else>
    <#lt><@sb.parameter inst.input/><#rt>
  </#if>
  <#if inst.output.channels?has_content>
    <#lt> (${inst.outputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.output/>)<#rt>
  <#else>
    <#lt><@sb.parameter inst.output/><#rt>
  </#if>"
</#list>
<#list refined.connectors.channelMappings as output>
      and "${output.keyChannel.pattern} = ${output.valueChannel.pattern}"
</#list>
    shows "${roughName}.causality <@sb.pattern ref.rough.input/> <@sb.pattern ref.rough.output/>"
  apply(insert assms)
  apply(simp add:<#list refined.parts as inst> ${inst.sps.theorySymbol.filename}.wholePredicate_def ${inst.sps.theorySymbol.filename}.causality_def</#list>
                  ${roughName}.predAndCausality_defs Let_def case_prod_unfold)
  apply(simp add:<#list refined.parts as part> ${part.inputMap.theorySymbol.filename}.connector.rep_eq ${part.outputMap.theorySymbol.filename}.connector.rep_eq</#list>)?
  apply(simp add: ${roughName}.causality_def strongpred_def weakpred_def tlen_prod_def)?
  apply(rule conjI)?
  (* autosledgi *) sorry

lemma pred_whole:
<#list refined.parts as inst>
  assumes "${inst.sps.theorySymbol.filename}.wholePredicate <@para.value inst/> <#rt>
  <#if inst.input.channels?has_content>
    <#lt>(${inst.inputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.input/>) <#rt>
  <#else>
    <#lt><@sb.parameter inst.input/> <#rt>
  </#if>
  <#if inst.output.channels?has_content>
    <#lt> (${inst.outputMap.theorySymbol.filename}.connector\<cdot><@sb.parameter inst.output/>)<#rt>
  <#else>
    <#lt><@sb.parameter inst.output/><#rt>
  </#if>"
</#list>
<#list refined.connectors.channelMappings as output>
      and "${output.keyChannel.pattern} = ${output.valueChannel.pattern}"
</#list>
    shows "${roughName}.wholePredicate <@para.pattern ref.rough/><#rt>
  <#lt> <@sb.pattern ref.rough.input/> <@sb.pattern ref.rough.output/>"
  apply(simp add: ${roughName}.wholePredicate_def)
  using assms causality
  <#list refined.parts as inst>
    ${inst.sps.theorySymbol.filename}.wholePredicate_def
  </#list>
  <#list 0..<ref.rough.predicatesLen as i>pred_${i} </#list>by auto

                                                       
lemma pred_whole2:
<#list refined.parts as inst>
  assumes "${inst.sps.theorySymbol.filename}.wholePredicate <@para.value inst/> <#rt>
  <#assign input = "(${refined.theorySymbol.filename}_rawinput2${inst.simpleName} input)">
  <#lt><#if inst.input.channels?has_content>(${inst.inputMap.theorySymbol.filename}.connector\<cdot>${input})<#else>${input}</#if><#rt>
  <#assign output = "(${refined.theorySymbol.filename}_rawoutput2${inst.simpleName} output)">
  <#lt><#if inst.output.channels?has_content>(${inst.outputMap.theorySymbol.filename}.connector\<cdot>${output})<#else>${output}</#if>"
</#list>
  assumes "${refined.connectors.theorySymbol.filename}.connector\<cdot>(<#rt>
<#lt>${refined.theorySymbol.filename}_rawinput2${refined.connectors.name} input) = <#rt>
<#lt>${refined.theorySymbol.filename}_rawoutput2${refined.connectors.name} output"
  assumes "rawinput2${refined.theorySymbol.filename?lower_case}_feedback input = rawoutput2${refined.theorySymbol.filename?lower_case}_feedback output"
    shows "${roughName}.wholePredicate <@para.pattern ref.rough/><#rt>
  <#lt> (rawinput2${refinedName?lower_case} input) (rawoutput2${refinedName?lower_case} output)"
  apply(rule rawinput2${refinedName?lower_case}.cases[of "input"],
        rule rawoutput2${refinedName?lower_case}.cases[of "output"], simp)
  apply(rule pred_whole)
  using assms apply (auto simp add: ${refined.connectors.theorySymbol.filename}.connector.rep_eq)
  done

                                                                                              
                                                                                                    
lemma raw_input_eq:
  assumes "spf\<in>(${refinedName}.rawSps <@para.pattern refined/>)"
    shows "((sb)\<star>::${ref.rough.input.theorySymbol.filename}.channels\<^sup>\<Omega>)
         = ((sb \<uplus>\<^sub>\<star> spf\<cdot>sb)::(<#rt>
  <#list refined.allSpses as inst>
    <#lt>${inst.input.theorySymbol.filename}.channels<#rt>
    <#lt><#sep>${"\n"}                           \<union></#sep><#rt>
  </#list><#t>
  <#lt>)\<^sup>\<Omega>)\<star>"
  by(simp add: sb_star21)

                                                             
lemma raw_pred_whole:
  assumes "spf\<in>(${refinedName}.rawSps <@para.pattern refined/>)"
    shows "${roughName}.wholePredicate <@para.pattern ref.rough/>
             (${ref.rough.input.theorySymbol.filename}.SB.getter\<cdot>(sb\<star>))
             (${ref.rough.output.theorySymbol.filename}.SB.getter\<cdot>((spf\<cdot>(sb))\<star>))"
  apply(subst raw_input_eq[OF assms(1)])
  apply(simp add: ${ref.rough.input.theorySymbol.filename}.sbgetter_def ${ref.rough.output.theorySymbol.filename}.sbgetter_def
                  ${refined.theorySymbol.filename}_input_Sub.getter_sub_eq ${refined.theorySymbol.filename}_output_Sub.getter_sub_eq)
  apply(rule pred_whole2)
<#list refined.parts as inst>
  (* Durch ${inst.simpleName} Assumption ziehen *)
  apply(simp only: ${inst.simpleName}_input_Sub.getter_sub_eq[symmetric] ${inst.simpleName}_output_Sub.getter_sub_eq[symmetric])
  apply(simp add: ${inst.inputMap.theorySymbol.filename}.connector.rep_eq ${inst.outputMap.theorySymbol.filename}.connector.rep_eq)
  apply(subst ${inst.input.theorySymbol.filename}.getter_fold,
        subst ${inst.output.theorySymbol.filename}.getter_fold,
        subst sb_star21, simp)
  apply(rule ${inst.simpleName}_pred_general[OF assms(1)])
  apply(simp add: ${inst.sps.theorySymbol.filename}.Sps_def)
</#list>
                              
  apply(simp only: ${refined.connectors.name}_input_Sub.getter_sub_eq[symmetric]
                   ${refined.connectors.name}_output_Sub.getter_sub_eq[symmetric])
  apply(subst ${refined.connectors.input.theorySymbol.filename}.getter_fold,
        subst ${refined.connectors.output.theorySymbol.filename}.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst connector_apply_eq, simp, simp)
  (* Durch ${refined.feedback.simpleName} ziehen *)
  apply(simp only: feedback_input_sub.getter_sub_eq[symmetric]
                   feedback_output_sub.getter_sub_eq[symmetric])
  apply(subst ${refined.feedback.theorySymbol.filename}.getter_fold,
        subst ${refined.feedback.theorySymbol.filename}.getter_fold,
        subst sb_star21, simp)
  using assms(1) apply(subst feedback_getter_eq, simp, simp)
  done

                                                                                                    
lemma comp_pred_whole:
  assumes "spf\<in>(${refinedName}.Sps <@para.pattern refined/>)"
    shows "${roughName}.wholePredicate <@para.pattern ref.rough/>
             (${ref.rough.input.theorySymbol.filename}.SB.getter\<cdot>sb)
             (${ref.rough.output.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>(sb)))"
  apply(rule spsconvert_predicate)
  using assms apply(simp add: ${refinedName}.Sps_def)
  using raw_pred_whole apply blast
  by auto

lemma refinement[simp]: "${refinedName}.Sps <@para.pattern refined/> \<subseteq> <#rt>
${roughName}.Sps <@para.pattern ref.rough/>"
  by(simp add: subsetI ${roughName}.Sps_def comp_pred_whole)


end
