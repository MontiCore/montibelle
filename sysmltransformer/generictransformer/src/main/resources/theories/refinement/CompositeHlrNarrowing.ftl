<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"      type="montibelle.focus._ast.ASTRefinement" -->
<#t>
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#-- @ftlvariable name="rough"   type="montibelle.focus._symboltable.CompositionSymbol" -->
<#t><#-- @ftlvariable name="refined" type="montibelle.focus._symboltable.CompositionSymbol" -->
<#t><#assign rough = ref.rough>
<#t><#assign refined = ref.refined>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) generator.ArchRef
    (* Gen  *) ${refined.theorySymbol.importFrom(ref.theorySymbol)} ${rough.theorySymbol.importFrom(ref.theorySymbol)}
<#list ref.subComponentRefinements as subRef>               ${subRef.theorySymbol.importFrom(ref.theorySymbol)}
</#list>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


<#list refined.allSpses as refinedPart>
  <#list rough.allSpses as roughPart>
    <#if refinedPart.simpleName == roughPart.simpleName>
(* ${refinedPart.simpleName} *)

fun ${refinedPart.simpleName}_in :: "${refinedPart.input.theorySymbol.filename}.channels \<Rightarrow> ${roughPart.input.theorySymbol.filename}.channels" where
        <#list refinedPart.input.channels as chanRefined>
          <#list roughPart.input.channels as chanRough>
            <#if chanRefined_index = chanRough_index>
  "${refinedPart.simpleName}_in ${refinedPart.input.theorySymbol.filename}.${chanRefined.localName} = ${roughPart.input.theorySymbol.filename}.${chanRough.localName}"<#sep> |</#sep>
            </#if>
          </#list>
        </#list>

fun ${refinedPart.simpleName}_out :: "${roughPart.output.theorySymbol.filename}.channels \<Rightarrow> ${refinedPart.output.theorySymbol.filename}.channels" where
        <#list roughPart.output.channels as chanRough>
          <#list refinedPart.output.channels as chanRefined>
            <#if chanRough_index = chanRefined_index>
  "${refinedPart.simpleName}_out ${roughPart.output.theorySymbol.filename}.${chanRough.localName} = ${refinedPart.output.theorySymbol.filename}.${chanRefined.localName}"<#sep> |</#sep>
            </#if>
          </#list>
        </#list>

    </#if>
  </#list>
</#list>

(* refinement *)

lemma refinement_withAssms:
<#list refined.parts as refinedPart>
  <#list rough.parts as roughPart>
    <#if refinedPart_index = roughPart_index>
<#if refinedPart_index = 0>assumes <#else>    and </#if>"<#if refinedPart.sps.parameters?has_content>\<And> ${refinedPart.sps.parameters?map(p -> p.name)?join(" ")}. </#if>${refinedPart.sps.theorySymbol.filename}.Sps <@para.pattern refinedPart.sps/> \<subseteq> ${roughPart.sps.theorySymbol.filename}.Sps <@para.pattern roughPart.sps/>"
    </#if>
  </#list>
</#list>
  shows "${refined.theorySymbol.filename}.Sps <@para.pattern refined/> \<subseteq> ${rough.theorySymbol.filename}.Sps <@para.pattern rough/>"
proof -

  <#list refined.allSpses?reverse[1..] as part>
  interpret step${part?counter}: <#if part?has_next>wrappedSPSCompParallelConvert<#else>wrappedSPSCompNoOverlapConvert</#if>
  ${part.simpleName}_in
  ${part.simpleName}_out
  <#if part?index == 0>${refined.allSpses?reverse[0].simpleName}_in
  ${refined.allSpses?reverse[0].simpleName}_out
  <#else>step${part?counter -1}.comp_in
  step${part?counter -1}.comp_out
  </#if>"TYPE(${rough.input.theorySymbol.filename}.channels)"
  "TYPE(${rough.output.theorySymbol.filename}.channels)"
    apply(unfold_locales)
    apply(wrappedSPSConvert_proof input_channels_exists: ${part.input.theorySymbol.filename}.channels_exists)<#if part?index == 0>
    apply(wrappedSPSConvert_proof input_channels_exists: ${refined.allSpses?reverse[0].input.theorySymbol.filename}.channels_exists)</#if>
    <#if part?has_next>                                                                        
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    apply((solves \<open>simp; force\<close>))?
    done<#else>by(wrappedSPSCompNoOverlap_proof)</#if>

  </#list>

<#list refined.allSpses as refinedPart>
  <#list rough.allSpses as roughPart>
    <#t><#-- @ftlvariable name="refinedPart" type="montibelle.focus._symboltable.InstanceSymbol" -->
    <#t><#-- @ftlvariable name="roughPart"   type="montibelle.focus._symboltable.InstanceSymbol" -->
    <#if refinedPart.simpleName == roughPart.simpleName>
<#if refined.connectors.name == refinedPart.simpleName>
  <#if refinedPart?index == 0><#else>moreover </#if>have "<#if refined.connectors.parameters?has_content>\<And> ${refined.connectors.parameters?map(p -> p.name)?join(" ")}. </#if>{sbRenameCh ${refinedPart.simpleName}_in} \<then> ${refinedPart.theorySymbol.filename}.Sps <@para.pattern refined.connectors/> \<then> {sbRenameCh ${refinedPart.simpleName}_out} \<subseteq> ${roughPart.theorySymbol.filename}.Sps <@para.pattern rough.connectors/>"
    by (connector_simulation_proof simp_defs: ${refinedPart.theorySymbol.filename}.Sps_def
                                              ${refinedPart.input.theorySymbol.filename}.sbgetter_def
                                              ${refinedPart.output.theorySymbol.filename}.sbsetter_def
                                              ${roughPart.theorySymbol.filename}.Sps_def
                                              ${roughPart.input.theorySymbol.filename}.sbgetter_def
                                              ${roughPart.output.theorySymbol.filename}.sbsetter_def
                                    con_defs: ${refinedPart.theorySymbol.filename}.connector_def
                                              ${roughPart.theorySymbol.filename}.connector_def
                                sbGen_axioms: ${refinedPart.input.theorySymbol.filename}.SB.sbGen_axioms
                                              ${refinedPart.output.theorySymbol.filename}.SB.sbGen_axioms
                                              ${roughPart.input.theorySymbol.filename}.SB.sbGen_axioms
                                              ${roughPart.output.theorySymbol.filename}.SB.sbGen_axioms
                                buildSB_defs: ${refinedPart.input.theorySymbol.filename}.buildSB_def
                                              ${refinedPart.output.theorySymbol.filename}.buildSB_def
                                              ${roughPart.input.theorySymbol.filename}.buildSB_def
                                              ${roughPart.output.theorySymbol.filename}.buildSB_def)
<#else>
  <#if refinedPart?index == 0><#else>moreover </#if>have "<#if refined.parameters?has_content>\<And> ${refined.parameters?map(p -> p.name)?join(" ")}. </#if>{sbRenameCh ${refinedPart.simpleName}_in} \<then> ${refinedPart.theorySymbol.filename}.Sps <@para.pattern refined/> \<then> {sbRenameCh ${refinedPart.simpleName}_out} \<subseteq> ${roughPart.theorySymbol.filename}.Sps <@para.pattern rough/>"
    by (component_simulation_proof sps_ref: assms(${refinedPart?counter-1})
                                 simp_defs: ${refinedPart.theorySymbol.filename}.Sps_def
                                            ${refinedPart.inputMap.theorySymbol.filename}.Sps_def
                                            ${refinedPart.outputMap.theorySymbol.filename}.Sps_def
                                            ${refinedPart.input.theorySymbol.filename}.sbgetter_def
                                            ${refinedPart.output.theorySymbol.filename}.sbsetter_def
                                            ${roughPart.theorySymbol.filename}.Sps_def
                                            ${roughPart.inputMap.theorySymbol.filename}.Sps_def
                                            ${roughPart.outputMap.theorySymbol.filename}.Sps_def
                                            ${roughPart.input.theorySymbol.filename}.sbgetter_def
                                            ${roughPart.output.theorySymbol.filename}.sbsetter_def
                                  con_defs: ${refinedPart.inputMap.theorySymbol.filename}.connector_def
                                            ${roughPart.inputMap.theorySymbol.filename}.connector_def
                                            ${refinedPart.outputMap.theorySymbol.filename}.connector_def
                                            ${roughPart.outputMap.theorySymbol.filename}.connector_def
                              sbGen_axioms: ${refinedPart.input.theorySymbol.filename}.SB.sbGen_axioms
                                            ${refinedPart.output.theorySymbol.filename}.SB.sbGen_axioms
                                            ${roughPart.input.theorySymbol.filename}.SB.sbGen_axioms
                                            ${roughPart.output.theorySymbol.filename}.SB.sbGen_axioms
                              buildSB_defs: ${refinedPart.input.theorySymbol.filename}.buildSB_def
                                            ${refinedPart.output.theorySymbol.filename}.buildSB_def
                                            ${roughPart.input.theorySymbol.filename}.buildSB_def
                                            ${roughPart.output.theorySymbol.filename}.buildSB_def)
</#if>

    </#if>
  </#list>
</#list>
  ultimately show ?thesis
    apply(simp add: ${refined.theorySymbol.filename}.Sps_def ${refined.theorySymbol.filename}.rawSps_def
                    ${rough.theorySymbol.filename}.Sps_def ${rough.theorySymbol.filename}.rawSps_def)
    by(compositional_refinement_proof)?
qed

lemma refinement[simp]: "${refined.theorySymbol.filename}.Sps <@para.pattern refined/> \<subseteq> ${rough.theorySymbol.filename}.Sps <@para.pattern rough/>"
  using refinement_withAssms
  (* autosledgi *) oops


end
