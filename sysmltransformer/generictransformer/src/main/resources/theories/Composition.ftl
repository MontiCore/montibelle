<#t><#import "helper/Import.ftl" as import>
<#t><#import "helper/Macros.ftl" as macro>
<#t><#import "helper/Channel.ftl" as channel>
<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Parameter.ftl" as para>
<#t><#import "helper/Datatype.ftl" as datatype>
<#t><#import "helper/Composition.ftl" as composition>
<#t>
<#t><#-- @ftlvariable name="tc"        type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="comp"      type="montibelle.focus._ast.ASTComposition" -->
<#t>
<#t>${tc.signature("comment", "th", "comp")}
<#t><#assign compSymbol = comp.symbol>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) sps.SPSFun bundlelocale.SBConvertGen
    (* Gen  *) ${import.datatype(comp.symbol)}<#rt>
      <#lt><#list comp.allSpses as sps> ${sps.theorySymbol.importFrom(comp.theorySymbol)}<#rt>
      <#lt></#list> ${comp.feedback.theorySymbol.importFrom(comp.theorySymbol)}
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


declare len_prod_inf_snd[simp del]

<#if comp.allSpses?size gt 1 >
section \<open>Compositional Datatype\<close>

text \<open>This section iteratively builds the composition's input and output bundle. While building, additional
            lemmata will be generated.\<close>
  <#list comp._bindingsRawToFinal() as binding>

(* Combines channels of <#list binding.atomsFinalToRaw as atom>${atom.name}<#sep>, </#list> *)
definition rawinput${binding.name}_map ::
    "<@channel.streamTypes binding.inputChannels/> \<Rightarrow>
    (<@channel.streamTypes binding.outer.inputChannels/> \<times> <@channel.streamTypes binding.inner.inputChannels/>)" where
"rawinput${binding.name}_map \<equiv>
    \<lambda> <@channel.parameter binding.inputChannels /> .
    (<@channel.parameter binding.outer.inputChannels />, <@channel.parameter binding.inner.inputChannels />)"

lemma rawinput${binding.name}_map_insert[simp]:
    "rawinput${binding.name}_map <@channel.parameter binding.inputChannels />
  = (<@channel.parameter binding.outer.inputChannels />, <@channel.parameter binding.inner.inputChannels />)"
  by(simp add: rawinput${binding.name}_map_def)

interpretation RawInput${binding.name}:
    sbUnionGen "${datatype.buildSB(binding.outer.instance.input)}"
    <#if binding?is_first>
               "${datatype.buildSB(compSymbol.allSpses?last.input)}"
    <#else>
               "RawInput${binding.inner.name}.constructor"
    </#if>
               "rawinput${binding.name}_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawinput${binding.name}_map_def)+
    by(intro cont2cont)?
  </#list>


subsection \<open>Output\<close>
  <#list comp._bindingsRawToFinal() as binding>

definition rawoutput${binding.name}_map ::
  "<@channel.streamTypes binding.outputChannels/> \<Rightarrow>
  (<@channel.streamTypes binding.outer.outputChannels/> \<times> <@channel.streamTypes binding.inner.outputChannels/>)" where
"rawoutput${binding.name}_map \<equiv>
  \<lambda> <@channel.parameter binding.outputChannels /> .
  (<@channel.parameter binding.outer.outputChannels />, <@channel.parameter binding.inner.outputChannels/>)"

lemma rawoutput${binding.name}_map_insert[simp]:
  "rawoutput${binding.name}_map <@channel.parameter binding.outputChannels />
  = (<@channel.parameter binding.outer.outputChannels/>, <@channel.parameter binding.inner.outputChannels/>)"
  by(simp add: rawoutput${binding.name}_map_def)

interpretation RawOutput${binding.name}:
    sbUnionGen "${binding.outer.instance.output.theorySymbol.filename}.buildSB"
      <#if binding?is_first>
               "${comp.symbol.allSpses?last.output.theorySymbol.filename}.buildSB"
      <#else>
               "RawOutput${binding.inner.name}.constructor"
      </#if>
               "rawoutput${binding.name}_map"
  apply(unfold_locales, simp_all)
        apply(rule injI, case_tac x, case_tac y, simp, force?, auto)
    apply(simp_all only: len_prod_def2 min.assoc)?
    apply(simp add: min.commute min.left_commute image_iff surj_def id_def
                    len_unit_def len_prod_def rawoutput${binding.name}_map_def)+
    by(intro cont2cont)?
  </#list>


section \<open>Subsets\<close>

subsection \<open>Raw Datatype to Instance Conversion\<close>
  <#list comp._fromFinalToRaw() as atom>

subsubsection \<open>${atom.name}\<close>

abbreviation "${comp.theorySymbol.filename}_rawinput2${atom.name} \<equiv> <#rt>
    <#list atom.toFinal() as route>
      (<#if route.raw.isInnerElement()>fst<#else>snd</#if> o rawinput${route.final.name}_map)<#t>
      <#sep> o </#sep><#t>
    </#list>
    <#lt>"

abbreviation "${comp.theorySymbol.filename}_rawoutput2${atom.name} \<equiv> <#rt>
    <#list atom.toFinal() as route>
      (<#if route.raw.isInnerElement()>fst<#else>snd</#if> o rawoutput${route.final.name}_map)<#t>
      <#sep> o </#sep><#t>
    </#list>
    <#lt>"

interpretation ${atom.name}_input_Sub:
    subsetGen "RawInput.constructor" "${datatype.buildSB(atom.instance.input)}" "${comp.theorySymbol.filename}_rawinput2${atom.name}"
    <#list 0..<atom.depth as _>
  apply(rule subsetgen_transitive)
    </#list>
  using <#rt>
    <#list atom.toFinal() as route>
      <#t>RawInput${route.final.name}.subset_fst RawInput${route.final.name}.subset_snd
      <#t><#sep><#lt>${"\n"}        <#rt></#sep>
    </#list><#lt> by blast+

interpretation ${atom.name}_output_Sub:
    subsetGen "RawOutput.constructor" "${atom.instance.output.theorySymbol.filename}.buildSB" "${comp.theorySymbol.filename}_rawoutput2${atom.name}"
    <#list 0..<atom.depth as _>
  apply(rule subsetgen_transitive)
    </#list>
  using <#rt>
    <#list atom.toFinal() as route>
      <#t>RawOutput${route.final.name}.subset_fst RawOutput${route.final.name}.subset_snd
      <#t><#sep><#lt>${"\n"}        <#rt></#sep>
    </#list><#lt> by blast+

  </#list>

subsection \<open>Full Composition\<close>

fun rawinput2${comp.theorySymbol.filename?lower_case} ::
    "<@channel.streamTypes comp._finalBinding.inputChannels/>
  \<Rightarrow> <@datatype.streamTypes compSymbol.input/>" where
"rawinput2${comp.theorySymbol.filename?lower_case}${"\n"}<#rt><#---->
    <@channel.parameter comp._finalBinding.inputChannels/>${"\n"}<#rt>
  = <@datatype.pattern compSymbol.input/>"

interpretation ${comp.theorySymbol.filename}_input_Sub:
    subsetGen "RawInput.constructor"
              "${datatype.buildSB(compSymbol.input)}"
              "rawinput2${comp.theorySymbol.filename?lower_case}"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add:<#if compSymbol.input.channels?has_content> ${compSymbol.input.theorySymbol.filename}.buildSB_def</#if>
    <#list compSymbol.allSpses?filter(inst -> inst.input.channels?has_content) as inst>
               ${inst.input.theorySymbol.filename}.buildSB_def<#if inst?is_last>)+<#rt></#if>
    </#list>

fun rawoutput2${comp.theorySymbol.filename?lower_case} ::
    "<@channel.streamTypes comp._finalBinding.outputChannels/>
  \<Rightarrow> <@datatype.streamTypes compSymbol.output/>" where
"rawoutput2${comp.theorySymbol.filename?lower_case}${"\n"}<#rt><#---->
    <@channel.parameter comp._finalBinding.outputChannels/>${"\n"}<#rt>
  = <@datatype.pattern compSymbol.output/>"

interpretation ${comp.theorySymbol.filename}_output_Sub:
    subsetGen "RawOutput.constructor"
              "${datatype.buildSB(compSymbol.output)}"
              "rawoutput2${comp.theorySymbol.filename?lower_case}"
  apply(unfold_locales)
  apply(case_tac c, case_tac super; auto)
  by(simp add:<#if compSymbol.output.channels?has_content> ${compSymbol.output.theorySymbol.filename}.buildSB_def</#if>
    <#list compSymbol.allSpses?filter(inst -> inst.output?has_content) as inst>
               ${inst.output.theorySymbol.filename}.buildSB_def<#if inst?is_last>)+<#rt></#if>
    </#list>

subsection \<open>Feedback\<close>

fun rawinput2${comp.theorySymbol.filename?lower_case}_feedback ::
    "<@channel.streamTypes comp._finalBinding.inputChannels/>
  \<Rightarrow> <@datatype.streamTypes compSymbol.feedback/>" where
"rawinput2${comp.theorySymbol.filename?lower_case}_feedback${"\n"}<#rt>
    <@channel.parameter comp._finalBinding.inputChannels/>${"\n"}<#rt>
  = <@datatype.parameter compSymbol.feedback/>"

interpretation feedback_input_sub:
    subsetGen "RawInput.constructor"
              "${datatype.buildSB(compSymbol.feedback)}"
              "rawinput2${comp.theorySymbol.filename?lower_case}_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add:<#if compSymbol.feedback.channels?has_content> ${compSymbol.feedback.theorySymbol.filename}.buildSB_def</#if>
    <#list compSymbol.allSpses?filter(inst -> inst.input.channels?has_content) as inst>
               ${inst.input.theorySymbol.filename}.buildSB_def<#if inst?is_last>)+<#rt></#if>
    </#list>

fun rawoutput2${comp.theorySymbol.filename?lower_case}_feedback ::
    "<@channel.streamTypes comp._finalBinding.outputChannels/>
  \<Rightarrow> <@datatype.streamTypes compSymbol.feedback/>" where
"rawoutput2${comp.theorySymbol.filename?lower_case}_feedback${"\n"}<#rt>
    <@channel.parameter comp._finalBinding.outputChannels/>${"\n"}<#rt>
  = <@datatype.parameter compSymbol.feedback/>"

interpretation feedback_output_sub:
    subsetGen "RawOutput.constructor"
              "${datatype.buildSB(compSymbol.feedback)}"
              "rawoutput2${comp.theorySymbol.filename?lower_case}_feedback"
  apply(unfold_locales)
  apply(case_tac c; auto)
  by(simp add:<#if compSymbol.feedback.channels?has_content> ${compSymbol.feedback.theorySymbol.filename}.buildSB_def</#if>
    <#list compSymbol.allSpses?filter(inst -> inst.output.channels?has_content) as inst>
               ${inst.output.theorySymbol.filename}.buildSB_def<#if inst?is_last>)+<#rt></#if>
    </#list>

</#if>


section \<open>rawSPS\<close>

definition rawSps :: "<@para.type comp.symbol/> \<Rightarrow> <#rt>
(${composition.inputType(compSymbol)}\<^sup>\<Omega> \<rightarrow> ${composition.outputType(compSymbol)}\<^sup>\<Omega>) set" where
"rawSps \<equiv> \<lambda> <@para.pattern comp.symbol/>. <#rt>
  <#lt><#list comp.allSpses as sps>${sps.theorySymbol.filename}.Sps <@para.pattern sps.symbol/><#sep> \<Otimes> </#list>"


section \<open>Lemmas\<close>

(* Lemmas to assert correct typing *)
lemma assert_input_type: "chDom TYPE (${compSymbol.input.theorySymbol.filename}.channels) = chDom TYPE(${composition.inputType(compSymbol)})"
  by auto

lemma assert_output_type: "chDom TYPE (${compSymbol.output.theorySymbol.filename}.channels) \<subseteq> chDom TYPE(${composition.outputType(compSymbol)})"
  by auto

subsection\<open>Properties after Composition\<close>

declare Fun.comp_apply[simp del] Automaton.stateSem_bot[simp del] ubunion_fst[simp del] sbtypecast_closed[simp del] SB.sbgetch_empty[simp del]

<#t><#assign lhs="" /> <#---->
<#list comp.allSpses as instance>

subsubsection \<open>${instance.name}\<close>

lemma ${instance.name}_input_eq:
  assumes "spf \<in> (rawSps <@para.pattern comp.symbol/>)"
  <#if instance?index == 0>
    <#t><#assign lhs="(sb \\<uplus>\\<^sub>- spf\\<cdot>sb)" />
  <#elseif !instance?is_last>
    <#t> <#function repeat n>
    <#t>   <#assign res ="spf\\<cdot>sb"/>
    <#t>   <#list 0..<n as i>
    <#t>     <#assign res = "(${res})\\<star>\\<^sub>2"/>
    <#t>   </#list>
    <#t>   <#return res/>
    <#t> </#function>
    <#t><#assign lhs="((${lhs}\\<star>\\<^sub>2) \\<uplus>\\<^sub>- (${repeat(instance?index)}))"/>
  </#if>
  <#t><#---->
  <#t><#---->
    shows "(${lhs}<#if instance?is_last>\<star>\<^sub>2<#else>\<star>\<^sub>1</#if>) = ((sb \<uplus> spf\<cdot>sb)\<star>)"
  apply (simp add: sbtypecast_reduce1)?
  apply (simp add: sbtypecast_reduce2)?
  apply (rule sb_eqI)?
  apply (simp only: sbtypecast_getch)?
  apply (case_tac c)?
  by (simp_all+)?

lemma ${instance.name}_output_eq:
  assumes "spf \<in> (rawSps <@para.pattern comp.symbol/>)"
    shows "(spf\<cdot>sb)\<star> = (<#if instance?is_last>(${repeat(instance?index-1)})\<star>\<^sub>2<#else>(${repeat(instance?index)})\<star>\<^sub>1</#if>)"
  by(simp add: sbtypecast_reduce1 sbtypecast_reduce2)
</#list>
<#list comp.partsDefinitionListUnsafe as instance> <#---->
  <#if (instance.inputBundleSymbol.channels?has_content)>

lemma ${instance.name}_pred_general:
  assumes "spf \<in> (rawSps <@para.pattern compSymbol/>)"
      and "\<And>sb spf. spf \<in> ${instance.spsSymbol.theorySymbol.filename}.Sps <@para.value instance.symbol/><#rt>
     <#lt> \<Longrightarrow> P (${instance.spsSymbol.input.theorySymbol.filename}.SB.getter\<cdot>sb)<#rt>
                           <#lt> (${instance.spsSymbol.output.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P (${instance.inputBundleSymbol.theorySymbol.filename}.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))<#rt>
     <#lt> (${instance.outputBundleSymbol.theorySymbol.filename}.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst ${instance.name}_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst ${instance.name}_output_eq[OF assms(1)])
  by(pred_solver inst2def: ${instance.theorySymbol.filename}.pred_inst2def assms: assms)
  <#elseif (instance.outputBundleSymbol.channels?has_content)>

lemma ${instance.name}_pred_general:
  assumes "spf \<in> (rawSps <@para.pattern compSymbol/>)"
      and "\<And>sb spf. spf \<in> ${instance.spsSymbol.theorySymbol.filename}.Sps <@para.value instance.symbol/><#rt>
     <#lt> \<Longrightarrow> P () (${instance.spsSymbol.output.theorySymbol.filename}.SB.getter\<cdot>(spf\<cdot>sb))"
    shows "P () (${instance.outputBundleSymbol.theorySymbol.filename}.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst ${instance.name}_input_eq[OF assms(1), symmetric])
  apply(insert assms(1), simp only: rawSps_def, subst ${instance.name}_output_eq[OF assms(1)])
  by(pred_solver inst2def: ${instance.theorySymbol.filename}.pred_inst2def assms: assms)
  <#else>

lemma ${instance.name}_pred_general:
  assumes "spf \<in> (rawSps <@para.pattern comp.symbol/>)"
      and "\<And>sb spf. spf \<in> ${instance.spsSymbol.theorySymbol.filename}.Sps <@para.value instance.symbol/><#rt>
     <#lt> \<Longrightarrow> P () ()"
    shows "P () ()"
  apply(insert assms(1), simp only: rawSps_def)
    <#list 0..instance?index as index>
      <#if !index?is_last>
  apply(rule spscomp_predicater2, simp, simp)
      <#elseif index?is_last && !instance?is_last>
  apply(rule spscomp_predicatel2, simp)
      </#if>
    </#list>
  apply(auto simp add: ${instance.theorySymbol.filename}.Sps_def)
  apply(rule assms(2))
  by simp
  </#if>
</#list>

lemma connector_apply_eq:
  assumes "spf \<in> (rawSps <@para.pattern compSymbol/>)"
    shows "${compSymbol.connectors.theorySymbol.filename}.connector\<cdot>(${compSymbol.connectors.input.theorySymbol.filename}.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>))
                         = (${compSymbol.connectors.output.theorySymbol.filename}.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply (subst ${compSymbol.connectors.name}_input_eq[OF assms(1), symmetric])
  apply (insert assms(1), simp only: rawSps_def, subst ${comp.connectors.name}_output_eq[OF assms(1)])
  apply (rule spscomp_predicatel2, simp)
  by (simp add: ${comp.connectors.theorySymbol.filename}.Sps_def)

lemma feedback_getter_eq:
  assumes "spf \<in> (rawSps <@para.pattern compSymbol/>)"
    shows "(${compSymbol.feedback.theorySymbol.filename}.SB.getter\<cdot>((sb \<uplus> spf\<cdot>sb)\<star>)) = (${compSymbol.feedback.theorySymbol.filename}.SB.getter\<cdot>((spf\<cdot>sb)\<star>))"
  apply(subst sbunion_conv_snd)
  by simp_all

declare Fun.comp_apply[simp add] Automaton.stateSem_bot[simp add] ubunion_fst[simp add] sbtypecast_closed[simp add] SB.sbgetch_empty[simp add]

section \<open>Final SPS\<close>

definition Sps :: "<@para.type compSymbol/> \<Rightarrow> <#rt>
(${compSymbol.input.theorySymbol.filename}.channels\<^sup>\<Omega> \<rightarrow> ${compSymbol.output.theorySymbol.filename}.channels\<^sup>\<Omega>) set" where
"Sps \<equiv> \<lambda> <@para.pattern compSymbol/>. spsConvert \<cdot> (rawSps <@para.pattern compSymbol/>) "

declare len_prod_inf_snd[simp]


end
