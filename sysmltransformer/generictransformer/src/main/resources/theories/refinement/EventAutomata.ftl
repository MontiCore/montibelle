<#t><#import "../helper/Macros.ftl" as macro>
<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Datatype.ftl" as datatype>
<#t><#import "../helper/Type.ftl" as type>
<#t>
<#t>
<#t><#-- @ftlvariable name="tc"       type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"  type="Boolean" -->
<#t><#-- @ftlvariable name="th"       type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"      type="montibelle.focus._ast.ASTRefinement" -->
<#t><#-- @ftlvariable name="rough"    type="montibelle.focus._symboltable.EventAutomatonSymbol" -->
<#t><#-- @ftlvariable name="refined"  type="montibelle.focus._symboltable.EventAutomatonSymbol" -->
<#t>
<#t>${tc.signature("comment", "th", "ref")}
<#t>
<#t><#assign roughFile = ref.rough.theorySymbol.filename>
<#t><#assign refinedFile = ref.refined.theorySymbol.filename>
<#t>
<#t><#assign rough = ref.rough>
<#t><#assign refined = ref.refined>
<#t>
<#t><#if comment><@macro.comment/></#if>
theory ${th.filename}
  imports
    (* Core *) automaton.AREC inc.TryTac
    (* Gen  *) ${rough.theorySymbol.importFrom(ref.theorySymbol)}<#rt>
<#lt> ${refined.theorySymbol.importFrom(ref.theorySymbol)}<#rt>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin


fun stateInv:: "${refined.states.theorySymbol.filename}.State \<Rightarrow> bool" where
"stateInv (${refined.states.theorySymbol.filename}.StateConstr s<#rt>
<#lt><#list refined.states.variableNamesList as var> ${var}</#list>)
  = True"

fun paramMap:: "<@para.type ref.refined/> \<Rightarrow> <@para.type ref.rough/>" where
"paramMap <@para.pattern ref.refined/> = <@para.pattern ref.rough/>"

fun stateMap :: "${refined.states.theorySymbol.filename}.State \<Rightarrow> ${rough.states.theorySymbol.filename}.State" where
<#list refined.states.astNode.getStatesList() as state>
<#lt>"stateMap (${refined.states.theorySymbol.filename}.StateConstr<#rt>
  ${refined.states.theorySymbol.filename}.${state}<#rt>
  <#list refined.states.astNode.getStateVariableList() as var>${var.name}</#list>)<#rt>
  = ${rough.states.theorySymbol.filename}.StateConstr<#rt>
  ${rough.states.theorySymbol.filename}.${state}<#rt>
  <#list refined.states.astNode.getStateVariableList() as var>${var.name}</#list>"<#sep>|</#sep>
</#list>

section \<open>Refinement\<close>
<#list ref.rough.input.channels as channel>

lemma transition_refine_${channel.name}:
  assumes "(nextState, output) \<in> ${refinedFile}.eventTransition p state (${channel.localName}, ${type.constructor(channel.typeSymbol)} sbe)"
    shows "(stateMap nextState, output) \<in> ${roughFile}.eventTransition (paramMap p) (stateMap state) (${channel.localName}, ${type.constructor(channel.typeSymbol)} sbe)
            \<or> ${roughFile}.eventTransition (paramMap p) (stateMap state) (${channel.localName}, ${type.constructor(channel.typeSymbol)} sbe) = {}"
  apply(insert assms)
  apply(cases state)                                                  
  apply(cases p)?
  <#---->
  <#if refined.states.variableNamesList?has_content>
  apply(case_tac x1)?
  <#else>
  apply(case_tac x)?
  </#if>
  apply auto                                 
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} ${roughFile}.${channel.name}_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_${channel.name}:
  assumes "${refinedFile}.eventTransition p state (${channel.localName}, ${type.constructor(channel.typeSymbol)} sbe) = {}"
    shows "${roughFile}.eventTransition (paramMap p) (stateMap state) (${channel.localName}, ${type.constructor(channel.typeSymbol)} sbe) = {}"
  apply(insert assms)
  apply(cases state)                                                  
  apply(cases p)?
    <#---->
  <#if refined.states.variableNamesList?has_content>
  apply(case_tac x1)?
  <#else>
  apply(case_tac x)?
  </#if>
  apply auto                                 
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} ${roughFile}.${channel.name}_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry
</#list>

lemma transition_refine_tick:
  assumes "(nextState, output) \<in> ${refinedFile}.tickTransition p state"
    shows "(stateMap nextState, output) \<in> ${roughFile}.tickTransition (paramMap p) (stateMap state)
            \<or> ${roughFile}.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)                                                  
  apply(cases p)?
  <#---->
  <#if refined.states.variableNamesList?has_content>
  apply(case_tac x1)?
  <#else>
  apply(case_tac x)?
  </#if>
  apply auto                                 
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} ${roughFile}.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_notempty_tick:
  assumes "${refinedFile}.tickTransition p state = {}"
    shows "${roughFile}.tickTransition (paramMap p) (stateMap state) = {}"
  apply(insert assms)
  apply(cases state)                                                  
  apply(cases p)?
  <#---->
  <#if refined.states.variableNamesList?has_content>
  apply(case_tac x1)?
  <#else>
  apply(case_tac x)?
  </#if>
  apply auto                                 
  apply(tactic \<open>doIT (realGuards3 @{term "paramMap p"} @{term "stateMap state"} ${roughFile}.tick_transitionList) @{context}\<close>)
  apply trytac?
  (* autosledgi *) sorry

lemma transition_refine:
  assumes "(nextState, output) \<in> ${refinedFile}.eventTransition p state sbe"
    shows "(stateMap nextState, output) \<in> ${roughFile}.eventTransition (paramMap p) (stateMap state) sbe
            \<or> ${roughFile}.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only:<#list ref.rough.input.channels as channel> transition_refine_${channel.name}</#list>)
  by simp_all?

lemma transition_notempty:
  assumes "${refinedFile}.eventTransition p state sbe = {}"
  shows "${roughFile}.eventTransition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  apply(cases sbe; rename_tac c msg; case_tac c; case_tac msg)
  apply(simp_all only:<#list ref.rough.input.channels as channel> transition_notempty_${channel.name}</#list>)
  by simp_all?

lemma initials_refine:
  assumes "initState \<in> ${refinedFile}.initialConfigs p"
    shows "apfst stateMap initState \<in> ${roughFile}.initialConfigs (paramMap p)
            \<or> ${roughFile}.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialConfigs_def ${roughFile}.initialConfigs_def)
  (* autosledgi *) sorry

lemma initials_notempty:
  assumes "${refinedFile}.initialConfigs p = {}"
    shows "${roughFile}.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialConfigs_def ${roughFile}.initialConfigs_def)
  (* autosledgi *) sorry

theorem statesem_refine:
  assumes "stateInv state"
    shows "eStateSem (${refinedFile}.behavior.eaut p) state
         \<subseteq> eStateSem (${roughFile}.behavior.eaut (paramMap p)) (stateMap state)"
  apply(rule eaut_statesem_refine [where Inv="stateInv"])
          apply(simp_all only: transition_refine transition_notempty transition_refine_tick transition_notempty_tick)
     apply (simp add: assms)
     (* autosledgi *) sorry

theorem sem_refine: "eSem (${refinedFile}.behavior.eaut p)
                   \<subseteq> eSem (${roughFile}.behavior.eaut (paramMap p))"
  apply(rule eaut_sem_refine [where Inv="stateInv" and f="stateMap" and g="paramMap"])
      apply(simp_all only: initials_refine statesem_refine initials_notempty)
    apply(rename_tac s; case_tac s; simp add: ${roughFile}.initialConfigs_def ${refinedFile}.initialConfigs_def)+
    (* autosledgi *) sorry

theorem refinement[simp]: "${refinedFile}.behavior.Sem p \<subseteq> ${roughFile}.behavior.Sem (paramMap p)"
  apply(simp add: ${refinedFile}.behavior.Sem_def ${roughFile}.behavior.Sem_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
