<#t><#import "../helper/Parameter.ftl" as para>
<#t><#import "../helper/Macros.ftl" as macro>
<#t>
<#t><#-- @ftlvariable name="tc"          type="de.monticore.generating.templateengine.TemplateController" -->
<#t><#-- @ftlvariable name="comment"     type="Boolean" -->
<#t><#-- @ftlvariable name="th"          type="montibelle.focus._ast.ASTTheory" -->
<#t><#-- @ftlvariable name="ref"         type="montibelle.focus._ast.ASTRefinement" -->
<#t><#-- @ftlvariable name="ref.rough"   type="montibelle.focus._ast.ASTAutomaton" -->
<#t><#-- @ftlvariable name="ref.refined" type="montibelle.focus._ast.ASTAutomaton" -->
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
    (* Gen *) ${rough.theorySymbol.importFrom(ref.theorySymbol)} ${refined.theorySymbol.importFrom(ref.theorySymbol)}<#rt>
    <#lt><#if ref.stateMapping?has_content> ${ref.stateMapping.theorySymbol.importFrom(ref.theorySymbol)}</#if><#rt>
    <#lt><#if ref.paramMapping?has_content> ${ref.paramMapping.theorySymbol.importFrom(ref.theorySymbol)}</#if><#rt>
    <#lt><#if ref.stateInv?has_content> ${ref.stateInv.theorySymbol.importFrom(ref.theorySymbol)}</#if>
    (* Hwl  *)<#list th.prologueImportStatements as hwl> ${hwl}</#list>

begin

section \<open>Refinement\<close>

lemma transition_refine:
  assumes "(nextState, output) \<in> ${refinedFile}.transition p state sbe"
    shows "(stateMap nextState, output) \<in> ${roughFile}.transition (paramMap p) (stateMap state) sbe
            \<or> ${roughFile}.transition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  unfolding ${refinedFile}.transition_def
  <#---->
  <#if ref.refined.states.variables?size == 0>
  apply(cases state; (cases p)?; (cases sbe)?; (case_tac x)?)                                      
  <#else>
  apply(cases state; (cases p)?; (cases sbe)?; (case_tac x1)?)                                      
  </#if>
  apply auto                                 
  unfolding ${roughFile}.transition_def
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} ${roughFile}.transitionList) @{context}\<close>)
  (* autosledgi *) sorry

lemma transition_notempty:
  assumes "${refinedFile}.transition p state sbe = {}"
    shows "${roughFile}.transition (paramMap p) (stateMap state) sbe = {}"
  apply(insert assms)
  unfolding  ${roughFile}.transition_def
  apply(cases state) apply(cases p)? apply(cases sbe)?                                     
  apply auto                                 
  unfolding ${refinedFile}.transition_def
  apply(tactic \<open>doIT (realGuards4 @{term "paramMap p"} @{term "stateMap state"} @{term "sbe"} ${roughFile}.transitionList) @{context}\<close>)
  (* autosledgi *) sorry

lemma initials_refine:
  <#if ref.refined.isStrongCausal() && ref.rough.isStrongCausal()>
  assumes "initState \<in> ${refinedFile}.initialConfigs p"
    shows "apfst stateMap initState \<in> ${roughFile}.initialConfigs (paramMap p)
            \<or> ${roughFile}.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialConfigs_def ${roughFile}.initialConfigs_def)
  <#else>
  assumes "initState \<in> ${refinedFile}.initialStates p"
    shows "stateMap initState \<in> ${roughFile}.initialStates (paramMap p)
            \<or> ${roughFile}.initialStates (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialStates_def ${roughFile}.initialStates_def)
  </#if>
  (* autosledgi *) sorry

lemma initials_notempty:
  <#if ref.refined.isStrongCausal() && ref.rough.isStrongCausal()>
  assumes "${refinedFile}.initialConfigs p = {}"
  shows "${roughFile}.initialConfigs (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialConfigs_def ${roughFile}.initialConfigs_def)
  <#else>
  assumes "${refinedFile}.initialStates p = {}"
    shows "${roughFile}.initialStates (paramMap p) = {}"
  using assms apply(simp add: ${refinedFile}.initialStates_def ${roughFile}.initialStates_def)
  </#if>
  (* autosledgi *) sorry

                                           

lemma statesem_refine: "${refinedFile}.behavior.StateSem p state
                      \<subseteq> ${roughFile}.behavior.StateSem (paramMap p) (stateMap state)"
                                                                                                                    
  apply(rule ndastaterefine_inv__ndagen[where Inv="stateInv" and f="stateMap" and g="paramMap"])
  apply(simp_all only: transition_refine transition_notempty)
  apply(simp_all only: ${refinedFile}.behavior.tsGen_axioms ${roughFile}.behavior.tsGen_axioms)
  apply(case_tac "nextState::${refined.states.theorySymbol.filename}.State")
  (* autosledgi *) sorry

theorem sem_refine: "ndaSem (${refinedFile}.behavior.nda p)
                   \<subseteq> ndaSem (${roughFile}.behavior.nda (paramMap p))"
  apply(rule ndastaterefineinv_ndagen_sem [where Inv="stateInv" and f="stateMap" and g="paramMap"])
  apply(simp_all only: initials_refine statesem_refine initials_notempty)
  apply(simp_all only: ${refinedFile}.behavior.tsGen_axioms ${roughFile}.behavior.tsGen_axioms)
                                                                            
  (* autosledgi *) sorry

lemma refinement[simp]: "${refinedFile}.behavior.Sem p \<subseteq> ${roughFile}.behavior.Sem (paramMap p)"
  apply(simp add: ${refinedFile}.behavior.nda_def ${roughFile}.behavior.nda_def)
  using sem_refine by(auto simp add: seqcomp_insert)?


end
