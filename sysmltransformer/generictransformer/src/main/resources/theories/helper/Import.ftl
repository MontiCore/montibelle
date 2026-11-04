<#function datatype sps>
<#---->
<#-- @ftlvariable name="sps"  type="montibelle.focus._symboltable.SpsSymbol" -->
  <#return "${sps.input.theorySymbol.importFrom(sps.theorySymbol)}" +
    " ${sps.output.theorySymbol.importFrom(sps.theorySymbol)}">
</#function>

<#function datatypeImports currentTheory function constants>
<#---->
<#-- @ftlvariable name="currentTheory"         type="montibelle.focus._ast.ASTTheory" -->
<#-- @ftlvariable name="function"   type="montibelle.focus._ast.ASTFocusFunction" -->
<#-- @ftlvariable name="constants"   type="montibelle.transformer.generic.Constants" -->
  <#assign imports = []>

  <#list function.getParameterList() as p>
    <#assign theory = constants.getTheoryFor(
        p.symbol.symType
    )>

    <#if theory.isPresent()>
      <#assign importName = theory.get().importFrom(currentTheory.getSymbol())>

      <#if !imports?seq_contains(importName)>
        <#assign imports = imports + [importName]>
      </#if>
    </#if>
  </#list>

  <#return imports?join(" ")>
</#function>
