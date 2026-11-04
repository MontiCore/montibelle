<#function split dimension tuple seperator=", ">
<#--
Splits the provided tuple into its individual parts.

Example: split(3,x) -> "(fst x), (fst (snd x)), (snd (snd x))"
         split(1,x) -> "x"
         split(0,x) -> ""

@ftlvariable name="dimension" type="int"
@ftlvariable name="tuple"     type="String"
@ftlvariable name="seperator" type="String"
-->
  <#if dimension == 0>
    <#return "">
  <#elseif dimension == 1>
    <#return tuple>
  <#else>
    <#return "(fst " + tuple + ")" + seperator + split(dimension-1, "(snd " + tuple + ")", seperator)>
  </#if>
</#function>

<#function getNth dimension n tuple>
<#--
Returns n-th element of the tuple

@ftlvariable name="dimension" type="int"
@ftlvariable name="n" type="int"
@ftlvariable name="tuple"     type="String"
@ftlvariable name="seperator" type="String"
-->
  <#if dimension == 0>
    <#return "">
  <#elseif dimension == 1>
    <#return tuple>
  <#else>
    <#return split(dimension, tuple)?split(", ")[n]/>
  </#if>
</#function>
