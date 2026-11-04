<#t><#import "helper/Type.ftl" as type>
<#t><#import "helper/Channel.ftl" as channel>
<#t>
<#t><#-- @ftlvariable name="dt"       type="montibelle.focus._ast.ASTBundle" -->
<#t><#-- @ftlvariable name="typePrinter" type="trafos.ITypePrinter" -->
<#t>
section \<open>Channel Type\<close>

typedef channels = "{<@channel.list dt.symbol.decardinalizedChannels()/>}"
  by auto
<#if !dt.symbol.channels?has_content>

                                                                                       
abbreviation "${dt.theorySymbol.filename?lower_case}_buildSB \<equiv> (\<lambda>(u::unit) cs::channels. \<epsilon>)"
</#if>

instance channels::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_channels
        typedef_finite_UNIV by fastforce

instantiation channels::<#if dt.symbol.channels?has_content>somechan<#else>emptychan</#if>
begin
  definition Rep_channels_def: "Rep = Rep_channels"
  definition Abs_channels_def:"Abs = Abs_channels"
  definition ChanDom_channels_def: "chanDom(a::channels myself) = {<#list dt.symbol.decardinalizedChannels() as c><@channel.description c/><#sep>, </#list>}"

  lemma rep_range[simp]: "range (Rep::channels \<Rightarrow> channel) = {<@channel.list dt.symbol.decardinalizedChannels()/>}"
    apply(subst Rep_channels_def)
    using type_definition.Rep_range type_definition_channels by fastforce

  instance
    apply(intro_classes)
      apply(simp add: Abs_channels_def Rep_channels_def Rep_channels_inverse)
     apply(simp add:ChanDom_channels_def insert_Diff_if)
    by clarsimp
end

theorem channels_chdom[simp]: "chDom TYPE (channels) = {<#list dt.symbol.decardinalizedChannels() as c><@channel.description c/><#sep>, </#list>}"
  by (metis ChanDom_channels_def chandom_chdom_eq)
<#list dt.symbol.decardinalizedChannels()>

                           
    <#items as c>
definition ${c.localName} :: "channels" where
"${c.localName} \<equiv> Abs_channels <@channel.description c/>"

lemma ${c.localName}_rep [simp, code]: "Rep ${c.localName} = <@channel.description c/>"
  unfolding Rep_channels_def ${c.localName}_def
  by (simp add: Abs_channels_inverse)

lemma ${c.name}_abs [simp, code]: "Abs <@channel.description c/> = ${c.localName}"
  by (metis abs_rep_id ${c.localName}_rep)

    </#items>
free_constructors channels for <#list dt.symbol.decardinalizedChannels() as c>${c.localName}<#sep> | </#list>
  unfolding<#list dt.symbol.decardinalizedChannels() as c> ${c.localName}_def</#list>
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "<#list dt.symbol.decardinalizedChannels() as c>P ${c.localName}<#sep> \<or> </#list> \<Longrightarrow> \<exists>c. P c"
  by auto                                                                                          
</#list>
<#if !dt.symbol.channels?has_content>


                           
definition channel_cempty :: "channels" where
"channel_cempty \<equiv> Abs_channels (CH ''cempty'' TUntimed TNone)"

lemma channel_cempty_rep [simp, code]: "Rep channel_cempty = (CH ''cempty'' TUntimed TNone)"
  unfolding Rep_channels_def channel_cempty_def
  by (simp add: Abs_channels_inverse)

lemma channel_cempty_abs [simp, code]: "Abs (CH ''cempty'' TUntimed TNone) = channel_cempty"
  by (metis abs_rep_id channel_cempty_rep)

free_constructors channels for channel_cempty
  unfolding channel_cempty_def
  apply (metis Rep_channels Rep_channels_inverse empty_iff insert_iff)
  apply (simp_all add: Abs_channels_inject)?
  done

lemma channels_exists: "P channel_cempty \<Longrightarrow> \<exists>c. P c"
  by auto
</#if>

instance channels::<#if dt.symbol.timing.isEventBased()>echan<#else>tschan</#if>
  apply(intro_classes)
  by(case_tac c;simp)

<#if dt.symbol.channels?has_content>
instantiation channels::enum
begin
  definition "enum_channels \<equiv> [<#list dt.symbol.decardinalizedChannels() as c>${c.localName}<#sep>, </#list>]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end
</#if>
<#if !dt.symbol.channels?has_content>
instantiation channels::enum
begin
  definition "enum_channels \<equiv> [channel_cempty]"
  definition "enum_all_channels P \<equiv> \<forall>c::channels. P c"
  definition "enum_ex_channels P \<equiv> \<exists>c::channels. P c"

  instance
    apply(intro_classes)
    apply(simp_all add: enum_channels_def enum_all_channels_def enum_ex_channels_def)
    using channels.exhaust by blast
end
</#if>
<#rt>

section \<open>Channel functions\<close>
<#list dt.symbol.decardinalizedChannels() as c>

lift_definition ${channel.constructor(c)} :: "${typePrinter.print(c.typeSymbol.symType)} \<Rightarrow> channels msgWithChan" is
"\<lambda>x. (${c.localName}, ${type.constructor(c.typeSymbol)} x)"
  by (simp add: well_def)
</#list>

