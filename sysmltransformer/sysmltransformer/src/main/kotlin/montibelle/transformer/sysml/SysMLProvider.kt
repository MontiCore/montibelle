package montibelle.transformer.sysml

import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol
import de.monticore.lang.componentconnector._symboltable.RequirementSymbol
import de.monticore.lang.sysmlconstraints._symboltable.RequirementUsageSymbol
import de.monticore.lang.sysmlconstraints._visitor.SysMLConstraintsVisitor2
import de.monticore.lang.sysmlparts._symboltable.AttributeDefSymbol
import de.monticore.lang.sysmlparts._symboltable.EnumDefSymbol
import de.monticore.lang.sysmlparts._symboltable.PartDefSymbol
import de.monticore.lang.sysmlparts._visitor.SysMLPartsVisitor2
import de.monticore.lang.sysmlv2.SysMLv2Tool
import de.monticore.lang.sysmlv2._symboltable.ISysMLv2Scope
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol
import de.se_rwth.commons.logging.Log
import montibelle.transformer.sysml.Main.ifAnyThenInfo
import montibelle.transformer.sysml.Main.info
import java.io.IOException
import java.util.*
import kotlin.jvm.optionals.getOrNull
import kotlin.let

object SysMLProvider {

  @JvmStatic
  fun provideComponents(scope: ISysMLv2Scope): List<MildComponentSymbol> {
    Log.trace("Searching for part defs in ${scope.name}", javaClass.name)

    val traverser = SysMLv2Tool().traverser

    val partDefs = mutableListOf<PartDefSymbol>()

    traverser.add4SysMLParts(object : SysMLPartsVisitor2 {
      override fun visit(node: PartDefSymbol) {
        partDefs.add(node)
      }
    })

    scope.accept(traverser)

    Log.trace("Found ${partDefs.size} part defs, adapting to components...",
      javaClass.name)

    val components = partDefs
        .filter { it.isPresentAstNode }
        .mapIndexed { index, partDefSymbol ->
          info("Transforming ${index+1} of ${partDefs.size}: component ${partDefSymbol.fullName}")
          (partDefSymbol.enclosingScope as ISysMLv2Scope).resolveMildComponent(partDefSymbol.fullName).get()
    }

    Log.trace("Adapted ${components.size} components", javaClass.name)

    return components
  }

  @JvmStatic
  fun provideRequirements(scope: ISysMLv2Scope): List<RequirementSymbol> {
    Log.trace("Searching for requirements in ${scope.name}", javaClass.name)
    val requirementUsages = mutableListOf<RequirementUsageSymbol>()

    val traverser = SysMLv2Tool().traverser
    traverser.add4SysMLConstraints(object : SysMLConstraintsVisitor2 {
      override fun visit(node: RequirementUsageSymbol) {
        if("Requirement" == node.name || "req_SecurityOfGate" == node.name) {
          requirementUsages.add(node)
        }
      }
    })
    scope.accept(traverser)

    val requirements = requirementUsages
      .filter { it.isPresentAstNode }
      .mapIndexed { index, requirementUsageSymbol ->
        info("Transforming ${index+1} of ${requirementUsages.size}: requirementUsage ${requirementUsageSymbol.fullName}")
        (requirementUsageSymbol.enclosingScope as ISysMLv2Scope).resolveRequirement(requirementUsageSymbol.fullName).get()
      }

    Log.trace("Adapted ${requirements.size} requirementUsages", javaClass.name)
    return requirements
  }

  @JvmStatic
  fun provideUserDefinedTypes(scope: ISysMLv2Scope): List<TypeSymbol> {
    Log.trace("Searching for user-defined types in ${scope.name}", javaClass.name)
    val tool = SysMLv2Tool()

    val traverser = tool.traverser

    val userTypes = mutableListOf<TypeSymbol>()

    traverser.add4SysMLParts(object : SysMLPartsVisitor2 {
      override fun visit(node: EnumDefSymbol) {
        if (node.isPresentAstNode) {
          userTypes += node.enclosingScope.resolveType(node.fullName).get()
        }
      }
      override fun visit(node: AttributeDefSymbol) {
        if (node.isPresentAstNode) {
          userTypes += node.enclosingScope.resolveType(node.fullName).get()
        }
      }
    })

    scope.accept(traverser)

    Log.trace("Found ${userTypes.size} user-defined types", javaClass.name)
    return userTypes
  }
}
