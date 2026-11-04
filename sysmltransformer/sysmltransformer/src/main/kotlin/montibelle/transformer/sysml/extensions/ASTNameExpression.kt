package montibelle.transformer.sysml.extensions

import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression
import de.monticore.lang.sysmlconstraints._ast.ASTConstraintUsage
import de.monticore.lang.sysmlconstraints._ast.ASTRequirementDef
import de.monticore.lang.sysmlparts._symboltable.AttributeUsageSymbol
import de.monticore.lang.sysmlv2._symboltable.ISysMLv2Scope
import de.se_rwth.commons.logging.Log
import trafos.ConnectionMapping

fun ASTNameExpression.isAttributeUsage(): Boolean {
  val scope = this.enclosingScope
  if (scope is ISysMLv2Scope) {
    val attrUsage = scope.resolveAttributeUsage(this.name)
    return attrUsage.isPresent
  }

  if (this.enclosingScope != null
    && this.enclosingScope.isPresentAstNode
    && this.enclosingScope.astNode is ASTConstraintUsage
    && this.enclosingScope.enclosingScope != null
    && this.enclosingScope.enclosingScope.isPresentAstNode
    && this.enclosingScope.enclosingScope.astNode is ASTRequirementDef)
  {
    val reqDefScope = this.enclosingScope.enclosingScope as ISysMLv2Scope
    val potentialAutomaton = reqDefScope.localRequirementSubjectSymbols[0]
      .typesList[0].printFullName()
    val automaton = reqDefScope.resolvePartDef(potentialAutomaton)
    if (automaton.isPresent) {
      (automaton.get().spannedScope as ISysMLv2Scope).localStateUsageSymbols
        .forEach {
          val stateVariable = (it.spannedScope as ISysMLv2Scope)
            .resolveAttributeUsageLocally(this.name)
        if (stateVariable.isPresent) {
          return true
        }
      }
    }
  }

  return false
}

fun ASTNameExpression.getAttributeUsage() : AttributeUsageSymbol? {
  val scope = this.enclosingScope
  if (scope is ISysMLv2Scope) {
    val attrUsage = scope.resolveAttributeUsage(this.name)
    return attrUsage.get()
  }
  return null
}

fun ASTNameExpression.isType() : Boolean {
  if(this.enclosingScope != null && this.enclosingScope is ISysMLv2Scope) {
    var scope = this.enclosingScope as ISysMLv2Scope
    var type = scope.resolveType(this.name)
    return type.isPresent
  }
  return false
}

fun ASTNameExpression.getIsabelleName(): String {
  if(this.isAttributeUsage()) {
    val mapping = ConnectionMapping.getInstance()
    val attrUsage = this.getAttributeUsage()
    if(mapping.isConnectedToPort(attrUsage)){
      val pattern = mapping.getPattern(attrUsage)
      return pattern
    }
    return "var_${this.name}"
  }
  else if(this.isType()) {
    var scope = this.enclosingScope as ISysMLv2Scope
    var type = scope.resolveType(this.name)
    return type.get().fullName.replace(".", "_")
  }
  else {
    Log.warn("Unknown name expression encountered: \"${this.name}\". " +
        "Proceed with caution.")
    return this.name
  }
}
