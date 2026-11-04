package montibelle.transformer.sysml.printer

import de.monticore.expressions.expressionsbasis._ast.ASTExpression
import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression
import de.monticore.lang.sysmlexpressions._ast.ASTConditionalNotExpression
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLInstantiation
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLSequenceExpression
import de.monticore.prettyprint.IndentPrinter
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedType
import de.monticore.types.mccollectiontypes._ast.ASTMCListType
import montibelle.transformer.sysml.extensions.getIsabelleName
import montibelle.transformer.sysml.extensions.isAttributeUsage

class TsynAutomatonSysMLExpressions2Isabelle(printer: IndentPrinter, settings: IsabellePrinterSettings) : SysMLExpressions2Isabelle(printer, settings) {

  override fun traverse(node: ASTConditionalNotExpression) {
    if (node.expression is ASTNameExpression) {
      val nameExpr = node.expression as ASTNameExpression
      if (nameExpr.isAttributeUsage()) {
        val varName = nameExpr.getIsabelleName()
        printer.print("(lift (Not $varName))")
        return
      }
    }

    getTraverser().visit(node)
    node.expression.accept(getTraverser())
    getTraverser().endVisit(node)
  }

  override fun traverse(node: ASTSysMLSequenceExpression) {
    buildTsynTuple(node.expressionList)
  }

  private fun buildTsynTuple(elements: List<ASTExpression>) {
    printer.print("(liftedPair (")
    elements[0].accept(getTraverser())
    printer.print(", ")
    if (elements.size == 2) {
      elements[1].accept(getTraverser())
    } else {
      buildTsynTuple(elements.drop(1))
    }
    printer.print("))")
  }

  override fun visit(node: ASTSysMLInstantiation) {
    if (isList(node)) {
      printer.print("(liftedList [")
      settings.isBracketBeforeArg = true
    } else {
      super.visit(node)
    }
  }

  override fun endVisit(node: ASTSysMLInstantiation) {
    if (isList(node)) {
      printer.print("])")
    } else {
      super.endVisit(node)
    }
  }

  private fun isList(node: ASTSysMLInstantiation): Boolean {
    return node.mcType is ASTMCListType ||
      (node.mcType is ASTMCQualifiedType
        && (node.mcType as ASTMCQualifiedType).mcQualifiedName.baseName == "List")
  }
}
