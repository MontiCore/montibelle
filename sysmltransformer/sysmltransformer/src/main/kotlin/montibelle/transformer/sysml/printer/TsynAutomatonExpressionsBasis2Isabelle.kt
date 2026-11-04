package montibelle.transformer.sysml.printer

import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression
import de.monticore.prettyprint.IndentPrinter
import montibelle.transformer.sysml.extensions.getIsabelleName
import montibelle.transformer.sysml.extensions.isAttributeUsage

class TsynAutomatonExpressionsBasis2Isabelle(printer: IndentPrinter, settings: IsabellePrinterSettings) : ExpressionsBasis2Isabelle(printer, settings) {

  override fun visit(node: ASTNameExpression) {
    if (node.isAttributeUsage()) {
      printer.print("(lift ${node.getIsabelleName()})")
    } else {
      super.visit(node)
    }
  }
}
