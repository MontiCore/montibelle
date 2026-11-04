package montibelle.transformer.sysml.printer

import de.monticore.expressions.commonexpressions._ast.*
import de.monticore.prettyprint.IndentPrinter

class TsynAutomatonCommonExpressions2Isabelle(printer: IndentPrinter, settings: IsabellePrinterSettings) : TsynCommonExpressions2Isabelle(printer, settings) {

  override fun traverse(node: ASTEqualsExpression) {
    printer.print("toBool (liftedEq (")
    node.left.accept(this.traverser)
    printer.print(") (")
    node.right.accept(this.traverser)
    printer.print("))")
  }

  override fun traverse(node: ASTNotEqualsExpression) {
    printer.print("toBool (liftedNot (liftedEq (")
    node.left.accept(this.traverser)
    printer.print(") (")
    node.right.accept(this.traverser)
    printer.print(")))")
  }

  override fun traverse(node: ASTGreaterThanExpression) {
    printer.print("toBool (liftedApplyTwo (<) (")
    node.right.accept(this.traverser)
    printer.print(") (")
    node.left.accept(this.traverser)
    printer.print("))")
  }

  override fun mapToIsabelleTsyn(fqn: String): String? = when (fqn) {
    "List.head"       -> "liftedApplyOne hd "
    "List.tail"       -> "liftedApplyOne tl "
    "List.count"      -> "liftedApplyOne length "
    "List.append"     -> "liftedApplyTwo append "
    "EventStream.nth" -> "liftedApplyOne esnth "
    else              -> super.mapToIsabelleTsyn(fqn)
  }
}
