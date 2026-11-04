package montibelle.transformer.sysml.printer

import de.monticore.expressions.streamexpressions._ast.ASTStreamConstructorElement
import de.monticore.expressions.streamexpressions._ast.ASTStreamConstructorExpression
import de.monticore.expressions.streamexpressions._visitor.StreamExpressionsInheritanceHandler
import de.monticore.expressions.streamexpressions._visitor.StreamExpressionsVisitor2
import de.monticore.prettyprint.IndentPrinter

class StreamExpressions2Isabelle (val printer: IndentPrinter)
  : StreamExpressionsVisitor2, StreamExpressionsInheritanceHandler() {

  override fun traverse(node: ASTStreamConstructorExpression) {
    val elements = node.streamConstructorElementList
    for (i in elements.indices) {
      elements[i].accept(getTraverser())

      if (i < elements.size - 1) {
        printer.print(", ")
      }
    }
  }

  override fun visit(node: ASTStreamConstructorElement) {
    if(node.isPresentTick) {
      printer.print("Tick")
    } else if(node.isPresentAbsent) {
      printer.print("~")
    } else if(node.isPresentExpression) {
      printer.print("EventMsg ")
    }
  }

  override fun visit(node: ASTStreamConstructorExpression) {
    printer.print("(<[")
  }

  override fun endVisit(node: ASTStreamConstructorExpression) {
    printer.print("]>)")
  }
}
