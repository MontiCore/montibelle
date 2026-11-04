package trafos

import de.monticore.expressions.expressionsbasis._ast.ASTExpression
import de.monticore.visitor.ITraverser

interface IExpressionPrinter {
  val traverser: ITraverser

  val printer: ResettableIndentPrinter

  fun print(expression: ASTExpression): String {
    printer.reset()

    expression.accept(traverser)

    return printer.content
  }
}
