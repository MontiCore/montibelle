package montibelle.transformer.sysml.printer

import de.monticore.expressions.expressionsbasis._ast.ASTExpression
import de.monticore.ocl.oclexpressions._ast.ASTForallExpression
import de.monticore.ocl.oclexpressions._ast.ASTImpliesExpression
import de.monticore.ocl.oclexpressions._ast.ASTInDeclaration
import de.monticore.ocl.oclexpressions._ast.ASTInDeclarationVariable
import de.monticore.ocl.oclexpressions._ast.ASTOCLExpressionsNode
import de.monticore.ocl.oclexpressions._visitor.OCLExpressionsInheritanceHandler
import de.monticore.ocl.oclexpressions._visitor.OCLExpressionsVisitor2
import de.monticore.prettyprint.IndentPrinter

class OCLExpressions2Isabelle(private val printer: IndentPrinter)
  : OCLExpressionsVisitor2, OCLExpressionsInheritanceHandler()
{

  override fun visit(node: ASTInDeclarationVariable) {
    printer.print(node.name)
  }

  override fun traverse(node: ASTImpliesExpression) {
    node.left.accept(getTraverser())
    printer.print(" \\<longrightarrow> ")
    node.right.accept(getTraverser())
  }

  override fun traverse(node: ASTInDeclaration) {

    node.getInDeclarationVariable(0).accept(this.traverser)

    if (node.isPresentExpression) {
      printer.print(" \\<in> ")
      node.expression.accept(this.traverser)
    }
  }

  override fun traverse(node: ASTForallExpression) {
    node.inDeclarationList.get(0).accept(this.traverser)

    printer.print(".")

    if (node.expression != null) {
      node.expression.accept(this.traverser)
    }

    if (node.spannedScope != null) {
      node.spannedScope.accept(this.traverser)
    }
  }

  override fun visit(node: ASTForallExpression) {
    printer.print("\\<forall> ")
  }
}
