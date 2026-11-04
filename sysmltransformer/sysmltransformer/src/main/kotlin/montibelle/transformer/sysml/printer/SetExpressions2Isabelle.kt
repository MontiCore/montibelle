package montibelle.transformer.sysml.printer

import de.monticore.ocl.setexpressions._ast.ASTSetEnumeration
import de.monticore.ocl.setexpressions._visitor.SetExpressionsInheritanceHandler
import de.monticore.ocl.setexpressions._visitor.SetExpressionsVisitor2
import de.monticore.prettyprint.IndentPrinter

class SetExpressions2Isabelle(val printer: IndentPrinter)
  : SetExpressionsVisitor2, SetExpressionsInheritanceHandler()
{

  override fun visit(node: ASTSetEnumeration) {
    printer.print("{")
  }

  override fun traverse(node: ASTSetEnumeration) {
    var first = true
    for(element in node.setCollectionItemList) {
      if (!first) {
        printer.print(", ")
      }
      element.accept(getTraverser())
      first = false
    }
  }

  override fun endVisit(node: ASTSetEnumeration) {
    printer.print("}")
  }

}
